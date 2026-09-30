From mathcomp Require Import boot order algebra interval_inference.
From mathcomp Require Import classical_sets boolp reals Rstruct.
 (* convex. *)
From infotheo Require Import  convex fsdist realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import all_freerdps ping_common ping_client_serv.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope fsdist_scope.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope contract_scope.
Local Open Scope convex_scope.


(******************************************************************************)
(*                                                                            *)
(* Ok, in this file, what I am trying is to provide the probability as a part *)
(* of the client / server contract and to refine transmit over those effects. *)
(*                                                                            *)
(* To make it a bit more understandable, we currently have 2 working freer    *)
(* implementations :                                                          *)
(* - A freer model using probabilities                      (1) ;             *)
(* - A model using FreeSpec like interfaces/hoare reasoning (2).              *)
(*                                                                            *)
(* The goal here would be to use both at once, thus be able to model and make *)
(* the proofs of (1) using the implem / model of (2), which would further     *)
(* strengthen the confidence we have in our model.                            *)
(*                                                                            *)
(* Current experiment :                                                       *)
(* > Make a new provided effect based on client/serv + FlipEff and write      *)
(*   transmit from this effect. If this work correctly, we should be able to  *)
(*   reuse the ping_common.v file without any issue and this should be a good *)
(*   direction to write new systems with a probabilistic direction.           *)
(*                                                                            *)
(* The last experiments that were done :                                      *)
(* - Linking the probability to the channel directly                          *)
(*   +-> This makes sense because the client should not know when sending or  *)
(*   |   receiving that the message has been dropped. The actual mechanism    *)
(*   |   should be built through another mechansim                            *)
(*   +-> This works on a component and we currently have no way of linking    *)
(*   |   two components together.                                             *)
(*   +-> This could be an interesting research track though.                  *)
(*                                                                            *)
(* *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ** *)
(*                                                                            *)
(* Inner feeling :                                                            *)
(* - I think that there are two things (or maybe more) to take in account for *)
(*   probabilities :                                                          *)
(*   + the client should not make the prob choice of sending the message      *)
(*     unless it comes from a client's failure or malfunction or anything;    *)
(*   + the ns should handle the packet drops, but here that's probably        *)
(*     not a freer monad as the ns we use is a state... or maybe we can       *)
(*     find a way to cheat our way out ? <== I think that's what happened...  *)
(*   + Probabilities modeled by byzantine adversaries might fall in a 3rd     *)
(*     category... Or a mix of multiple...                                    *)
(*                                                                            *)
(******************************************************************************)


Import NetworkChannelMod.

Local Abbreviation R := Rdefinitions.R.


Section flip_contract.

Lemma fdist1_serverQ (p: {prob R}) nQ n1 n2 :
fsdist1 nQ = fsdist1 n1 <|p|> fsdist1 n2 ->
fsdist1 (serverQ nQ) = fsdist1 (serverQ n1) <|p|> fsdist1 (serverQ n2).
Proof.
move/(congr1 (fsdistmap serverQ)).
by rewrite fsdistmap_affine !fsdistmap1.
Qed.

Lemma fdist1_clientQ (p: {prob R}) nQ n1 n2 :
fsdist1 nQ = fsdist1 n1 <|p|> fsdist1 n2 ->
fsdist1 (clientQ nQ) = fsdist1 (clientQ n1) <|p|> fsdist1 (clientQ n2).
Proof.
move/(congr1 (fsdistmap clientQ)).
by rewrite fsdistmap_affine !fsdistmap1.
Qed.

Definition server_keep_or_drop (p: {prob R}) (ns : net_state) :
  R.-dist net_state :=
match ns with
| mk_chan _ cQ => (fsdist1 ns) <| p |> (fsdist1 (mk_chan None cQ))
end.

Definition client_keep_or_drop (p: {prob R}) (ns : net_state) :
  R.-dist net_state :=
match ns with
| mk_chan sQ _ => (fsdist1 ns) <| p |> (fsdist1 (mk_chan sQ None))
end.

Definition keep_or_drop p ns (is_server: bool) :=
if is_server then server_keep_or_drop p ns
else client_keep_or_drop p ns.

Definition flip_step (is_server : bool) (ns : net_state) :
  forall X, @FlipEff R X -> X -> R.-dist net_state
:= fun T op _ => match op with
| flipe p => keep_or_drop p ns is_server
end.
  (* avec prob p :
  dist p {
  - keep => Ret ns
  - drop => drop_new_packet ns is_server
  } *)

Definition select_queue (is_server : bool) ns : packet :=
  if is_server then serverQ ns else clientQ ns.

Definition expected_packet (is_server : bool) : packet :=
  if is_server then Some Ping else Some Pong.

Definition flip_requirement (is_server : bool) ns :
    forall X, @FlipEff R X -> Prop :=
  fun _ _ => select_queue is_server ns = expected_packet is_server.

(* On promise check, we have two things : *)
(* - The queue that received a change must be either same size or -1 *)
(* - The other queue must be the same as before *)
Inductive flip_promise (is_server : bool) (ns : net_state) :
    forall X, @FlipEff R X -> X -> Prop :=
  | KEEP_IT : select_queue is_server ns = expected_packet is_server
    -> flip_promise is_server ns (flipe 1%:i01) true
  | DROP_IT :
    select_queue is_server ns = None
    -> (forall fns, select_queue (~~is_server) fns = select_queue (~~is_server) ns)
    -> flip_promise is_server ns (flipe 0%:i01) false.
  (* /\ exists o, o = select_queue (~~is_server) ns  *)

Definition flip_contract (is_server : bool) :
    contract R (@FlipEff R) net_state :=
  make_contract (flip_step is_server)
    (flip_requirement is_server) (flip_promise is_server).

End flip_contract.
Section syntax.
Context {Fx : effect} `{@FlipEff R -< Fx}.
Context {M : freerMonad Fx}.

Print H.

Lemma syn_flip (p : {prob R}) : providesOnlyF (F:=@FlipEff R) (M := M) (flip p).
Proof. by exists (frTrigger (inj (flipe p))). Qed.

End syntax.

#[export] Hint Extern 0 (providesOnlyF (F:=FlipEff) (flip _)) =>
  solve [exact: syn_flip] : core.

Module Export ProbPingPongM.
Section client_program.
Context {Fx : effect}.
Context `{@FlipEff R ;; client_api -<< Fx} {M : freerMonad Fx}.

Definition transmit (p : {prob R}) (program : M unit) : M unit :=
  program >> (flip p >> Ret tt).
(* send <|| p ||> Ret tt. *)
(* TODO: Change to this ^^^ *)
Variable (p : {prob R}).

Definition psend : M unit := transmit p send.
Check psend.
Definition C : M (option msg) := psend >> wait.
End client_program.

Section server_program.
Context {Fx : effect}.
Context `{@FlipEff R ;; server_api -<< Fx} {M : freerMonad Fx}.

Variable (p : {prob R}).

Definition preply : M bool := reply >> flip p.
Definition pserver : M (option msg) :=
  recv >>= fun inc=> if inc is Some Ping then preply >> Ret inc else Ret inc.
Arguments pserver : simpl never.
End server_program.
End ProbPingPongM.

Import ccm scm.
From Stdlib Require Import Eqdep.
(** ** Packet Delivery Specification *)

Section flip_respectful_and_run_lemmas.
Context {Fx : effect} `{@FlipEff R -< Fx}.
Context {M : freerMonad Fx}.
Implicit Types (p : {prob R}).

Fact flip_respect is_server p (net : net_state)
    (queued : select_queue is_server net = expected_packet is_server):
  pre (flip_contract is_server |~ (flip p : M _)) net.
Proof.
by rewrite to_hoare_triggerE /= provided_callerP /= /flip_requirement.
Qed.

(* TODO: This lemma needs to be updated to fit the new style *)
Fact flip_run is_server p (ins fns : net_state) keep
    (run : post (flip_contract is_server |~ (flip p : M _))
      ins keep fns) :
  fsdist1 fns = keep_or_drop p ins is_server /\
  flip_promise is_server ins (flipe p) keep.
  (* fsdist1 fns = keep_or_drop p ins is_server. *)
  (* keep_or_drop p fns is_server = keep_or_drop p ins is_server. *)
Proof.
by move/post_to_hoare_triggerP: run.
(* move: run. *)
(* rewrite /server_keep_or_drop /=. Search (fsdist_conv). Print fsdist_conv. *)
(* rewrite to_hoare_triggerE /= provided_calleeP=> -[] /= Hupdate Hpromise.

inversion Hpromise as [Hcorrect Hbb Hp Hex | Hincorrect Hcoh Hbb Hp Hex ];
  apply inj_pair2 in Hex; subst;
  clear Hpromise.
- move: fns Hupdate=> -[sf cf] Hupdate.
  move: ins Hupdate Hcorrect=> -[si ci].
  by rewrite /select_queue /= /server_keep_or_drop=> <-.
  (* rewrite /keep_or_drop /server_keep_or_drop /client_keep_or_drop. *)
  (* by rewrite !conv1; case: is_server. *)
- move: Hupdate Hcoh=> _ /(_ fns).
  move: fns=> -[sf cf].
  move: ins Hincorrect=> -[si ci].
  rewrite /select_queue /= /server_keep_or_drop.
  rewrite /keep_or_drop /server_keep_or_drop /client_keep_or_drop.
  by rewrite !conv0; case: is_server=>/= <- ->. *)
Qed.
End flip_respectful_and_run_lemmas.

(** ** Client Specification *)

Module pccm.
Section client_respectful_and_run_lemmas.
Context {Fx ClientF : effect}.
Context `{@FlipEff R ;; client_api -<< Fx} `{ClientF -< Fx} {M : freerMonad Fx}.

Implicit Types (p : {prob R}).

(* Hc2 : *)
(* fsdist1 {| serverQ := s2; clientQ := c2 |} = *)
(* fsdist1 {| serverQ := None; clientQ := Some Pong |} <|p|>  *)
(* fsdist1 {| serverQ := None; clientQ := None |} *)

Fact pwait_respect p (net : net_state) :
    (fsdist1 (clientQ net) =
      fsdist1 (Some Pong : packet) <| p |> fsdist1 (None : packet)) ->
  pre (flip_contract true -^- client_c  |~ (wait : M packet)) net.
Proof.
move=>coh.
rewrite freer_contract_right //.
apply: ccm.wait_respect.
have := congr1 (fsdistmap (fun ns : packet => ns != Some Ping)) coh.
rewrite /= fsdistmap_affine !fsdistmap1 /=.
have -> : (Some Pong: packet) != Some Ping by apply/eqP.
have -> : ((None : packet) != (Some Ping: packet)) by apply/eqP.
by rewrite convmm=> /fsdist1_inj ->.
Qed.

Fact pwait_run (ins fns : net_state) om (run : post (flip_contract true -^- client_c |~ (wait : M _)) ins om fns ) :
  fns.(clientQ) = None /\ fns.(serverQ) = ins.(serverQ).
Proof.
move: run.
rewrite freer_contract_right //.
by move/ccm.wait_run.
Qed.


Fact psend_respect p (net : net_state) :
  pre (flip_contract true -^- client_c |~ (psend p : M _)) net.
Proof.
rewrite !freer_to_hoare_bindE freer_contract_right //.
split; first exact: send_respect.
move=> [] [sQ cQ] /send_run /= [-> ->].
rewrite freer_contract_left //.
split.
- exact: flip_respect.
- by move=> *; rewrite pre_ret.
Qed.

Fact psend_run p (ins fns : net_state) (u : unit)
    (run : post (flip_contract true -^- client_c |~ (psend p : M _))
      ins u fns) :
fsdist1 fns = server_keep_or_drop p (fill_serverQ Ping ins).
Proof.
move: run.
rewrite !freer_to_hoare_bindE freer_contract_right //.
case=> [[]] [[sQ cQ]] [] /send_run /= [-> ->].
rewrite freer_contract_left //.
case=> [keep] [net] [] /flip_run /= [] <- _.
by rewrite post_ret=> -[? <-] /=.
Qed.

Lemma pre_c (p : {prob R}) (net : net_state)
    (coh : fsdist1 (clientQ net) =
      fsdist1 (Some Pong : packet) <| p |> fsdist1 (None : packet)) :
  pre (flip_contract true -^- client_c |~ (C p : M _)) net.
Proof.
rewrite /C freer_to_hoare_bindE; split.
  exact: psend_respect.
move=> [] [sQ cQ] /psend_run /fdist1_clientQ.
rewrite /= convmm=> /fsdist1_inj same_client.
apply/(pwait_respect (p:=p)).
by rewrite /= same_client.
Qed.

Lemma post_c p (ins fns : net_state) (result : packet)
    (run : post (flip_contract true -^- client_c |~ (C p : M _))
      ins result fns) :
fsdist1 fns = server_keep_or_drop p  (mk_chan (Some Ping) None).
Proof.
move: run.
rewrite freer_to_hoare_bindE.
case=> [[]] [[sQ cQ]] [].
move/psend_run=>Hrun.
rewrite freer_contract_right //.
move: fns=> [sQ' cQ'] /wait_run=> -[/= -> ->].
move: (congr1 (fsdistmap (fun ns => mk_chan (serverQ ns) None)) Hrun).
by rewrite /server_keep_or_drop /= fsdistmap_affine !fsdistmap1.
Qed.
End client_respectful_and_run_lemmas.
End pccm.


Module pscm.
Section server_respectful_and_run_lemmas.
Context {Fx : effect}.
Context `{@FlipEff R ;; server_api -<< Fx} {M : freerMonad Fx}.

Implicit Types (p : {prob R}).

Fact precv_respect (p : {prob R}) (net : net_state)
    (coh : fsdist1 (serverQ net) =
      fsdist1 (Some Ping : packet) <| p |> fsdist1 (None : packet)) :
  pre (server_c |~ (recv : M _)) net.
Proof.
apply: scm.recv_respect.

have := congr1 (fsdistmap (fun ns : packet => ns != Some Pong)) coh.
rewrite /= fsdistmap_affine !fsdistmap1 /=.
have -> : (Some Ping: packet) != Some Pong by apply/eqP.
have -> : ((None : packet) != (Some Pong: packet)) by apply/eqP.
by rewrite convmm=> /fsdist1_inj ->.
Qed.

Fact preply_respect p (net : net_state) :
  pre (flip_contract false -^- server_c |~ (preply p : M _)) net.
Proof.
rewrite freer_to_hoare_bindE freer_contract_right //.
split; first exact: reply_respect.
move=> [] [sQ cQ] /reply_run /= [-> ->].
rewrite freer_contract_left //.
exact: flip_respect.
Qed.

Fact preply_run p (ins fns : net_state) keep
    (run : post (flip_contract false -^- server_c |~ (preply p : M _))
      ins keep fns) :
  fsdist1 fns = client_keep_or_drop p (fill_clientQ Pong ins).
Proof.
move: run; rewrite freer_to_hoare_bindE freer_contract_right //.
case=> [[]] [[sQ cQ]] [] /reply_run /= [-> ->].
rewrite freer_contract_left //.
by move/flip_run=> [-> _].
Qed.

Lemma s_p_respect (p : {prob R}) (net : net_state)
    (coh : fsdist1 (serverQ net) =
      fsdist1 (Some Ping : packet) <| p |> fsdist1 (None : packet)) :
  pre (flip_contract false -^- server_c |~ (pserver p : M _)) net.
Proof.
rewrite freer_to_hoare_bindE freer_contract_right //.
split; first by exact/(precv_respect (p:=p))/coh.
move=> [[]|] [sQ cQ] /recv_run /= [-> ->].
- rewrite freer_to_hoare_bindE; split.
  + exact: preply_respect.
  + move=> *.
all: by rewrite pre_ret.
Qed.

Lemma s_p_run p (ins fns : net_state) (result : packet)
    (run : post (flip_contract false -^- server_c |~ (pserver p : M _))
      ins result fns) :
  fsdist1 fns =
    if result is Some Ping then
      client_keep_or_drop p (mk_chan None (Some Pong))
    else fsdist1 (mk_chan None (clientQ ins)).
Proof.
move: run.
rewrite freer_to_hoare_bindE freer_contract_right //.
case=> [[[]|]] [[sQ cQ]] [] /recv_run /= [-> ->].
- rewrite freer_to_hoare_bindE.
  case=> [keep] [net] [] /preply_run=> /= replied.
all: rewrite post_ret.
all: case.
all: move=><-.
all: by move=><-.
Qed.
End server_respectful_and_run_lemmas.
End pscm.

Import pccm pscm.

Section prob_ping_contract.
Context {ClientF ServerF ProtoF : effect}.
Context `{@FlipEff R ;; client_api -<< ClientF}.
Context `{@FlipEff R ;; server_api -<< ServerF}.
Context `{ClientF ;; ServerF -<< ProtoF}.

Definition sharedP : contract R ProtoF net_state :=
  (flip_contract true -^- client_c) -^-
  (flip_contract false -^- server_c).
End prob_ping_contract.

Module Import ProbProtocolSyntax.
Section syntax.
Context {ClientF ServerF ProtoF : effect}.
Context `{@FlipEff R ;; client_api -<< ClientF}.
Context `{@FlipEff R ;; server_api -<< ServerF}.
Context `{ClientF ;; ServerF -<< ProtoF} {M : freerMonad ProtoF}.

Lemma syn_psend (p : {prob R}) :
  providesOnlyF (F:=ClientF) (M := M) (psend p).
Proof.
by exists (frBind (frTrigger (inj (SEND Ping)))
  (fun=> frBind (frTrigger (inj (flipe p))) (fun=> frRet tt))).
Qed.

Lemma syn_s_p (p : {prob R}) :
  providesOnlyF (F:= ServerF) (M := M) (pserver p).
Proof.
exists (frBind (frTrigger (inj RECV)) (fun inc=>
  if inc is Some Ping then
    frBind (frBind (frTrigger (inj (RPLY Pong)))
      (fun=> frTrigger (inj (flipe p)))) (fun=> frRet inc)
  else frRet inc)).
rewrite /= /pserver /preply.
congr (recv >>= _).
by apply: boolp.funext=> -[[]|].
Qed.

End syntax.

#[export] Hint Extern 0 (providesOnlyF (psend _)) =>
  solve [exact: syn_psend] : core.
#[export] Hint Extern 0 (providesOnlyF (pserver _)) =>
  solve [exact: syn_s_p] : core.
End ProbProtocolSyntax.

(** * Protocol Description *)

Module ProbProtocolM.
Section protocol.
Context {ClientF ServerF ProtoF : effect}.
Context `{@FlipEff R ;; client_api -<< ClientF}.
Context `{@FlipEff R ;; server_api -<< ServerF}.
Context `{ClientF ;; ServerF -<< ProtoF} {M : freerMonad ProtoF}.

Variable (p : {prob R}).

(* TODO put in common *)
Inductive ping_round : effect := one_round : ping_round outcome.

Definition prob_ping_protocol : component (M := M) ping_round ProtoF :=
  fun _ cmd=>
    match cmd with
    | one_round =>
        psend p >> (pserver p >>= fun om=>
          match om with
          | Some Ping => wait >>= fun om=>
            if om is Some Pong then Ret GotPong else Ret LostPong
          | _ => Ret LostPing
          end)
    end.

Definition prob_ping_contract : contract R ProtoF net_state :=
  sharedP (ClientF := ClientF) (ServerF := ServerF).

(* TODO put in common *)
Definition protocol_inv (net : net_state) := (serverQ net = None) /\ (clientQ net = None).

Lemma pre_prob_ping (net : net_state) :
  protocol_inv net ->
  pre (prob_ping_contract |~ prob_ping_protocol one_round) net.
Proof.
move=> [s0 c0].
rewrite freer_to_hoare_bindE freer_contract_left // freer_contract_prodT.
split; first by exact: psend_respect.
move=> [] [s1 c1] /psend_run.
rewrite /fill_serverQ.
move=>/= /fdist1_serverQ /= Hs1.
(* rewrite c0=> /= Hs1. *)
rewrite freer_to_hoare_bindE freer_contract_right // freer_contract_prodT.
split; first by exact/s_p_respect.
move=> opm [s2 c2] /s_p_run /=.
case: opm=> [[]|] Hc2 /=.
move/fdist1_clientQ: Hc2=>/= Hc2.
rewrite freer_to_hoare_bindE freer_contract_left // freer_contract_prodT.
split; first by exact: (pwait_respect (p:=p)).
rewrite freer_contract_right //.
move=> opm [s3 c3] /wait_run /= [-> ->].
case: opm=> [[]|] /=.
all: by rewrite pre_ret.
Qed.

Lemma post_prob_ping (ins fns : net_state) (result : outcome) :
  protocol_inv ins ->
  post (prob_ping_contract |~ prob_ping_protocol one_round) ins result fns ->
  protocol_inv fns.
Proof.
move=> [s0 c0].
rewrite freer_to_hoare_bindE freer_contract_left // freer_contract_prodT.
case=> [[]] [[s1 c1]] [] /psend_run.
rewrite /server_keep_or_drop.
move/fdist1_clientQ=>/=; rewrite convmm c0 =>/fsdist1_inj=>->.
rewrite freer_to_hoare_bindE freer_contract_right // freer_contract_prodT.
case=> [opm] [[s2 c2]] [] /s_p_run /=.
case: opm=> [[]|]=> Hc2/=.
rewrite freer_to_hoare_bindE freer_contract_left //.
rewrite freer_contract_prodT freer_contract_right //.
case=>[opm] [[s3 c3]] [] /wait_run /= [-> ->].
case: opm=> [[]|] /=.
all: rewrite post_ret.
all: case.
all: move=>/= ?.
all: move=><-.
all: move: Hc2.
all: try (move/fdist1_serverQ=>/=; rewrite convmm); move/fsdist1_inj=>//.
all: by move=>->.
Qed.

Theorem prob_ping_protocol_correct :
  correct_component prob_ping_protocol (no_contract R ping_round) prob_ping_contract
    (fun=> protocol_inv).
Proof.
move=> [] net inv ? [] []; split=> [|result net' run] /=.
  exact: pre_prob_ping.
by split=> //; exact: post_prob_ping inv run.
Qed.
End protocol.
End ProbProtocolM.
