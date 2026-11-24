From monae Require Import preamble hierarchy.
From mathcomp Require Import boot boolp.
From FreerDPS Require Import all_freerdps ping_common ping_client_serv_freespec.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope contract_scope.

(******************************************************************************)
(* The ping protocol split into two FreeSpec components.                     *)
(*                                                                            *)
(*   CLIENT == interface of the client: ASK emits a Ping, ANSWER reads the    *)
(*             reply                                                          *)
(*   SERVER == interface of the server: SERVE handles one incoming packet and *)
(*             says whether it replied                                        *)
(*   client == client component, CLIENT on top of client_api                  *)
(*   server == server component, SERVER on top of server_api                  *)
(*   ping_with cl sv == the protocol built from a client and a server       *)
(*   PhasedM == contracts on CLIENT and SERVER, and a round written against   *)
(*             those interfaces                                               *)
(*                                                                            *)
(* Both components share the network state and the invariant                 *)
(* chan_inv := serverQ != Some Pong /\ clientQ != Some Ping. The client       *)
(* requires clientQ != Some Ping (WAIT) and only sends Pings; the server      *)
(* requires serverQ != Some Pong (RECV) and only replies Pongs.               *)
(* Each component is checked alone against its own contract;                 *)
(* ping_with_correct then combines any two correct components without        *)
(* unfolding them.                                                            *)
(******************************************************************************)

Import NetworkChannelMod ccm scm.

(** * Interfaces *)

Inductive CLIENT : effect :=
| ASK : CLIENT unit
| ANSWER : CLIENT outcome.

Inductive SERVER : effect :=
| SERVE : SERVER (option unit).

(** * Reliable components *)

Section client.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.

Definition answer : M outcome := answer_of (fun=> wait) tt.

Definition client : component (M := M) CLIENT Fx :=
  fun _ cmd => match cmd with
  | ASK => send
  | ANSWER => answer
  end.

Lemma syn_client T (cmd : CLIENT T) :
  providesOnlyF (F := client_api) (client cmd).
Proof.
case: cmd; first exact: syn_send.
exists (frBind (frTrigger WAIT) (fun reply =>
  if reply is Some Pong then frRet GotPong else frRet LostPong)).
rewrite /= /answer /answer_of; congr (wait >>= _).
by apply: funext=> -[[]|].
Qed.

Lemma pre_client T (cmd : CLIENT T) ns :
  chan_inv ns -> pre (client_c |~ client cmd) ns.
Proof.
case: cmd=> [_ /=|[_ cQ_ok] /=]; first by rewrite send_respect.
rewrite /answer /answer_of freer_to_hoare_bindE; split.
  by rewrite wait_respect.
by move=> [[]|] *; rewrite pre_ret.
Qed.

Lemma post_client T (cmd : CLIENT T) ns t ns' :
  chan_inv ns -> post (client_c |~ client cmd) ns t ns' -> chan_inv ns'.
Proof.
case: ns=> sQ cQ; case: ns'=> sQ' cQ' [sQ_ok cQ_ok].
case: cmd t=> t /=.
  by move/send_run=> /= [-> ->]; split=> //; apply/eqP.
rewrite /answer /answer_of freer_to_hoare_bindE.
case=> reply [[s1 c1]] [/wait_run /= [-> ->]].
by case: reply=> [[]|]; rewrite post_ret=> -[_ [<- <-]]; split=> //; apply/eqP.
Qed.

Theorem client_correct :
  correct_component client (no_contract CLIENT) client_c (fun=> chan_inv).
Proof.
move=> sin ns inv T cmd _; split; first exact: pre_client.
by move=> t ns' run; split=> //; exact: post_client run.
Qed.

End client.

#[local] Hint Extern 0 (providesOnlyF answer) =>
  solve [exact: (syn_client ANSWER)] : core.

Section server.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.

Definition server : component (M := M) SERVER Fx :=
  fun _ cmd => match cmd with
  | SERVE => S_p
  end.

Lemma syn_server T (cmd : SERVER T) :
  providesOnlyF (F := server_api) (server cmd).
Proof. by case: cmd; exact: syn_s_p. Qed.

Lemma pre_server T (cmd : SERVER T) ns :
  chan_inv ns -> pre (server_c |~ server cmd) ns.
Proof. by case: cmd=> -[sQ_ok _]; rewrite s_p_respect. Qed.

Lemma post_server T (cmd : SERVER T) ns t ns' :
  chan_inv ns -> post (server_c |~ server cmd) ns t ns' -> chan_inv ns'.
Proof.
case: ns=> sQ cQ; case: ns'=> sQ' cQ' [sQ_ok cQ_ok].
case: cmd t=> t /s_p_run /=.
by case: t=> [[]|] [-> ->]; split=> //; apply/eqP.
Qed.

Theorem server_correct :
  correct_component server (no_contract SERVER) server_c (fun=> chan_inv).
Proof.
move=> sin ns inv T cmd _; split; first exact: pre_server.
by move=> t ns' run; split=> //; exact: post_server run.
Qed.

End server.

(** * Combining a client and a server *)

Section combination.
Context {Fx Fout : effect} `{Fout -<? Fx} {M : freerMonad Fx}.

Definition round_with (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) : M outcome :=
  round_of (cl _ ASK) (fun=> sv _ SERVE) (fun=> cl _ ANSWER).

(** Retrying a round that keeps [chan_inv] keeps [chan_inv]. *)
Lemma retry_ping_pong_ok (c : contract Fout net_state) (run : M outcome) :
    (forall ns, chan_inv ns ->
      pre (c |~ run) ns /\
      forall t ns', post (c |~ run) ns t ns' -> chan_inv ns') ->
  forall fuel ns, chan_inv ns ->
    pre (c |~ retry_ping_pong run fuel) ns /\
    forall t ns', post (c |~ retry_ping_pong run fuel) ns t ns' ->
      chan_inv ns'.
Proof.
move=> run_ok; elim=> [|fuel IH] ns inv /=; first exact: run_ok.
have [run_pre run_post] := run_ok ns inv.
rewrite freer_to_hoare_bindE; split.
  split=> // result ns1 /run_post inv1.
  by case: result; [rewrite pre_ret | exact: (IH ns1 inv1).1 ..].
move=> t ns' [result [ns1 [/run_post inv1]]].
by case: result; [rewrite post_ret=> -[_ <-] | exact: (IH ns1 inv1).2 ..].
Qed.

Definition ping_with (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) :
  component (M := M) ProtocolM.ping_round Fx :=
  fun _ cmd => match cmd with
  | ProtocolM.one_round => round_with cl sv
  | ProtocolM.retry_round fuel => retry_ping_pong (round_with cl sv) fuel
  end.

Section correct_component_views.
Context {Fin : effect} (compo : component (M := M) Fin Fx).
Context (c : contract Fout net_state).
Context (compo_ok : correct_component compo (no_contract Fin) c
  (fun=> chan_inv)).

Lemma correct_pre T (cmd : Fin T) ns :
  chan_inv ns -> pre (c |~ compo cmd) ns.
Proof. by move=> inv; case: (@compo_ok tt ns inv T cmd I). Qed.

Lemma correct_post T (cmd : Fin T) ns t ns' :
  chan_inv ns -> post (c |~ compo cmd) ns t ns' -> chan_inv ns'.
Proof.
by move=> inv run; case: (@compo_ok tt ns inv T cmd I)=> _ /(_ t ns' run) [].
Qed.

End correct_component_views.

(** The protocol is correct as soon as both components are: only their
    [correct_component] statements are used. *)
Theorem ping_with_correct (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) (c : contract Fout net_state) :
  correct_component cl (no_contract CLIENT) c (fun=> chan_inv) ->
  correct_component sv (no_contract SERVER) c (fun=> chan_inv) ->
  correct_component (ping_with cl sv) (no_contract ProtocolM.ping_round) c
    (fun=> chan_inv).
Proof.
move=> cl_ok sv_ok.
have round_ok ns : chan_inv ns ->
    pre (c |~ round_with cl sv) ns /\
    forall t ns', post (c |~ round_with cl sv) ns t ns' -> chan_inv ns'.
  move=> inv; rewrite /round_with /round_of bindA; split.
    rewrite freer_to_hoare_bindE; split.
      exact: (correct_pre cl_ok ASK inv).
    move=> _ ns1 /(correct_post cl_ok inv) inv1.
    rewrite freer_to_hoare_bindE; split.
      exact: (correct_pre sv_ok SERVE inv1).
    move=> served ns2 /(correct_post sv_ok inv1) inv2.
    case: served=> [[]|]; last by rewrite pre_ret.
    exact: (correct_pre cl_ok ANSWER inv2).
  move=> result ns'; rewrite freer_to_hoare_bindE.
  case=> _ [ns1] [/(correct_post cl_ok inv) inv1].
  rewrite freer_to_hoare_bindE.
  case=> served [ns2] [/(correct_post sv_ok inv1) inv2].
  case: served=> [[]|]; last by rewrite post_ret=> -[_ <-].
  exact: (correct_post cl_ok inv2).
move=> sin ns inv _ [|fuel] _ /=.
  have [round_pre round_post] := round_ok ns inv.
  by split=> // t ns' /round_post.
have [retry_pre retry_post] := retry_ping_pong_ok round_ok fuel inv.
by split=> // t ns' /retry_post.
Qed.

End combination.

(** * The reliable protocol *)

Section reliable_protocol.
Context {ProtoF : effect} `{client_api ;; server_api -<< ProtoF}.
Context {M : freerMonad ProtoF}.

(** Each component, checked against its own contract, is also correct for
    the shared contract of the protocol. *)
Lemma client_shared_correct :
  correct_component (client (M := M)) (no_contract CLIENT)
    ProtocolM.ping_contract (fun=> chan_inv).
Proof.
move=> sin ns inv T cmd req.
rewrite /ProtocolM.ping_contract freer_contract_left; first exact: syn_client.
exact: client_correct.
Qed.

Lemma server_shared_correct :
  correct_component (server (M := M)) (no_contract SERVER)
    ProtocolM.ping_contract (fun=> chan_inv).
Proof.
move=> sin ns inv T cmd req.
rewrite /ProtocolM.ping_contract freer_contract_right; first exact: syn_server.
exact: server_correct.
Qed.

(** The composition is the monolithic protocol of ProtocolM. *)
Lemma ping_with_client_server :
  ping_with (client (M := M)) server = ProtocolM.ping_protocol.
Proof. by []. Qed.

Theorem reliable_ping_correct :
  correct_component (ping_with (client (M := M)) server)
    (no_contract ProtocolM.ping_round) ProtocolM.ping_contract
    (fun=> chan_inv).
Proof.
apply: ping_with_correct.
  exact: client_shared_correct.
exact: server_shared_correct.
Qed.

End reliable_protocol.

(** * Phased interface contracts *)

(** Contracts on CLIENT and SERVER, and a round written against those
    interfaces. *)
Module PhasedM.

Inductive phase := Idle | Waiting.
HB.instance Definition _ := gen_eqMixin phase.
HB.instance Definition _ := gen_choiceMixin phase.

(** ** Client contract: ASK when idle, ANSWER when waiting *)

Definition client_step (ph : phase) : forall X, CLIENT X -> X -> phase :=
  fun _ cmd _ => match cmd with
  | ASK => Waiting
  | ANSWER => Idle
  end.

Definition client_req (ph : phase) : forall X, CLIENT X -> Prop :=
  fun _ cmd => match cmd with
  | ASK => ph = Idle
  | ANSWER => ph = Waiting
  end.

Definition client_promise (ph : phase) : forall X, CLIENT X -> X -> Prop :=
  fun X cmd => match cmd in CLIENT X return X -> Prop with
  | ASK => fun _ => True
  | ANSWER => fun result => result <> LostPing
  end.

Definition client_phase_c : contract CLIENT phase :=
  make_contract client_step client_req client_promise.

(** An idle client has no reply pending. *)
Definition phase_net (ph : phase) (ns : net_state) :=
  chan_inv ns /\ (ph = Idle -> clientQ ns = None).


Section phased_client.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.

Theorem phased_client_correct :
  correct_component (client (M := M)) client_phase_c client_c phase_net.
Proof.
move=> ph ns [inv idle] T cmd req.
split; first exact: (pre_client cmd inv).
move=> t ns' run; have inv' := post_client inv run.
case: cmd t req run=> t req run /=.
  by split.
move: run; rewrite /= /answer /answer_of freer_to_hoare_bindE.
case=> reply [ns1] [/wait_run [cQ1 sQ1]].
case: reply=> [[]|]; rewrite post_ret=> -[<- <-].
all: split=> //; rewrite /phase_net.
all: move: inv=>[c0 s0]; split; rewrite /chan_inv // cQ1 sQ1; split=>//.
all: exact/eqP.
Qed.

End phased_client.

(** ** Server contract: SERVE only says whether it replied *)

Definition server_phase_c : contract SERVER unit :=
  make_contract const_witness no_requirement no_promise.

Section phased_server.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.

Theorem phased_server_correct :
  correct_component (server (M := M)) server_phase_c server_c
    (fun=> chan_inv).
Proof.
move=> u ns inv T cmd _; split; first exact: (pre_server cmd inv).
by move=> t ns' run; split=> //; exact: post_server inv run.
Qed.

End phased_server.

(** ** A round written against the two interfaces *)

Section round.
Context {Fx : effect} `{CLIENT ;; SERVER -<< Fx} {M : freerMonad Fx}.

Definition round : M outcome :=
  ptrigger ASK >> ptrigger SERVE >>= fun served =>
    if served is Some _ then ptrigger ANSWER else Ret LostPing.

Definition round_c : contract Fx (phase * unit)%type :=
  client_phase_c -*- server_phase_c.

Lemma pre_round_client T (cmd : CLIENT T) s :
  pre (round_c |~ (ptrigger cmd : M T)) s <->
  requirement client_phase_c s.1 cmd.
Proof.
rewrite to_hoare_triggerE /hoare_of_contract /= /gen_requirement /=.
rewrite /gen_requirement /= injK_Some injK_None.
by split=> [[]|].
Qed.

Lemma post_round_client T (cmd : CLIENT T) s t s' :
  post (round_c |~ (ptrigger cmd : M T)) s t s' <->
  s' = (client_step s.1 cmd t, s.2) /\ promise client_phase_c s.1 cmd t.
Proof.
rewrite to_hoare_triggerE /hoare_of_contract /= /gen_state_update.
rewrite /gen_promise /= /gen_state_update /gen_promise /=.
rewrite injK_Some injK_None.
by split=> [[-> []]|[-> ?]].
Qed.

Lemma pre_round_server T (cmd : SERVER T) s :
  pre (round_c |~ (ptrigger cmd : M T)) s.
Proof.
rewrite to_hoare_triggerE /hoare_of_contract /= /gen_requirement /=.
rewrite /gen_requirement /=.
by rewrite injK_Some injK_None.
Qed.

Lemma post_round_server T (cmd : SERVER T) s t s' :
  post (round_c |~ (ptrigger cmd : M T)) s t s' <->
  s' = s /\ promise server_phase_c s.2 cmd t.
Proof.
rewrite to_hoare_triggerE /hoare_of_contract /= /gen_state_update.
rewrite /gen_promise /= /gen_state_update /gen_promise /=.
rewrite injK_Some injK_None.
case: s=> ph [].
by split=> [[-> []]|[-> ?]].
Qed.

Lemma pre_round : pre (round_c |~ round) (Idle, tt).
Proof.
rewrite /round bindA freer_to_hoare_bindE; split.
  by rewrite pre_round_client.
move=> _ s1 /post_round_client [-> _] /=.
rewrite freer_to_hoare_bindE; split; first exact: pre_round_server.
move=> [[]|] s2 /post_round_server [-> _]; last by rewrite pre_ret.
by rewrite pre_round_client.
Qed.

(** A lost Ping ends the round with the client still waiting. *)
Lemma post_round result s' :
  post (round_c |~ round) (Idle, tt) result s' ->
  (s' = (Idle, tt) /\ result <> LostPing) \/
  (s' = (Waiting, tt) /\ result = LostPing).
Proof.
rewrite /round bindA freer_to_hoare_bindE.
case=> _ [s1] [/post_round_client [-> _]] /=.
rewrite freer_to_hoare_bindE.
case=> served [s2] [/post_round_server [-> _]].
case: served=> [[]|]; last by rewrite post_ret=> -[<- <-]; right.
by move/post_round_client=> [-> ?]; left.
Qed.

(** Hence two rounds in a row break the client contract: ASK is called
    again while the client is waiting. *)
Lemma two_rounds_unsafe : ~ pre (round_c |~ (round >> round)) (Idle, tt).
Proof.
rewrite freer_to_hoare_bindE=> -[_ /(_ LostPing (Waiting, tt))].
have run : post (round_c |~ round) (Idle, tt) LostPing (Waiting, tt).
  rewrite /round bindA freer_to_hoare_bindE.
  exists tt, (Waiting, tt); split; first by rewrite post_round_client.
  rewrite freer_to_hoare_bindE.
  exists None, (Waiting, tt); split; last by rewrite post_ret.
  by rewrite post_round_server.
move=> /(_ run); rewrite /round bindA freer_to_hoare_bindE.
by case=> /pre_round_client.
Qed.

End round.
End PhasedM.
