
From mathcomp Require Import all_ssreflect all_algebra interval_inference.
From mathcomp Require Import classical_sets boolp reals Rstruct.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order.
From mathcomp Require Import all_analysis.
From infotheo Require Import convex fsdist realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import all_freerdps ping_common ping_components.

Local Open Scope proba_scope.
Local Open Scope convex_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope monae_scope.
Import ChoiceRelation Order.LTheory.

Section about_freer_flip_monad.
Context {R : realType} {Fx: effect}
  `{@FlipEff R -< Fx} {M : choiceEqFreerMonad Fx R _}.

Fact freer_flip_choice (p : {prob R}) :
  (Ret true <|| p ||> Ret false : M _) ≈ (flip p).
Proof.
rewrite /freer_choice -[X in _ ≈ X]bindmret.
by apply: bindfwB=> -[].
Qed.

Fact flip_or_true (p q : {prob R}) :
  (Ret true <|| p ||> flip q  : M _) ≈ (flip [s_of p, q]).
Proof.
    by rewrite -2!freer_flip_choice freer_choiceA freer_choicemm.
Qed.
End about_freer_flip_monad.

Import NetworkChannelMod.

Local Abbreviation R := Rdefinitions.R.

(** The packet just sent to the server ([is_server]) or to the client is
    dropped, unless it is [kept]. *)
Definition drop_new_packet (ns : net_state) (kept is_server : bool) :
    net_state :=
  if kept then ns
  else if is_server then consume_serverQ ns else consume_clientQ ns.

Section flip_contract.

Definition flip_step is_server ns :
    forall X, @FlipEff R X -> X -> net_state :=
  fun T op => match op in (@FlipEff _ T) return T -> net_state with
  | flipe _ => fun kept => drop_new_packet ns kept is_server
  end.

Definition select_queue (is_server : bool) ns : packet :=
  if is_server then serverQ ns else clientQ ns.

Definition expected_packet (is_server : bool) : packet :=
  if is_server then Some Ping else Some Pong.

Definition flip_requirement is_server ns :
    forall X, @FlipEff R X -> Prop :=
  fun _ _ => select_queue is_server ns = expected_packet is_server.

(* On promise check, we have two things : *)
(* - The queue that received a change must be either same size or -1 *)
(* - The other queue must be the same as before *)
Inductive flip_promise is_server (net : net_state):
    forall X, @FlipEff R X -> X -> Prop :=
| KEEP_IT (p : {prob R}) :
  (p%:num > 0) ->
  select_queue is_server net = expected_packet is_server
    -> flip_promise is_server net bool (flipe p) true
| DROP_IT (p : {prob R}) :
  p%:num > 0 ->
  select_queue is_server net = None
  -> (exists ns, select_queue (~~is_server) ns = select_queue (~~is_server) net)
  -> flip_promise is_server net bool (flipe ((p%:num.~)%:i01)) false.
  (* /\ exists o, o = select_queue (~~is_server) ns  *)

Definition flip_contract (is_server : bool) :
(* (is_server : bool) : *)
    contract (@FlipEff R) net_state :=
  make_contract
    (flip_step is_server)
    (flip_requirement is_server)
    (flip_promise is_server).

End flip_contract.
Section syntax.
Context {Fx : effect} `{@FlipEff R -< Fx} {M : freerMonad Fx}.
Lemma syn_flip (p : {prob R}) : providesOnlyF (F:=@FlipEff R) (M := M) (flip p).
Proof. by exists (frTrigger (inj (flipe p))). Qed.
End syntax.

Import ccm scm.

Module ProbProtocolM.
Section transmission.
Context {Fx : effect} `{@FlipEff R -< Fx} {M : freerMonad Fx}.
(* Success with p; failure with 1 - p. *)
Definition transmit {A} (p : {prob R}) (a : A) : M (option A) :=
  Ret (Some a) <|| p ||> Ret None.

Lemma syn_transmit {A} (p : {prob R}) (a : A) :
  providesOnlyF (F := @FlipEff R) (transmit p a).
Proof.
exists (frBind (frTrigger (flipe p))
  (fun sent => frRet (if sent then Some a else None))).
rewrite /= /transmit /freer_choice.
congr (_ >>= _).
by apply: boolp.funext=> -[].
Qed.

Ltac ssubst :=
  lazymatch goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ]
  => apply Eqdep.EqdepTheory.inj_pair2 in H; ssubst
| [ |- _] => subst
  end.

Lemma pre_transmit1 {A} is_server (a : A) (net : net_state)
    (queued : select_queue is_server net = expected_packet is_server) :
  pre (flip_contract is_server |~ transmit 1%:i01 a) net.
Proof.
rewrite freer_to_hoare_bindE.
split; last by case; rewrite pre_ret.
exact/pre_to_hoare_triggerP.
Qed.

Lemma post_transmit1 {A} is_server {a : A} {ins fns : net_state}
    {result : option A}
    (queued : select_queue is_server ins = expected_packet is_server)
    (run : post (flip_contract is_server |~ transmit 1%:i01 a)
      ins result fns) :
  result = Some a /\ fns = ins.
Proof.
move: run.
rewrite freer_to_hoare_bindE to_hoare_triggerE /=.
case=> res; case=> net; case.
rewrite provided_calleeP /=; case=> ->.
inversion 1; ssubst; last first.
  by move: H0 H2; rewrite onem_eq1=> ->; rewrite ltxx.
by rewrite post_ret=> -[<- <-].
Qed.
End transmission.

#[export] Hint Extern 0 (providesOnlyF (transmit _ _)) =>
  solve [exact: syn_transmit] : core.

Section protocol.
Context {clientF serverF ProtoF : effect}.
Context `{HFclient: client_api ;; @FlipEff R -<< clientF}.
Context `{HFserver: server_api ;; @FlipEff R -<< serverF}.
Context `{HFproto: clientF ;; serverF -<< ProtoF}.
Context {M : choiceEqFreerMonad ProtoF R _}.


Definition client_flipF : @FlipEff R -< ProtoF :=
  @provideT ProtoF clientF (@FlipEff R) HFclient.(p2) HFproto.(p1).

Definition server_flipF : @FlipEff R -< ProtoF :=
  @provideT ProtoF serverF (@FlipEff R) HFserver.(p2) HFproto.(p2).

(* TODO put in common *)
Inductive ping_round : effect := one_round : ping_round outcome.

(* Ok, so, here there are 2 paths to try :
 1. Try a 2 component approach using probabilistic components
 2. Remake it using 2 different transmits.
 Starting with number 2 will be faster for now, need to go best effort.
 *)
Definition prob_ping_proto (p : {prob R}) : M outcome :=
  ping_pong_with (transmit (H:=client_flipF)) (transmit (H:=server_flipF))
    send reply (fun=>recv) (fun=>wait) p.

Definition prob_ping_protocol (p : {prob R}) : component ping_round ProtoF :=
  fun _ cmd=>
    match cmd with
    | one_round => prob_ping_proto p
    end.

Definition prob_ping_contract : contract ProtoF net_state :=
(client_c -^- flip_contract true) -^-
(server_c -^- flip_contract false).

Lemma pre_ping1 net :
  pre (prob_ping_contract |~ prob_ping_protocol (1%:i01) _ one_round) net.
Proof.
rewrite /prob_ping_protocol /prob_ping_proto /ping_pong_with.
rewrite /client_send /server_reply /client_receive /round_of /serve_of
  /answer_of.
rewrite !bindA /prob_ping_contract.
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_left //.
split; first by rewrite send_respect.
move=> [] [s1 c1] /send_run /= [-> ->].
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_right //.
split; first by apply: pre_transmit1.
move=> ? [s2 c2].
move/(post_transmit1 true)=> /= [] // ? [] -> ->.
rewrite freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_left //.
split; first by rewrite recv_respect; exact/eqP.
move=> om [s3 c3].
move/recv_run=> /= [] -> ->.
case: om=> [[]|].
rewrite bindA freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_left //.
split; first by rewrite reply_respect.
move=> ? [s4 c4].
move/reply_run=> /= [] -> ->.
rewrite bindA freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_right //.
split; first by exact: (pre_transmit1 false).
move=> ? [s5 c5].
move/(post_transmit1 false)=> /= [] // ? [] -> ->.
all: rewrite bindretf.
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_left //.
split; first by rewrite wait_respect; exact/eqP.
move=> om [s6 c6].
move/wait_run=> /= [] -> ->.
case: om=> [[]|].
all: by rewrite pre_ret.
Qed.

Lemma post_ping1 {net res net'}
  (inv : chan_inv net)
  (run : post (prob_ping_contract |~ prob_ping_protocol (1%:i01) _ one_round)
    net res net') :
  chan_inv net'.
Proof.
  move: inv run.
  case: net=> s0 c0 [_ c0_ok].
  rewrite /prob_ping_protocol /prob_ping_proto /ping_pong_with.
  rewrite /client_send /server_reply /client_receive /round_of /serve_of
    /answer_of.
  rewrite !bindA /prob_ping_contract.

rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_left //.
case;case; case;case=> s1 c1; case.
move/send_run=>/= [-> ->].
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_right //.
case=>ou; case;case=> s2 c2; case.
move/(post_transmit1 true)=>/= [] // ? ->.
rewrite freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_left //.
case=> output; case;case=> s3 c3; case.
move/recv_run=>/= [-> ->].
case: output=> [[]|] /=.
(*3 cases from here:
 - Ping => we go through
 - Pong => should not be possible
 - None => we do nothing *)
(* I. Ping. *)
  - rewrite bindA freer_to_hoare_bindE freer_contract_right //
      freer_contract_prodT freer_contract_left //.
    case;case; case;case=> s4 c4;case.
    move/reply_run=>/= [-> ->].
    rewrite bindA freer_to_hoare_bindE freer_contract_right //
      freer_contract_prodT freer_contract_right //.
    case=>ou'; case;case=> s5 c5;case.
    move/(post_transmit1 false)=>/= [] // ? ->.
  all: rewrite bindretf.
  - rewrite freer_to_hoare_bindE freer_contract_left //
      freer_contract_prodT freer_contract_left //.
    case=> output; case;case=> s6 c6; case.
    move/wait_run=>/= [-> ->].
    case: output=> [[]|].
    all: by rewrite post_ret=> -[] _ <-; split=> //; apply/eqP.
Qed.

Theorem ping_correct :
  correct_component (prob_ping_protocol 1%:i01) (no_contract ping_round)
    prob_ping_contract
    (fun=> chan_inv).
Proof.
move=>[] n inv ? [] []; split=>[|m n' Hpost] /=.
  exact: pre_ping1.
  by split=>//; move: (post_ping1 inv Hpost).
Qed.
End protocol.
End ProbProtocolM.
