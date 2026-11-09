
From mathcomp Require Import boot order algebra interval_inference.
From mathcomp Require Import classical_sets boolp reals Rstruct.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order.
#[warning="-notation-incompatible-prefix"]
From mathcomp Require Import all_analysis finmap.
From infotheo Require Import convex fsdist realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import all_freerdps ping_common ping_client_serv_freespec.

Local Open Scope proba_scope.
Local Open Scope convex_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope monae_scope.
Import ChoiceRelation Order.LTheory GRing.Theory Num.Theory.

Section about_freer_flip_monad.
Context {R : realType} {Fx: effect}
  `{@FlipEff R -< Fx} {M : choiceEqFreerMonad Fx R}.

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
Section flip_contract.

Lemma fdist1_serverQ (p: {prob R}) nQ n1 n2 :
  fsdist1 nQ = fsdist1 n1 <| p |> fsdist1 n2 ->
  fsdist1 (serverQ nQ) = fsdist1 (serverQ n1) <| p |> fsdist1 (serverQ n2).
Proof.
move/(congr1 (fsdistmap serverQ)).
by rewrite fsdistmap_affine !fsdistmap1.
Qed.

Lemma fdist1_clientQ (p: {prob R}) nQ n1 n2 :
  fsdist1 nQ = fsdist1 n1 <| p |> fsdist1 n2 ->
  fsdist1 (clientQ nQ) = fsdist1 (clientQ n1) <| p |> fsdist1 (clientQ n2).
Proof.
move/(congr1 (fsdistmap clientQ)).
by rewrite fsdistmap_affine !fsdistmap1.
Qed.

Definition flip_step is_server ns :
  forall X, @FlipEff R X -> X -> R.-dist net_state :=
  fun T op => match op in (@FlipEff _ T) return T -> R.-dist net_state with
  | flipe p => fun _kept => drop_new_packet ns p is_server
  end.
  (* avec prob p :
  dist p {
  - keep => Ret ns
  - drop => drop_new_packet ns is_server  } *)

Definition select_queue (is_server : bool) ns : packet :=
  if is_server then serverQ ns else clientQ ns.

Definition expected_packet (is_server : bool) : packet :=
  if is_server then Some Ping else Some Pong.

Definition flip_requirement is_server (d : R.-dist net_state) :
    forall X, @FlipEff R X -> Prop :=
  fun _ _ => exists q : {prob R}, fsdistmap (select_queue is_server) d
    = fsdist1 (expected_packet is_server) <| q |> fsdist1 (None : packet).

Definition flip_promise is_server (d : R.-dist net_state) :
    forall X, @FlipEff R X -> X -> Prop :=
  fun X op => match op in (@FlipEff _ X) return X -> Prop with
  | flipe p => fun kept =>
    let d' := fsdistbind d (fun ns => drop_new_packet ns p is_server) in
    fsdistmap (select_queue is_server) d'
      = fsdistmap (select_queue is_server) d <| p |> fsdist1 (None : packet)
    /\ fsdistmap (select_queue (~~ is_server)) d'
       = fsdistmap (select_queue (~~ is_server)) d
    /\ exists (q : {prob R}) (rest : R.-dist bool), q != 0%:i01
       /\ fsdist1 true <| p |> fsdist1 false = fsdist1 kept <| q |> rest
  end.

Definition flip_contract (is_server : bool) :
    contract R (@FlipEff R) net_state :=
  make_contract
    (flip_step is_server)
    (flip_requirement is_server)
    (flip_promise is_server).

(* TODO: Check if this lemma is useful. *)
Lemma flip_promise_possible is_server (d : R.-dist net_state) (p : {prob R})
    (kept : bool) (possible : if kept then p != 0%:i01 else p != 1%:i01) :
  flip_promise is_server d bool (flipe p) kept.
Proof.
have bind_cst (e : R.-dist packet) : fsdistbind d (fun=> e) = e.
  apply/fsdist_ext=> x; rewrite fsdistbindE -big_distrl /=.
  by rewrite FSDist.f1 mul1r.
rewrite /= /fsdistmap !fsdistbindA; split; [|split].
- have flipped : (fun ns => fsdistbind (drop_new_packet ns p is_server)
        (fun ns' => fsdist1 (select_queue is_server ns')))
      = (fun ns => fsdist1 (select_queue is_server ns))
        <| p |> (fun=> fsdist1 (None : packet)).
    apply: boolp.funext=> ns.
    transitivity (fsdist1 (select_queue is_server ns)
      <| p |> fsdist1 (None : packet)); last by [].
    by case: is_server; case: ns=> ? ?;
      rewrite /= fsdist_conv_bind_left_distr !fsdist1bind.
  by rewrite flipped fsdist_conv_bind_right_distr bind_cst.
- congr fsdistbind; apply: boolp.funext=> ns.
  by case: is_server; case: ns=> ? ?; rewrite /= fsdist_conv_bind_left_distr
    !fsdist1bind convmm.
case: kept possible=> possible.
  by exists p, (fsdist1 false).
exists (p%:num.~)%:i01, (fsdist1 true); split; last exact: convC.
by apply/prob_gt0; rewrite /= subr_gt0; exact/prob_lt1.
Qed.

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

Lemma drop_new_packet1 ns is_server :
  drop_new_packet ns 1%:i01 is_server = fsdist1 ns.
Proof. by case: is_server; case: ns=> ? ?; rewrite /= conv1. Qed.

Lemma pre_transmit1 {A} is_server (a : A) (net : net_state)
    (queued : select_queue is_server net = expected_packet is_server) :
  pre (flip_contract is_server |~ transmit 1%:i01 a) (fsdist1 net).
Proof.
rewrite /transmit /freer_choice /flip.
rewrite freer_to_hoare_bindE.
split; last by case; rewrite pre_ret.
rewrite pre_to_hoare_triggerP /= /flip_requirement fsdistmap1 queued.
by exists 1%:i01; rewrite conv1.
Qed.

Lemma post_transmit1 {A} is_server {a : A} {ins : net_state}
    {fns : R.-dist net_state} {result : option A}
    (run : post (flip_contract is_server |~ transmit 1%:i01 a)
      (fsdist1 ins) result fns) :
  result = Some a /\ fns = fsdist1 ins.
Proof.
move: run.
rewrite /transmit /freer_choice /flip freer_to_hoare_bindE.
case=> kept [d1 []].
rewrite post_to_hoare_triggerP fsdist1bind /= drop_new_packet1.
case=> -> [_ [_ [q [rest [q_neq0]]]]].
rewrite conv1.
case: kept; first by rewrite post_ret=> _ [<- <-].
move/(congr1 (fun d : R.-dist bool => d false)).
rewrite fsdist_convE fsdist1xx fsdist10 // avgRE mulr1=> /esym/eqP.
rewrite gt_eqF // ltr_pwDl ?mulr_ge0 //.
exact/prob_gt0.
Qed.

Lemma flip_requirement_after_flip is_server ns (p : {prob R})
    (queued : select_queue is_server ns = expected_packet is_server) :
  flip_requirement is_server (drop_new_packet ns p is_server) bool (flipe p).
Proof.
exists p; rewrite -queued.
by case: is_server {queued}; case: ns=> ? ?;
  rewrite /= fsdistmap_affine !fsdistmap1.
Qed.

Lemma recv_requirement_after_flip ns (p : {prob R})
    (queued : serverQ ns = Some Ping) :
  requirement server_c (drop_new_packet ns p true) RECV.
Proof.
case: ns queued=> ? ? /= ->.
rewrite fsdistmap_affine !fsdistmap1 !asboolT ?convmm //.
all: exact/eqP.
Qed.

End transmission.

#[export] Hint Extern 0 (providesOnlyF (transmit _ _)) =>
  solve [exact: syn_transmit] : core.

Section protocol.
Context {clientF serverF ProtoF : effect}.
Context `{HFclient: client_api ;; @FlipEff R -<< clientF}.
Context `{HFserver: server_api ;; @FlipEff R -<< serverF}.
Context `{HFproto: clientF ;; serverF -<< ProtoF}.
Context {M : choiceEqFreerMonad ProtoF R}.


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

Definition prob_ping_contract : contract R ProtoF net_state :=
(client_c -^- flip_contract true) -^-
(server_c -^- flip_contract false).

(* TODO put in common *)
Definition ping_inv (net : net_state) :=
  (serverQ net = None) /\ (clientQ net = None).

Lemma pre_ping1 net :
  ping_inv net ->
  pre (prob_ping_contract |~ prob_ping_protocol (1%:i01) _ one_round)
    (fsdist1 net).
Proof.
move=> [s0 c0].
rewrite /prob_ping_protocol /prob_ping_proto /ping_pong_with.
rewrite /client_send /server_reply /client_receive.
rewrite !bindA /prob_ping_contract.
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_left //.
split; first by exact:send_respect.
move=> [] d1 /send_run [[s1 c1] [-> /=]].
rewrite c0=> -[] -> ->.
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_right //.
split; first by apply: pre_transmit1.
move=> ? d2.
move/(post_transmit1 true)=> /= [] // ? ->.
rewrite freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_left //.
split; first by exact/recv_respect/eqP.
move=> om d3.
move/recv_run=> [[s3 c3] [-> /= [-> ->]]].
case: om=> [[]|].
rewrite bindA freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_left //.
split; first by exact: reply_respect.
move=> ? d4.
move/reply_run=> [[s4 c4] [-> /= [-> ->]]].
rewrite bindA freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_right //.
split; first by exact: (pre_transmit1 false).
move=> ? d5.
move/(post_transmit1 false)=> /= [] // ? ->.
all: rewrite bindretf.
rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_left //.
split; first by exact/wait_respect/eqP.
move=> om d6.
move/wait_run=> [[s6 c6] [-> /= [-> ->]]].
case: om=> [[]|].
all: by rewrite pre_ret.
Qed.

Lemma post_ping1 {net res net'}
  (H: ping_inv net)
  (run: post (prob_ping_contract |~ prob_ping_protocol (1%:i01) _ one_round)
    (fsdist1 net) res net') :
  dist_inv ping_inv net'.
Proof.
  case: H run.
  case: net=>??/= -> ->.
  rewrite /prob_ping_protocol /prob_ping_proto /ping_pong_with.
  rewrite /client_send /server_reply /client_receive.
  rewrite !bindA /prob_ping_contract.

rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_left //.
case; case; case=> d1; case.
move/send_run=> [[s1 c1] [-> /= [-> ->]]].


rewrite freer_to_hoare_bindE freer_contract_left //
  freer_contract_prodT freer_contract_right //.
case=>ou; case=> d2; case.
move/(post_transmit1 true)=>/= [] // ? ->.

rewrite freer_to_hoare_bindE freer_contract_right //
  freer_contract_prodT freer_contract_left //.
case=> output; case=> d3; case.
move/recv_run=> [[s3 c3] [-> /= [-> ->]]].

case: output=> [[]|] /=.
(*3 cases from here:
 - Ping => we go through
 - Pong => should not be possible
 - None => we do nothing *)

(* I. Ping. *)
  - rewrite bindA freer_to_hoare_bindE freer_contract_right //
      freer_contract_prodT freer_contract_left //.
    case; case; case=> d4; case.
    move/reply_run=> [[s4 c4] [-> /= [-> ->]]].

    rewrite bindA freer_to_hoare_bindE freer_contract_right //
      freer_contract_prodT freer_contract_right //.
    case=>ou'; case=> d5; case.
    move/(post_transmit1 false)=>/= [] // ? ->.
  all: rewrite bindretf.
  - rewrite freer_to_hoare_bindE freer_contract_left //
      freer_contract_prodT freer_contract_left //.
    case=> output; case=> d6; case.
    move/wait_run=> [[s6 c6] [-> /= [-> ->]]].
    case: output=> [[]|].
    all: by rewrite post_ret=> -[] _ <-; eexists.
Qed.

Theorem ping_correct :
  correct_component (prob_ping_protocol 1%:i01) (no_contract R ping_round)
    prob_ping_contract (fun=> dist_inv ping_inv).
Proof.
move=> ? ? [n [-> inv]] ? [] []; split=> [|m n' Hpost] /=.
  exact: pre_ping1.
  by split=>//; move: (post_ping1 inv Hpost).
Qed.
End protocol.
End ProbProtocolM.
