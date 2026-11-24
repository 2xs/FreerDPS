From mathcomp Require Import boot order algebra interval_inference.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy proba_lib.
From FreerDPS Require Import ping_common.

Local Open Scope nat_scope.
Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope proba_monad_scope.

Section about_probMonad.
Context {R : realType} {M : probMonad R}.

Fact bcoin_or_true (p q : {prob R}) :
  Ret true <| p |> bcoin q = bcoin [s_of p, q] :> M bool.
Proof. by rewrite /bcoin choiceA choicemm. Qed.

End about_probMonad.

Section lossy_round_trip.
Context {R : realType} {M : probMonad R}.
Implicit Types (m : msg) (psucc : {prob R}).

Definition transmit psucc m : M (option msg) :=
  Ret (Some m) <| psucc |> Ret None.

Lemma transmit1 m : transmit 1%:i01 m = Ret (Some m).
Proof. exact: choice1. Qed.

Lemma ping_pong1 : ping_pong (transmit:=transmit) 1%:i01 = Ret GotPong.
Proof.
rewrite ping_pongE.
by rewrite transmit1 bindretf transmit1 bindretf.
Qed.

Lemma ping_pongs1 fuel : ping_pongs (transmit:=transmit) 1%:i01 fuel = Ret GotPong.
Proof.
by elim : fuel => [|n IH];
    rewrite ping_pongsE ping_pong1 ?bindretf.
Qed.

Lemma ping_pong_distribution psucc :
    ping_pong (transmit:=transmit) psucc = exchange_once (choose:=choice) psucc.
Proof.
rewrite ping_pongE.
by repeat rewrite choice_bindDl !bindretf.
Qed.

Lemma ping_pongs_exchanges psucc fuel :
  ping_pongs (transmit:=transmit) psucc fuel = exchanges (choose:=choice) psucc fuel.
Proof.
elim: fuel => [|fuel IH].
  exact: ping_pong_distribution.
rewrite ping_pongsSE ping_pong_distribution exchangesSE.
by rewrite !choice_bindDl !bindretf IH.
Qed.

Lemma ping_pong_success_probability psucc :
  ping_pong_success (transmit:=transmit) psucc = bcoin (p_exchange_once psucc).
Proof.
rewrite ping_pong_successE success_ofE ping_pong_distribution.
rewrite /exchange_once p_exchange_onceE /bcoin.
rewrite !choice_bindDl !bindretf !success_eventE.
have [->/=|p0] := eqVneq psucc 0%:i01; first by rewrite p_of_0s !choice0.
have [->/=|p1] := eqVneq psucc 1%:i01; first by rewrite p_of_1s choice1.
have pp1 : [p_of psucc, psucc] != 1%:i01 by rewrite p_of_rs1 (negbTE p1) andbF.
rewrite -[Ret false in RHS](choicemm [q_of psucc, psucc]).
by rewrite choiceA (s_of_pqK pp1) (r_of_pqK pp1 p0).
Qed.

Lemma ping_pongs_success_stepE p fuel :
  ping_pongs_success (transmit:=transmit) p (fuel.+1) =
    (Ret true <| p |> ping_pongs_success (transmit:=transmit) p fuel) <| p |>
    ping_pongs_success (transmit:=transmit) p fuel.
Proof.
  rewrite ping_pongs_successE success_ofE ping_pongsE ping_pongE.
  repeat rewrite !choice_bindDl !bindretf.
  by rewrite success_eventE.
Qed.

Lemma ping_pong_retry_success_probability psucc (fuel : nat) :
  ping_pongs_success (transmit:=transmit) psucc fuel =
    bcoin (p_exchanges psucc fuel).
Proof.
elim: fuel=> [|n]; first exact: ping_pong_success_probability.
rewrite ping_pongs_success_stepE !p_exchangesE p_exchangeE p_exchange_onceE=> ->.
have [->/=|p0] := eqVneq psucc 0%:i01.
  by rewrite p_of_0s s_of_0q choice0.
have [->/=|p1] := eqVneq psucc 1%:i01.
  by rewrite /bcoin p_of_1s s_of_1q !choice1.
rewrite -p_exchangesE.
rewrite -(bcoin_or_true [p_of psucc, psucc] (p_exchanges psucc n)).
have pp1 : [p_of psucc, psucc] != 1%:i01 by rewrite p_of_rs1 (negbTE p1) andbF.
rewrite -[bcoin (p_exchanges psucc n) in RHS](choicemm [q_of psucc, psucc]).
by rewrite choiceA (s_of_pqK pp1) (r_of_pqK pp1 p0).
Qed.
End lossy_round_trip.
