From mathcomp Require Import boot boolp interval_inference.
From mathcomp Require Import ssrnum ssralg reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From HB Require Import structures.

Import GRing.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope monae_scope.

Inductive msg := Ping | Pong.
HB.instance Definition _ := gen_eqMixin msg.
Inductive outcome := GotPong | LostPing | LostPong.
HB.instance Definition _ := gen_eqMixin outcome.

Section syntactic_sugar_for_probabilities.
Context {R : realType}.

Definition p_exchange_once (p : {prob R}) : {prob R} := [p_of p, p].

Lemma p_exchange_onceE p : p_exchange_once p = [p_of p, p].
Proof. by []. Qed.

Definition p_exchange (psucc retry : {prob R}) : {prob R} :=
  [s_of (p_exchange_once psucc), retry].

Fixpoint p_exchanges (loss : {prob R}) n : {prob R} :=
  if n is n'.+1 then p_exchange loss (p_exchanges loss n') else p_exchange_once loss.

Lemma p_exchangesE psucc n :
  p_exchanges psucc n =
    if n is n'.+1 then p_exchange psucc (p_exchanges psucc n')
    else p_exchange_once psucc.
Proof. by case: n. Qed.

Lemma p_exchangeE psucc retry :
  p_exchange psucc retry = [s_of (p_exchange_once psucc), retry].
Proof. by []. Qed.

Fact retry0 : forall n, p_exchanges (widen_itv 0%:itv) n = 0%:i01.
Proof.
by elim=> [|n IH];
  rewrite p_exchangesE ?p_exchangeE p_exchange_onceE p_of_0s // s_of_0q IH.
Qed.

Fact retry1 : forall n, p_exchanges (widen_itv 1%:itv) n = 1%:i01.
Proof.
by case=> [|n];
  rewrite p_exchangesE ?p_exchangeE p_exchange_onceE p_of_1s // s_of_1q.
Qed.

End syntactic_sugar_for_probabilities.

Section ping_pong_protocol.
Context {R : realType} {M : monad}.
Implicit Types (m : msg) (psucc : {prob R}).

Fixpoint retry_ping_pong (run : M outcome) (fuel : nat) : M outcome :=
  if fuel is fuel'.+1 then
    run >>= fun result =>
      if result is GotPong then Ret GotPong else retry_ping_pong run fuel'
  else
    run.

Section custom_protocol.
Context {A B C : Type}.
Context (client_transmit : {prob R} -> A -> M B).
Context (server_transmit : {prob R} -> A -> M C).
Context (initial_prog reply : M A).
Context (retrieve_input : B -> M (option msg)).
Context (wait_data : C -> M (option msg)).

Definition client_send psucc : M B :=
  initial_prog >>= client_transmit psucc.

(* None marks a missing Ping; Some carries the reply transmission result. *)
Definition server_reply psucc sent : M (option C) :=
  retrieve_input sent >>= fun to_server =>
    if to_server is Some Ping then
      (reply >>= server_transmit psucc) >>= fun sent => Ret (Some sent)
    else Ret None.

Definition client_receive sent : M outcome :=
  wait_data sent >>= fun from_server =>
    if from_server is Some Pong then Ret GotPong else Ret LostPong.

Definition ping_pong_with psucc : M outcome :=
  (client_send psucc >>= server_reply psucc) >>= fun response =>
    if response is Some sent then client_receive sent else Ret LostPing.

Definition ping_pongs_with psucc (fuel : nat) : M outcome :=
  retry_ping_pong (ping_pong_with psucc) fuel.

Lemma ping_pongs_withE psucc fuel :
  ping_pongs_with psucc fuel =
    if fuel is fuel'.+1 then
      ping_pong_with psucc >>= fun result =>
        if result is GotPong then Ret GotPong else ping_pongs_with psucc fuel'
    else
      ping_pong_with psucc.
Proof. by case: fuel. Qed.

Lemma ping_pongs_withSE psucc fuel :
  ping_pongs_with psucc fuel.+1 =
    ping_pong_with psucc >>= fun result =>
      if result is GotPong then Ret GotPong else ping_pongs_with psucc fuel.
Proof. by []. Qed.

End custom_protocol.
End ping_pong_protocol.

Section default_ping_pong_protocol.
Context {R : realType} {M : monad}.
Context {transmit : {prob R} -> msg -> M (option msg)}.
Implicit Types (m : msg) (psucc : {prob R}).

Definition ping_pong psucc : M outcome :=
  ping_pong_with transmit transmit (Ret Ping) (Ret Pong)
    (fun packet => Ret packet) (fun packet => Ret packet) psucc.

Definition ping_pongs psucc (fuel : nat) : M outcome :=
  ping_pongs_with transmit transmit (Ret Ping) (Ret Pong)
    (fun packet => Ret packet) (fun packet => Ret packet) psucc fuel.

Lemma ping_pongE psucc :
  ping_pong psucc =
    (transmit psucc Ping >>= fun to_server =>
      if to_server is Some Ping then
        transmit psucc Pong >>= fun from_server =>
          if from_server is Some Pong then Ret GotPong else Ret LostPong
      else Ret LostPing).
Proof.
rewrite /ping_pong /ping_pong_with /client_send /server_reply /client_receive.
rewrite !bindretf bindA.
congr (transmit psucc Ping >>= _).
apply: boolp.funext=> -[[]|]; rewrite !bindretf //.
rewrite bindA.
congr (transmit psucc Pong >>= _).
by apply: boolp.funext=> packet; rewrite !bindretf.
Qed.

Lemma ping_pongsE psucc fuel :
  ping_pongs psucc fuel =
    if fuel is fuel'.+1 then
      ping_pong psucc >>= fun result =>
        if result is GotPong then Ret GotPong else ping_pongs psucc fuel'
    else
      ping_pong psucc.
Proof. by case: fuel. Qed.

Lemma ping_pongsSE psucc fuel :
  ping_pongs psucc fuel.+1 =
    ping_pong psucc >>= fun result =>
      if result is GotPong then Ret GotPong else ping_pongs psucc fuel.
Proof. by []. Qed.

Definition success_event : pred outcome := fun result =>
  if result is GotPong then true else false.

Definition success_of (run : M outcome) : M bool :=
  run >>= fun result => Ret (success_event result).

Definition ping_pong_success p : M bool := success_of (ping_pong p).

Definition ping_pongs_success p fuel : M bool :=
  success_of (ping_pongs p fuel).

Lemma success_eventE result :
  success_event result = if result is GotPong then true else false.
Proof. by case: result. Qed.

Lemma success_ofE run :
  success_of run = (run >>= fun result => Ret (success_event result)).
Proof. by []. Qed.

Lemma ping_pong_successE p :
  ping_pong_success p = success_of (ping_pong p).
Proof. by []. Qed.

Lemma ping_pongs_successE p fuel :
  ping_pongs_success p fuel = success_of (ping_pongs p fuel).
Proof. by []. Qed.

End default_ping_pong_protocol.

Section ping_pong_distribution.
Context {R : realType} {M : monad} {choose : {prob R} -> forall A, M A -> M A -> M A}.

Definition exchange psucc lostping lostpong : M outcome :=
  choose psucc  _ (choose psucc _ (Ret GotPong) lostpong) lostping.

Definition exchange_once psucc : M outcome :=
  exchange psucc (Ret LostPing) (Ret LostPong).

Fixpoint exchanges psucc fuel : M outcome :=
  if fuel is fuel'.+1 then
    exchange psucc (exchanges psucc fuel') (exchanges psucc fuel')
  else
    exchange_once psucc.

Lemma exchangesSE psucc fuel :
  exchanges psucc fuel.+1 =
    exchange psucc (exchanges psucc fuel) (exchanges psucc fuel).
Proof. by []. Qed.

End ping_pong_distribution.
