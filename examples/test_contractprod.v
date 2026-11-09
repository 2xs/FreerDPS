From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat choice boolp reals.
From infotheo Require Import fsdist.
From monae Require Import hierarchy.
From FreerDPS Require Import all_freerdps.

(* File written by claude to verify that contractprod works correctly. *)
(* Checks [contractprod] on two stores: each contract only sees
   its own effect and its own component of the product witness. *)

Local Open Scope contract_scope.

Section two_stores.
Context {R : realType}.

Local Abbreviation Fx := (eplus (STORE nat) (STORE bool)).
Local Abbreviation c :=
  (store_specs R nat -*- store_specs R bool : contract R Fx (nat * bool)).

Definition put_then_get : freer Fx nat := iput 3%N >> iget.

(* [Put] changes the first component only. *)
Lemma put3_update (n : nat) (b : bool) :
  gen_state_update c (fsdist1 (n, b)) (inj (Put 3%N) : Fx _) tt =
  fsdist1 (3%N, b).
Proof.
by rewrite /gen_state_update /= fsdist1bind /gen_state_update /=
  !fsdist1bind dist_pair1.
Qed.

Lemma put_then_get_pre (n : nat) (b : bool) :
  pre (c |~ put_then_get) (fsdist1 (n, b)).
Proof.
rewrite freer_to_hoare_bindE; split.
  rewrite to_hoare_triggerE /=; apply/contractprod_requirement1.
  by rewrite /gen_requirement /=; split=> //; rewrite fsdistmap1 asboolT.
move=> [] d1; rewrite to_hoare_triggerE => -[-> _].
rewrite put3_update to_hoare_triggerE /=; apply/contractprod_requirement1.
by rewrite /gen_requirement /=; split=> //; rewrite fsdistmap1 asboolT.
Qed.

Lemma put_then_get_post (n : nat) (b : bool) (m : nat)
    (d : R.-dist (nat * bool))
    (run : post (c |~ put_then_get) (fsdist1 (n, b)) m d) :
  m = 3%N /\ d = fsdist1 (3%N, b).
Proof.
move: run; rewrite freer_to_hoare_bindE => -[[] [d1 []]].
rewrite to_hoare_triggerE => -[-> _].
rewrite put3_update to_hoare_triggerE => -[->].
move/contractprod_promise1=> [+ _].
rewrite /gen_promise /= fsdistmap1 => /fsdist1_inj/asboolP <-; split=> //.
by rewrite /gen_state_update /= fsdist1bind /gen_state_update /=
  !fsdist1bind dist_pair1.
Qed.

End two_stores.
