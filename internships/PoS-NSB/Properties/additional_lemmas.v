From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Reals Interval.Tactic.

From AUChain Require Import GlobalState CG.
From mathcomp.analysis_stdlib Require Import Rstruct_topology.
From AUChain Require Import Schedule.
From mathcomp Require Import (canonicals) Rstruct.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal interval_inference topology normedtype.
From mathcomp Require Import sequences realfun convex real_interval.
From mathcomp Require Import derive esum measure measurable_realfun.
From mathcomp Require Import kernel probability.
From mathcomp Require Import hoelder unstable.
From mathcomp Require Import archimedean.
From HB Require Import structures.
From AUChain Require Import sampling.
From AUChain Require Import
  Network Protocol Blocks Messages MessageTuple Parameters BlockTree LocalState
  MemEq SsrFacts TreeChain.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import hoelder ess_sup_inf.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Set Printing Notations.
Local Open Scope ereal_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope schedule_scope.
Section set_lemmas.
  Context (n : nat) (R : realType) {d} (T : measurableType d)
    (P : probability T R) (NT : n.-tuple T).

Lemma ST_Set :  forall {I : Type} (s : set I) , setT `&` s = s.
Proof.
move=> I s; apply/seteqP.
by split=> i //= [_ ]; exact.
Qed.

Lemma setT_def {I : Type} : ([set _ | true] : set I) = setT.
Proof. by apply/seteqP; split. Qed.

Lemma set0_def {I : Type} : ([set _ | false] : set I) = set0.
Proof. by apply/seteqP; split. Qed.

Lemma set_lt_eq_neg_le :
    forall (X : (n.-tuple T) -> R) (B : R),
      [set r  | (B < X r)%R] = ~` [set r | (X r <= B)%R].
Proof.
by move=> X B; apply/seteqP; split=> r //=; rewrite ltNge=>/negP; exact.
Qed.

Lemma set_le_eq_neg_le :
    forall (X : (n.-tuple T) -> R) (B : R),
    [set r | ~~ (X r <= B)%R] = ~` [set r | (X r <= B)%R].
Proof.
by move=> X B; apply/seteqP; split=> i //= /negP; exact.
Qed.

Lemma set_gt_as_compl_le {I : Type} (X : I -> R) (B : R) :
    [set r : I | (B < X r)%R] = [set r : I | ~~ (B >= X r)%R].
Proof. by apply/seteqP; split=> r //=; rewrite -ltNge.  Qed.

Lemma set_lt_as_compl_ge {I : Type} (X : I -> R) (B : R) :
    [set r : I | (X r < B)%R] = [set r : I | ~~ (B <= X r)%R].
Proof. by apply/seteqP; split=> r //=; rewrite -ltNge. Qed.

Import MeasurableR.
Lemma complementary_specialized_le (Q : probability T R) (X: (n.-tuple T) -> R)
  (B : R) (Hm : measurable_fun setT X) :
    (\X_n Q) [set i | ~~ (X i <= B)%R]%R
    =
    (((1%R)%:E - (\X_n Q) [set i | X i <= B]%R))%E.
Proof.
rewrite (set_le_eq_neg_le X B); apply probability_setC.
rewrite -(ST_Set ([set i | X i <= B])).
apply: (measurable_fun_le (D := setT) (f := X) (g := fun _ => B))=>//=.
Qed.

Lemma try :
    forall (X : (n.-tuple T) -> R) (B : R),
    [set r  | (X r < B)%R] = ~` [set r | ( B <= X r)%R].
Proof.
by move=> X B; apply/seteqP; split=>r; rewrite /= ltNge=>/negP; apply.
Qed.

Lemma try2 :
    forall (X : (n.-tuple T) -> R) (B : R),
    [set r | ( B <= X r)%R] =  ~` [set r  | (X r < B)%R] .
Proof.
move=> X B; apply/seteqP; split=> r Hr /=.
- by rewrite ltNge Hr.
- by rewrite leNgt; apply/negP.
Qed.

Lemma try3 :
    forall (X : (n.-tuple T) -> R) (B : R),
    [set r | ( X r <= B)%R] =  ~` [set r  | (B < X r)%R] .
Proof.
move=> X B; apply/seteqP; split=> r Hr /=.
- by rewrite ltNge Hr.
- by rewrite leNgt; apply/negP.
Qed.

End set_lemmas.
