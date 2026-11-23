(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

From HB Require Import structures.
From mathcomp Require Import boot boolp functions ssrnum ssralg.
From mathcomp Require Import interval_inference.
From mathcomp Require Import unstable reals Rstruct.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib state_lib.
From monae Require Import monad_transformer proba_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_monad_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope monae_scope.

(******************************************************************************)
(* State and probabilistic choice.                                            *)
(*                                                                            *)
(* This relies on stateT embedding a probMonad. This way we don't need to     *)
(* actually over engineer the laws of state + prob, nor a model.              *)
(******************************************************************************)

(* If we wanted to go for prob + state + nondet, we would rely on nondet's *)
(* right assoc *)
#[short(type=probDrStateMonad)]
HB.structure Definition MonadProbDrState (R : realType) (S : UU0) :=
  {M of MonadProbDr R M & MonadState S M}.

Module ProbStateModel.
Section prob_state_model.
Context {R : realType} (S : UU0) (N : probDrMonad R).

Let choiceS (p : {prob R}) (A : UU0) (m1 m2 : MS S N A) : MS S N A :=
  fun s => m1 s <| p |> m2 s.

Let choiceS1 (A : UU0) (a b : MS S N A) : choiceS 1%:i01 a b = a.
Proof. by apply: funext=> s; exact: choice1. Qed.

Let choiceSC (A : UU0) p (a b : MS S N A) :
  choiceS p a b = choiceS (p%:num.~%:i01) b a.
Proof. by apply: funext=> s; exact: choiceC. Qed.

Let choiceSmm (A : UU0) p : idempotent_op (@choiceS p A).
Proof. by move=> a; apply: funext=> s; exact: choicemm. Qed.

Let choiceSA (A : UU0) (p q : {prob R}) (a b c : MS S N A) :
  choiceS p a (choiceS q b c) =
  choiceS [s_of p, q] (choiceS [r_of p, q] a b) c.
Proof. by apply: funext=> s; exact: choiceA. Qed.

HB.instance Definition _ := isMonadConvex.Build R (MS S N)
  choiceS choiceS1 choiceSC choiceSmm choiceSA.

Let bindDl p :
  BindLaws.left_distributive (@hierarchy.bind (MS S N)) (choice p).
Proof.
by move=> A B m1 m2 k; apply: funext=> s; rewrite !MS_bindE choice_bindDl.
Qed.

Let bindDr p :
  BindLaws.right_distributive (@hierarchy.bind (MS S N)) (choice p).
Proof.
move=> A B m k1 k2; apply: funext=> s.
have -> : ((m >>= k1) <| p |> (m >>= k2)) s =
    (m >>= k1) s <| p |> (m >>= k2) s by [].
rewrite !MS_bindE -choice_bindDr.
by congr (_ >>= _); apply: funext=> -[].
Qed.

HB.instance Definition _ := isMonadProb.Build R (MS S N) bindDl.
HB.instance Definition _ := isMonadConvexDr.Build R (MS S N) bindDr.

End prob_state_model.
End ProbStateModel.
HB.export ProbStateModel.
