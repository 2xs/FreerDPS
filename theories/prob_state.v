From HB Require Import structures.
From mathcomp Require Import boot boolp functions ssrnum ssralg.
From mathcomp Require Import interval_inference.
From mathcomp Require Import unstable reals Rstruct.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib state_lib.
From monae Require Import monad_transformer proba_model.
From FreerDPS Require Import init effect freer free_choice contract component.

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
(*                                                                            *)
(* This also adds a dedicated handler to denote from freerMonad to probState. *)
(*                                                                            *)
(* `c !~ p` = freer_to_prob (c : contract Fx S) A (p : M A)                   *)
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

Section prob_handler.
Context {R : realType} {Fx : effect} `{HF : @FlipEff R -< Fx} {S : UU0}.
Context {N : probDrStateMonad R S}.
Variables (c : contract Fx S) (res : S -> forall X, Fx X -> X).

Definition store_op X (cmd : Fx X) : N X :=
  get >>= fun s =>
    let t := res s cmd in put (state_update c s cmd t) >> Ret t.

Definition prob_handler : Fx ~~> N :=
  fun X cmd => match prj (F := @FlipEff R) cmd with
  | Some f => match f in FlipEff Y return N Y with
              | flipe q => bcoin q
              end
  | None => store_op cmd
  end.

Lemma prob_handler_flip q : prob_handler (inj (flipe q)) = bcoin q.
Proof. by rewrite /prob_handler injK_Some. Qed.

Lemma prob_handler_store X (cmd : Fx X) :
  prj (F := @FlipEff R) cmd = None -> prob_handler cmd = store_op cmd.
Proof. by rewrite /prob_handler=> ->. Qed.

Definition compliant :=
  forall s X (cmd : Fx X), prj (F := @FlipEff R) cmd = None ->
    promise c s cmd (res s cmd).

Lemma prob_handler_unit (cmd : Fx unit) :
  prj (F := @FlipEff R) cmd = None ->
  prob_handler cmd = get >>= fun s => put (state_update c s cmd tt) >> Ret tt.
Proof.
move/prob_handler_store=> ->; rewrite /store_op; bind_ext=> s.
by case: (res s cmd).
Qed.

(** A non-flip command whose promise fixes its result to [f s]. *)
Lemma prob_handler_promise X (cmd : Fx X) (f : S -> X) :
  compliant -> prj (F := @FlipEff R) cmd = None ->
  (forall s r, promise c s cmd r -> r = f s) ->
  prob_handler cmd =
  get >>= fun s => put (state_update c s cmd (f s)) >> Ret (f s).
Proof.
move=> res_ok flip0 promise_f; rewrite prob_handler_store // /store_op.
bind_ext=> s.
have H := res_ok s X cmd flip0.
by have -> := promise_f s _ H.
Qed.

End prob_handler.

Section freer_to_prob.
Context {R : realType} {Fx : effect} `{@FlipEff R -< Fx} {S : UU0}.
Context {M : freerMonad Fx} {N : probDrStateMonad R S}.

Definition freer_to_prob (c : contract Fx S) (res : S -> forall X, Fx X -> X)
    A (p : M A) : N A :=
  denote N (prob_handler c res) A p.
End freer_to_prob.
Arguments freer_to_prob {R Fx _ S M N} c res {A} p.

(* TODO: Enable this when the contracts carry probabilities. *)
(* Notation "c !~ p" := (freer_to_prob c p) (at level 60, no associativity).*)

(** * Probabilistic correctness of a component *)

(** The probabilistic counterpart of [correct_component]: from the state [s0],
    running [compo] through the contract [c], with the results given by
    [res], behaves like the reference protocol [ref_proto], command by
    command. *)
Section prob_correct_component.
Context {R : realType} {Fin Fx : effect} `{HF : @FlipEff R -< Fx}.
Context {S : UU0} {M : freerMonad Fx} {N : probDrStateMonad R S}.

Definition prob_correct_component (compo : component (M := M) Fin Fx)
    (c : contract Fx S) (res : S -> forall X, Fx X -> X) (s0 : S)
    (ref_proto : Fin ~~> N) :=
  forall T (cmd : Fin T),
    put s0 >> freer_to_prob c res (compo T cmd) = put s0 >> ref_proto T cmd.

End prob_correct_component.
