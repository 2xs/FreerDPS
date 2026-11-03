(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import boot classical_sets boolp.
From monae Require Import hierarchy.
From FreerDPS Require Import all_freerdps.

From mathcomp Require Import ssreflect ssrfun reals Rstruct.
From infotheo Require Import fsdist.

Local Abbreviation R := Rdefinitions.R.
(* DOORS == TODO *)


Module Export DoorsControllerM.
(** ** Doors *)

Inductive door : Type := left | right.
Implicit Type d : door.

HB.instance Definition _ := gen_eqMixin door.

Inductive DOORS : effect :=
| CheckOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Section doors_s.
Context {Fx : effect} `{DOORS -< Fx} {M : freerMonad Fx}.

Definition is_open d : M bool := ptrigger $ CheckOpen d.
Definition toggle d : M unit := ptrigger $ Toggle d.
Definition open_door d : M unit :=
  is_open d >>= fun b => when (~~ b) (toggle d).
Definition close_door d : M unit :=
  is_open d >>= fun b => when b (toggle d).
End doors_s.

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| PressButton d : CONTROLLER unit.

Definition opposite_door d : door :=
  match d with
  | left => right
  | right => left
  end.

Definition controller {Fx : effect} `{DOORS -< Fx, STORE nat -< Fx}
    {M : freerMonad Fx} : component (M := M) CONTROLLER Fx :=
  fun _ cmd =>
    match cmd with
    | Tick =>
      iget >>= fun cpt =>
      when (15 < cpt)%N $
        close_door left >>
        close_door right >>
        iput 0%nat
    | PressButton d =>
      close_door (opposite_door d) >>
      open_door d >>
      iput 0%nat
    end.
End DoorsControllerM.

(** * Verifying the Airlock Controller *)

Definition open := true.
Definition closed := false.

Definition state : Type := bool * bool.

Definition door_state d : state -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition toggle d (s : state) : state :=
  match d with
  | left => (~~ s.1, s.2)
  | right => (s.1, ~~ s.2)
  end.

Lemma tog_equ_1 d (s : state) :
  door_state d (toggle d s) = ~~ door_state d s.
Proof. by case: d. Qed.

Lemma tog_equ_2 d (s : state) :
  door_state (opposite_door d) (toggle d s) = door_state (opposite_door d) s.
Proof. by case: d. Qed.

Opaque toggle.

(* -------------------------------------------------------------------------- *)

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

Section contract.
Implicit Types s : state.

Definition doors_witness_update s (U : Type) (c : DOORS U) : state :=
  if c is Toggle d then toggle d s else s.

Definition doors_requirement s : forall U, DOORS U -> Prop :=
  fun _ cmd =>
    match cmd with
    | CheckOpen _ => True
    | Toggle d => door_state (opposite_door d) s -> door_state d s
    end.
(*
doors_requirement does not hold when we toggle a door d
which is closed while the opposite door is open;
observe that doors_o_caller can be true if the opposite door is
open while we try to close the other open door (though this
situation is of course not supposed to happen)
*)

(*
true true   true
true false  false
false false true
false true  true
*)

Definition doors_promise s : forall U, DOORS U -> U -> Prop :=
  fun U cmd =>
    match cmd with
    | CheckOpen d => fun b => door_state d s = b
    | Toggle _ => fun _ => True
    end.

(*
relation between a command c and a state u;
it is false only when the state of a door that we check is not u
*)

Definition doors_c : contract R DOORS state :=
  make_det_contract
   (fun s U cmd _ => doors_witness_update s U cmd)
   doors_requirement
   doors_promise.

End contract.

Local Open Scope classical_set_scope.

Remark one_door_safe_all_doors_safe (s : state) d
    (safe : (~~ door_state d s) || (~~ door_state (opposite_door d) s)) :
  forall d',(~~ door_state d' s) || (~~ door_state (opposite_door d') s).
Proof.
by move=> d'; move: d d' safe => [|] [|]//=; rewrite orbC.
Qed.

Definition not_both_open s :=
  (~~ door_state left s) || (~~ door_state right s).

Section RespectfulAndRunLemmas.
Context {Fx : effect} `{DOORS -< Fx} {M : freerMonad Fx}.

(** Closing a door [d] in any system [s] is always a respectful operation. *)
Lemma close_door_respectful d (s : state) :
  pre (doors_c |~ (close_door d : M _)) (fsdist1 s).
Proof.
rewrite /close_door freer_to_hoare_bindE/=; split.
  by rewrite pre_trigger1P.
case=> w'; rewrite pre_to_hoare_whenP // post_trigger1P /=.
by case=> -> door_open; rewrite pre_trigger1P /= door_open.
Qed.

Lemma open_door_respectful (s : state) d
    (safe : ~~ door_state (opposite_door d) s) :
  pre (doors_c |~ (open_door d : M _)) (fsdist1 s).
Proof.
rewrite /open_door freer_to_hoare_bindE; split.
  by rewrite pre_trigger1P.
case=> w'; rewrite pre_to_hoare_whenP // post_trigger1P /=.
case=> -> door_closed; rewrite pre_trigger1P /= door_closed.
by move: safe=> /= /negPf ->.
Qed.

Lemma close_door_run (s : state) d (s' : R.-dist state) (x : unit)
    (run : post (doors_c |~ (close_door d : M _)) (fsdist1 s) x s') :
  dist_inv (fun t=>~~ door_state d t) s'.
Proof.
move: run; rewrite /close_door freer_to_hoare_bindE.
move=> [opened [w] []].
rewrite post_to_hoare_whenP post_trigger1P /= => -[->].
case: opened=> /= [door_open [[]] | /[swap] -> door_closed]; last first.
  by exists s; rewrite door_closed.
rewrite post_trigger1P /= => -[-> _].
by exists (toggle d s); rewrite tog_equ_1 door_open.
Qed.

Opaque close_door.
Opaque open_door.
Opaque Nat.ltb.
Opaque door_state.

Lemma doors_trigger_preserves_safe
    {a : Type} (cmd : Fx a) (s : R.-dist state) (x : a)
    (s' : R.-dist state) :
  pre (doors_c |~ (ptrigger cmd : M _)) s ->
  post (doors_c |~ (ptrigger cmd : M _)) s x s' ->
  dist_inv not_both_open s -> dist_inv not_both_open s'.
Proof.
move=> pre_s post_s [t [sE safe]]; move: pre_s post_s; rewrite sE.
rewrite to_hoare_triggerE /=.
rewrite /gen_requirement /gen_state_update /gen_promise.
case: prj=> [door_op |_ [-> _]]; last by exists t.
rewrite /= fsdist1bind.
move: door_op x; case=> d /= [] [s0 [/fsdist1_inj ts0 caller]] [-> _];
  try by exists t.
all: rewrite fsdist1bind /= dist_inv1P //.
apply: (one_door_safe_all_doors_safe (toggle d t) d).
move: caller; rewrite -ts0.
rewrite tog_equ_1 tog_equ_2 negbK.
by case: (door_state d t); case: (door_state (opposite_door d) t)
  => //= /(_ isT).
Qed.

Lemma doors_handler_preserves_safe {a : Type} (cmd : Fx a) :
  preserves_invariant (dist_inv not_both_open) (hoare_of_contract doors_c cmd).
Proof.
move=> witness result witness' hpre hpost.
apply: doors_trigger_preserves_safe;
  rewrite to_hoare_triggerE.
- exact: hpre.
- exact: hpost.
Qed.

End RespectfulAndRunLemmas.

(* From now on, proofs will use the inductive version. *)
Section InvariantRunLemmas.
Context {Fx : effect} `{DOORS -< Fx} {M : inductiveFreerMonad Fx}.

(** /!\ WARNING: This lemma is the only one needing `f_ind` because we
  * require to "execute" the freer program in order to denote it and see
  * if the invariant was preserved all along.
  *)
Lemma doors_run_preserves_safe {A : Type} (p : M A) :
  preserves_invariant (dist_inv not_both_open) (doors_c |~ p).
Proof.
by apply: to_hoare_preserves_invariant=> *;
  exact: (doors_handler_preserves_safe (M := M)).
Qed.

Lemma respectful_run_inv {A : Type} (p : M A)
    (s : R.-dist state) (safe : dist_inv not_both_open s)
    (a : A) (s' : R.-dist state)
    (hpre : pre (doors_c |~ p) s)
    (hpost : post (doors_c |~ p) s a s') :
  dist_inv not_both_open s'.
Proof. by move: hpre hpost safe; exact: doors_run_preserves_safe. Qed.
End InvariantRunLemmas.

(** ** Main Theorem *)
Section controller_s.
Context {Fx : effect} `{DOORS ;; (STORE nat) -<< Fx}
  {M : inductiveFreerMonad Fx}.

Lemma controller_pre {A : Type} (cmd : CONTROLLER A) (s : state) :
  pre (doors_c |~ controller (M := M) A cmd) (fsdist1 s).
Proof.
case: cmd => [| d].
- rewrite freer_to_hoare_bindE; split =>[|cpt w].
  + rewrite to_hoare_triggerE.
    exact: distinguished_caller.
  + rewrite to_hoare_triggerE.
    move/distinguished_callee=> <-.
    rewrite pre_to_hoare_whenP.
    case: (15 < cpt)%N => //=.
    rewrite freer_to_hoare_bindE; split => [|*].
    * rewrite freer_to_hoare_bindE; split=> [|? ? /close_door_run[t [-> _]]].
        exact: close_door_respectful.
      exact: close_door_respectful.
    * rewrite to_hoare_triggerE => x ?.
      by apply: distinguished_caller.
- rewrite freer_to_hoare_bindE; split => [|*].
  + rewrite freer_to_hoare_bindE; split => [|? ? /close_door_run[t [-> ?]]].
      exact: close_door_respectful.
    exact: open_door_respectful.
  + rewrite to_hoare_triggerE => x ?.
    exact: distinguished_caller.
Qed.

Theorem controller_correct :
  correct_component controller (M := M)
    (no_contract R CONTROLLER) doors_c (fun=> dist_inv not_both_open).
Proof.
move=> ? sout safe ? cmd _; split=> [| ? ? hpost].
  by case: safe=> s [-> _]; exact: controller_pre.
split=> //.
have [s [sE _]] := safe.
have hpre := controller_pre cmd s; move: hpre hpost; rewrite -sE.
exact: respectful_run_inv.
Qed.

End controller_s.
