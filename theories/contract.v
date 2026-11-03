(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In this library, we provide the necessary material to reason about FreeSpec
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on effs, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From mathcomp Require Import ssreflect ssrfun choice.
From FreerDPS Require Import init effect freer mathcomp_extra.
From HB Require Import structures.

From mathcomp Require Import reals.
From infotheo Require Import fsdist realType_ext.

Local Open Scope signature_scope.
Local Open Scope fsdist_scope.

(** * Definition *)

(** A contract dedicated to [F : effect] primarily provides two
    predicates.

    - [caller_obligation] distinguishes between primitives that can be used (by
      an impure computation), and primitives that cannot be used.
    - [callee_obligation] specifies which guarantees can be expected from
      primitives results, as computed by a “good” operational semantics.

    Both [caller_obligation] and [callee_obligation] model properties that may
    vary in time, e.g., a primitive may be forbidden at a given time, but
    authorized later.  To take this possibility into account, contracts are
    parameterized by what we have called a “witness.”  A witness is a term which
    describes the necessary information of the past, and allows for taking
    decision for the present.  It can be seen as an abstraction of the concrete
    state of the effect implementor.

    To keep this state up-to-date after each primitive interpretation,
    contracts also define a dedicated function [state_update]. *)
Declare Scope contract_scope.

Record contract (R : realType) (F : effect) (S : choiceType) : Type :=
  make_contract {
    state_update : S -> forall U : Type, F U -> U -> R.-dist S ;
    requirement : R.-dist S -> forall U : Type, F U -> Prop ;
    promise : R.-dist S -> forall U : Type, F U -> U -> Prop }.

Arguments make_contract [R F S] (_ _ _).
Arguments state_update [R F S] (c _) [U] (_ _).
Arguments requirement [R F S] (c _) [U] (_).
Arguments promise [R F S] (c _) [U] (_ _).

Bind Scope contract_scope with contract.

Definition make_det_contract {R : realType} [F] [S : choiceType]
    (su : S -> forall U : Type, F U -> U -> S)
    (re : S -> forall U : Type, F U -> Prop)
    (pr : S -> forall U : Type, F U -> U -> Prop)
  : contract R F S :=
  make_contract
    (fun d U cmd x => fsdist1 d >>= fun s => fsdist1 (su s U cmd x))
    (fun d U cmd => exists s, d = fsdist1 s /\ re s U cmd)
    (fun d U cmd x => exists s, d = fsdist1 s /\ pr s U cmd x).

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given effect, and for the operational semantics which compute results for
    these primitives. *)
Definition const_witness {F : effect} :=
  fun (u : unit) (T : Type) (cmd : F T) (t : T) => u.

Definition no_requirement {F : effect} {S : Type}
    (s : S) (T : Type) (cmd : F T) : Prop :=
  True.

Definition no_promise {F : effect} {S : Type}
    (s : S) (T : Type) (cmd : F T) (t : T) : Prop :=
  True.

Definition no_contract (R : realType) (F : effect) : contract R F unit :=
  make_contract (fun d _ _ _ => fsdist1 d) no_requirement no_promise.

(** A similar —and as simple— contract is the one that forbids the use of a
    given effect. *)
Definition do_no_use {F : effect} {S : Type}
    (s : S) (T : Type) (cmd : F T) : Prop :=
  False.


Definition forbid_specs (R : realType) (F : effect) : contract R F unit :=
  {|
    state_update := fun d _ _ _ => fsdist1 d
   ; requirement := do_no_use
   ; promise := no_promise
   |}.

(** * Composing Contracts *)

(** As we compose effs and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [F] and
    [E] two effs, if we can reason about [F] and [E] independently (e.g., the
    caller obligations of [E] do not vary when we use [F]), then we can compose
    [ci : contract F ΩF] and [cj : contract E ΩE], such that
    [contractprod ci cj] in a contract for [F + E]. *)

Definition gen_state_update {R : realType} {Fx F : effect} `{F -<? Fx}
    {S : choiceType} {T : Type} (c : contract R F S)
    (s : R.-dist S) (cmd : Fx T) (t : T)
  : R.-dist S :=
  if prj cmd is Some cmd then fsdistbind s (fun ss=> state_update c ss cmd t) else s.
Arguments gen_state_update : simpl never.

Definition gen_requirement {R : realType} [Fx F] `{F -<? Fx}
    {S : choiceType} {T : Type} (c : contract R F S)
    (s : R.-dist S) (cmd : Fx T)
  : Prop :=
  if prj cmd is Some cmd then requirement c s cmd else True.

Definition gen_promise {R : realType} [Fx F] `{F -<? Fx}
    {S : choiceType} {T : Type} (c : contract R F S)
    (s : R.-dist S) (cmd : Fx T) (t : T)
  : Prop :=
  if prj cmd is Some cmd then promise c s cmd t else True.

Definition dist_pair {R : realType} {A B : choiceType}
    (p : R.-dist A) (q : R.-dist B) : R.-dist (A * B) :=
  fsdistbind p (fun a =>
    fsdistmap (A:=B) (B:=(A * B)) (fun b => (a, b)) q).

Lemma dist_pair1 {R : realType} {A B : choiceType} (a : A) (b : B) :
  dist_pair (fsdist1 a) (fsdist1 b) = fsdist1 (a, b) :> R.-dist (A * B).
Proof. by rewrite /dist_pair fsdist1bind fsdistmap1. Qed.

(* CLAUDE: revived (was commented out with "TODO: Check if this works properly
   with an example").  Fix: [state_update] receives a plain state [s], so each
   component is updated from the point mass of its projection; requirement and
   promise read the marginals of the distribution. *)
Definition contractprod {R : realType} {Fx F E : effect} `{F -< Fx, E -< Fx}
    {ΩF ΩE : choiceType}
    (ci : contract R F ΩF) (cj : contract R E ΩE)
  : contract R Fx (ΩF * ΩE) :=
  {| state_update := fun s (T : Type) (cmd : Fx T) (t : T) =>
       dist_pair (gen_state_update ci (fsdist1 s.1) cmd t)
                 (gen_state_update cj (fsdist1 s.2) cmd t)
  ;  requirement := fun d (T : Type) (cmd : Fx T) =>
       gen_requirement ci (fsdistmap fst d) cmd /\
       gen_requirement cj (fsdistmap snd d) cmd
  ;  promise := fun d (T : Type) (cmd : Fx T) (t : T) =>
       gen_promise ci (fsdistmap fst d) cmd t /\
       gen_promise cj (fsdistmap snd d) cmd t
  |}.

Infix "-*-" := contractprod (at level 20) : contract_scope.

Section contractprod_point_mass.
Context {R : realType} {Fx F E : effect} `{F -< Fx, E -< Fx}
    {ΩF ΩE : choiceType} (ci : contract R F ΩF) (cj : contract R E ΩE)
    (x : ΩF) (y : ΩE) {T : Type} (cmd : Fx T).

Lemma contractprod_requirement1 :
  requirement (ci -*- cj) (fsdist1 (x, y)) cmd <->
  gen_requirement ci (fsdist1 x) cmd /\ gen_requirement cj (fsdist1 y) cmd.
Proof. by rewrite /= !fsdistmap1. Qed.

Lemma contractprod_promise1 (t : T) :
  promise (ci -*- cj) (fsdist1 (x, y)) cmd t <->
  gen_promise ci (fsdist1 x) cmd t /\ gen_promise cj (fsdist1 y) cmd t.
Proof. by rewrite /= !fsdistmap1. Qed.

End contractprod_point_mass.

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)
Definition sharedcontractprod {R : realType} {Fx F E : effect}
    `{F ;; E -<< Fx}
    {S : choiceType} (ci : contract R F S) (cj : contract R E S)
  : contract R Fx S := {|
  state_update :=
    fun (s : S) (T : Type) (cmd : Fx T) (t : T) =>
      (* we need to check [F] before [E] because [sharedcontractprod]
         will be right associative *)
      match prj (F:=F) cmd with
      | Some cmd => state_update ci s cmd t
      | _ => if prj (F:=E) cmd is Some cmd then state_update cj s cmd t else fsdist1 s
      end;
  requirement :=
    fun (s : R.-dist S) (T : Type) (cmd : Fx T) =>
      gen_requirement ci s cmd /\ gen_requirement cj s cmd;
  promise :=
    fun (s : R.-dist S) (T : Type) (cmd : Fx T) (t : T) =>
      gen_promise ci s cmd t /\ gen_promise cj s cmd t
  |}.

Infix "-^-" := sharedcontractprod (at level 20, right associativity) :
    contract_scope.
(** * Contract By Example *)

(** Finally, and as an example, we define a contract for the effect
    [STORE s] we discuss in [FreerDPS.Freer].

    For [STORE s], the best witness is the actual value of the mutable
    variable.  Therefore, the contract for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (S : Type) :=
  fun (s : S) (T : Type) (cmd : STORE S T) (_ : T) =>
    match cmd with
    | Get => s
    | Put s' => s'
    end.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly equivalent to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Definition o_callee_store (S : Type) (x : S) :
    forall T, STORE S T -> T -> Prop :=
  fun T cmd =>
    match cmd in STORE _ T return T -> Prop with
    | Get => fun x' => x = x'
    | Put _ => fun _ => True
    end.

(** The actual contract can therefore be defined as follows: *)

Definition store_specs (R : realType) (S : choiceType)
  : contract R (STORE S) S :=
  make_det_contract (store_update S) no_requirement (o_callee_store S).

(** Now, as we briefly mentionned, this contract allows for reasoning about an
    impure computation which uses the [STORE s] effect, assuming the mutable,
    global variable has been initialized.  We can define another contract that
    does not rely on such assumption, and on the contrary, requires an impure
    computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [promise] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefits of the FreeSpec approach: because the
    contracts are defined independently from impure computations and
    effs, we can actually define several contracts to consider
    different set of hypotheses. *)


Section contract_helpers.
Context {R : realType} {Fx F : effect} `{F -< Fx} {S : choiceType}
    {X Y : Type} (c : contract R F S)  (cmd : F X) (s s' : R.-dist S)
    (cmd' : F Y) (x : X) (concl : Prop).

Local Abbreviation inj := (inj (Fx:=Fx)).

Lemma provided_callerP :
  gen_requirement c s (inj cmd)
  <-> requirement c s cmd.
Proof.
by rewrite /gen_requirement !injK_Some.
Qed.

Lemma provided_calleeP  :
  (s' = gen_state_update c s (inj cmd) x /\ gen_promise c s (inj cmd) x )
  <-> (s' = fsdistbind s (fun ss=> state_update c ss cmd x) /\ promise c s cmd x) .
Proof.
by split; rewrite /gen_promise /gen_state_update !injK_Some.
Qed.

End contract_helpers.

Section contract_distinguish_helpers.
Context {Fx F G : effect} `{F -<? Fx} `{G -< Fx}
    `{Distinguish Fx G F}
    {R : realType} {S : choiceType} {X : Type} (c : contract R F S)
    (cmd : G X) (x : X).

Local Abbreviation inj := (inj (Fx:=Fx)).

Lemma distinguished_caller (s : R.-dist S) :
  gen_requirement c s (inj cmd).
Proof.
by rewrite /gen_requirement injK_None.
Qed.

Lemma distinguished_callee (s s' : R.-dist S):
  (s' = gen_state_update c s (inj cmd) x /\ gen_promise c s (inj cmd) x)
  <-> s = s'.
Proof.
rewrite /gen_state_update /gen_promise injK_None.
by split=> [[-> _] | ->].
Qed.
End contract_distinguish_helpers.
