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
From monae Require Import monad_model.
From infotheo Require Import fsdist realType_ext.

#[local]
Open Scope signature_scope.
Open Scope fsdist_scope.
Open Scope monae_scope.

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
Section tmp.
Context (R: realType).
Record contract (F : effect) (T: Type) : Type := make_contract {
    state_update : T -> forall U : Type, F U -> U -> fsdist R (monad_model.choice_of_Type T);
    requirement : T -> forall U : Type, F U -> Prop ;
    promise : T -> forall U : Type, F U -> U -> Prop }.


Arguments make_contract [F T] (_ _ _).
Arguments state_update [F T] (c _) [U] (_ _).
Arguments requirement [F T] (c _) [U] (_).
Arguments promise [F T] (c _) [U] (_ _).

(* Definition c_dist (R: realType) (T: Type) := fsdist R (monad_model.choice_of_Type T). *)
Definition dist X := (@fsdist R (monad_model.choice_of_Type X)).
Definition pure1 {S : Type} (s : S) : dist S:=
  @fsdist1 R (monad_model.choice_of_Type S) s.
(* Abbreviation prob_contract R := (contractG (c_dist R)). *)
(* Abbreviation prob_mk_contract R := (make_contractG (c_dist R) pure_c_dist). *)
(*  *)
(* Definition id_dist := @idfun Type. *)
(* Definition purei {S : Type} (s : S) : *)
    (* id_dist S := s. *)
(* Abbreviation contract := (contractG (id_dist)). *)
(* Abbreviation make_contract := (make_contractG (dist:=id_dist) purei). *)

Bind Scope contract_scope with contract.

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given effect, and for the operational semantics which compute results for
    these primitives. *)

Definition make_contract' [F T]
(su : T -> forall U : Type, F U -> U -> T)
(re: T -> forall U : Type, F U -> Prop )
(pr : T -> forall U : Type, F U -> U -> Prop)
     : contract F T := make_contract (fun t U fu u => pure1 (su t U fu u)) re pr .
Definition const_witness {F : effect} :=
  fun (u : unit) (T : Type) (cmd : F T) (t : T) => u.

Definition no_requirement {F : effect} {S : Type}
    (s : S) (T : Type) (cmd : F T) : Prop :=
  True.

Definition no_promise {F : effect} {S : Type}
    (s : S) (T : Type) (cmd : F T) (t : T) : Prop :=
  True.

Definition no_contract (F : effect) : contract F unit :=
  make_contract' const_witness no_requirement no_promise.

(** A similar —and as simple— contract is the one that forbids the use of a
    given effect. *)

Definition do_no_use {F : effect} {S : Type}
    (s : S) (T : Type) (cmd : F T) : Prop :=
  False.


Definition forbid_specs (F : effect) : contract F unit :=
  {|
    state_update := (fun t U fu u => pure1 (const_witness t U fu u))
   ; requirement := do_no_use
   ; promise := no_promise
   |}.

(** * Composing Contracts *)

(** As we compose effs and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [F] and [E]
    two effs, if we can reason about [F] and [E] independently (e.g., the
    caller obligations of [E] do not vary when we use [F]), then we can compose
    [ci : contract F ΩF] and [cj : contract E ΩE], such that [contractprod ci cj] in a
    contract for [F + E]. *)

Definition gen_state_update {Fx F : effect} `{F -<? Fx}
    {S T : Type} (c : contract F S)
    (s : S) (cmd : Fx T) (t : T)
  : dist S :=
  if prj cmd is Some cmd then state_update c s cmd t else pure1 s.
Arguments gen_state_update : simpl never.

Definition gen_requirement {Fx F : effect} `{F -<? Fx}
    {S T : Type} (c : contract F S)
    (s :  S) (cmd : Fx T)
  : Prop :=
  if prj cmd is Some cmd then requirement c s cmd else True.

Definition gen_promise {Fx F : effect} `{F -<? Fx}
    {S T : Type} (c : contract F S)
    (s :  S) (cmd : Fx T) (t : T)
  : Prop :=
  if prj cmd is Some cmd then promise c s cmd t else True.

Definition dist_pair {A B : Type} (p : dist A) (q : dist B) :
    dist (A * B) :=
  fsdistbind p (fun a =>
    fsdistmap (A:=monad_model.choice_of_Type B)
      (B:=monad_model.choice_of_Type (A * B)) (fun b => (a, b)) q).

Definition contractprod {Fx F E : effect} `{F -< Fx, E -< Fx}
    {ΩF ΩE : Type}
    (ci : contract F ΩF) (cj : contract E ΩE)
  : contract Fx (ΩF * ΩE) :=
  {| state_update := fun (s : ΩF * ΩE) (T : Type) (cmd : Fx T) (t : T) =>
                    dist_pair
                         (gen_state_update ci (fst s) cmd t)
                          (gen_state_update cj (snd s) cmd t)
  ;  requirement := fun (s : ΩF * ΩE) (T : Type) (cmd : Fx T) =>
                       gen_requirement ci (fst s) cmd /\
                       gen_requirement cj (snd s) cmd
  ;  promise := fun (s : ΩF * ΩE) (T : Type) (cmd : Fx T) (t : T) =>
                   gen_promise ci (fst s) cmd t /\ gen_promise cj (snd s) cmd t
  |}.

Infix "-*-" := contractprod (at level 20) : contract_scope .

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)
Definition sharedcontractprod {Fx F E : effect} `{F ;; E -<< Fx}
    {S : Type} (ci : contract F S) (cj : contract E S)
  : contract Fx S :=
  {|
  state_update :=
    fun (s : S) (T : Type) (cmd : Fx T) (t : T) =>
      (* we need to check [F] before [E] because [sharedcontractprod]
         will be right associative *)
      match prj (F:=F) cmd with
      | Some cmd => state_update ci s cmd t
      | _ => if prj (F:=E) cmd is Some cmd then state_update cj s cmd t else pure1 s
      end;
  requirement :=
    fun (s : S) (T : Type) (cmd : Fx T) =>
      gen_requirement ci s cmd /\ gen_requirement cj s cmd;
  promise :=
    fun (s : S) (T : Type) (cmd : Fx T) (t : T) =>
      gen_promise ci s cmd t /\ gen_promise cj s cmd t
  |}.

Infix "-^-" := sharedcontractprod (at level 20, right associativity) : contract_scope.
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

Definition store_specs (S : Type) : contract (STORE S) S := make_contract'
  (store_update S) no_requirement (o_callee_store S).

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
Context {Fx F : effect} `{F -< Fx} {S X Y : Type}
    (c : contract F S) (s : S) (s' : dist S) (cmd : F X) (cmd' : F Y)
    (x : X) (concl : Prop).

Local Abbreviation inj := (inj (Fx:=Fx)).

Lemma provided_callerP :
  gen_requirement c s (inj cmd)
  <-> requirement c s cmd.
Proof.
by rewrite /gen_requirement !injK_Some.
Qed.

Lemma provided_calleeP :
  (s' = gen_state_update c s (inj cmd) x /\ gen_promise c s (inj cmd) x )
  <-> (s' = state_update c s cmd x /\ promise c s cmd x) .
Proof.
by split; rewrite /gen_promise /gen_state_update !injK_Some.
Qed.

End contract_helpers.

Section contract_distinguish_helpers.
Context {Fx F G : effect} `{F -<? Fx} `{G -< Fx}
    `{Distinguish Fx G F}
    {S X : Type} (c : contract F S) (s : S) (s' : dist S) (cmd : G X) (x : X).

Local Abbreviation inj := (inj (Fx:=Fx)).

Lemma distinguished_caller :
  gen_requirement c s (inj cmd).
Proof.
by rewrite /gen_requirement injK_None.
Qed.

Lemma distinguished_callee :
  (s' = gen_state_update c s (inj cmd) x /\ gen_promise c s (inj cmd) x)
  <-> s' = pure1 s.
Proof.
rewrite /gen_state_update /gen_promise injK_None.
by split=> [[-> _] | ->].
Qed.
End contract_distinguish_helpers.
End tmp.

Bind Scope contract_scope with contract.

Arguments make_contract [R F T] (_ _ _).
Arguments state_update [R F T] (c _) [U] (_ _).
Arguments requirement [R F T] (c _) [U] (_).
Arguments promise [R F T] (c _) [U] (_ _).
Arguments contractprod [R Fx F E H H0 _ _] (_ _).
Arguments sharedcontractprod [R Fx F E H _] (_ _).
Arguments dist [R] (_).
Infix "-*-" := contractprod (at level 20) : contract_scope .
Infix "-^-" := sharedcontractprod (at level 20, right associativity) : contract_scope.
