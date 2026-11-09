(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* CLAUDE: new file.  Origin: FreeSpec theories/Core/Semantics.v,
   SemanticsFacts.v, Instrument.v and InstrumentFacts.v (lthms/FreeSpec
   d4e2f3a).  Programs are run with [denote] into monae's state monad instead
   of ExtLib's; contract witnesses are distributions, as in contract.v. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun choice reals.
From infotheo Require Import fsdist.
From monae Require Import preamble hierarchy monad_model monad_transformer.
From FreerDPS Require Import init effect freer contract hoare.

(* CLAUDE: [semantics] quantifies over result types, so it lives one universe
   above them.  Universe polymorphism lets [semprod] (indexed by [eplus]) and
   [run_freer] (which keeps a semantics as the state of a monad) pick
   different universe instances. *)
Local Set Universe Polymorphism.

(** In FreeSpec, there is no particular semantics attached to the primitives
    of an effect.  Once an effect has been defined, we can provide one (or
    more) operational semantics to interpret its primitives. *)

(** * Definition *)

(** An operational [semantics] for the effect [F] is coinductively defined as
    a function which interprets any primitive of [F], and produces both a
    result and the semantics to use for the next primitive.  This is
    necessary to model impurity: the same primitive may or may not return the
    same result when called several times. *)

CoInductive semantics (F : effect) : Type :=
| mk_semantics (f : forall A : Type, F A -> A * semantics F).

Arguments mk_semantics [F] (f).

Declare Scope semantics_scope.
Bind Scope semantics_scope with semantics.
Delimit Scope semantics_scope with semantics.

Definition run_effect {F : effect} {A : UU0} (sem : semantics F)
    (cmd : F A) : A * semantics F :=
  let: mk_semantics f := sem in f A cmd.

Definition eval_effect {F : effect} {A : UU0} (sem : semantics F)
    (cmd : F A) : A :=
  (run_effect sem cmd).1.

Definition exec_effect {F : effect} {A : UU0} (sem : semantics F)
    (cmd : F A) : semantics F :=
  (run_effect sem cmd).2.

Lemma run_effectE {F : effect} {A : UU0} (sem : semantics F) (cmd : F A) :
  run_effect sem cmd = (eval_effect sem cmd, exec_effect sem cmd).
Proof. by rewrite /eval_effect /exec_effect; case: run_effect. Qed.

(** The simplest semantics is the one of [eempty], the empty effect. *)

Definition eempty_semantics : semantics eempty :=
  mk_semantics (fun (A : UU0) (cmd : eempty A) =>
    match cmd return A * semantics eempty with end).

(** We also provide a semantics for the [STORE S] effect. *)

CoFixpoint store {S : UU0} (s : S) : semantics (STORE S) :=
  mk_semantics (fun (A : UU0) (cmd : STORE S A) =>
    match cmd in STORE _ A return A * semantics (STORE S) with
    | Get => (s, store s)
    | Put s' => (tt, store s')
    end).

(** Operational semantics can be composed horizontally with [semprod]. *)

CoFixpoint semprod {F E : effect} (sem_f : semantics F)
    (sem_e : semantics E) : semantics (eplus F E) :=
  mk_semantics (fun (A : UU0) (cmd : eplus F E A) =>
    match cmd with
    | in_left cmd =>
        let: (x, next) := run_effect sem_f cmd in (x, semprod next sem_e)
    | in_right cmd =>
        let: (x, next) := run_effect sem_e cmd in (x, semprod sem_f next)
    end).

Infix "*" := semprod : semantics_scope.

(** * Interpreting Impure Computations *)

(** A semantics turns each primitive into a step of any state monad whose
    state is the semantics itself.  [run_freer] interprets a program [p]
    with a semantics [sem] in monae's model of the state monad, and returns
    both the result of [p] and the semantics to use afterwards.
    [eval_freer] only keeps the result, and [exec_freer] only keeps the next
    semantics. *)

(* CLAUDE: the handlers are written with [get] and [put] from monae's
   [isMonadState] mixin, so that [with_semantics] reuses [effect_to_state]
   in [stateT]; only the runs pick the model [StateMonad.acto]. *)
Definition effect_to_state {F : effect} {M : stateMonad (semantics F)} :
    F ~~> M :=
  fun A cmd => get >>= fun sem : semantics F =>
    let: (x, next) := run_effect sem cmd in put next >> (Ret x : M A).

Section run_freer.
Context {F : effect} {M : freerMonad F}.

Definition run_freer {A : UU0} (sem : semantics F) (p : M A) :
    A * semantics F :=
  denote (StateMonad.acto _) effect_to_state A p sem.

Definition eval_freer {A : UU0} (sem : semantics F) (p : M A) : A :=
  (run_freer sem p).1.

Definition exec_freer {A : UU0} (sem : semantics F) (p : M A) :
    semantics F :=
  (run_freer sem p).2.

Lemma run_freer_ret {A : UU0} (sem : semantics F) (x : A) :
  run_freer sem (Ret x : M A) = (x, sem).
Proof. by rewrite /run_freer denote_ret. Qed.

Lemma run_freer_bind {A B : UU0} (sem : semantics F) (p : M A)
    (f : A -> M B) :
  run_freer sem (p >>= f) =
  let: (x, next) := run_freer sem p in run_freer next (f x).
Proof.
rewrite /run_freer denote_bind state_bindE /= up_compE.
by case: (run_freer sem p).
Qed.

Lemma run_freer_trigger {A : UU0} (sem : semantics F) (cmd : F A) :
  run_freer sem (freer.trigger A cmd : M A) = run_effect sem cmd.
Proof.
rewrite /run_freer denote_trigger /effect_to_state state_bindE up_compE /=.
by case: (run_effect sem cmd).
Qed.

End run_freer.

(** * In-place Primitives Handling *)

(** [with_semantics] locally provides the effect [G] within a program,
    handling its primitives with [sem]; the other primitives are kept.  The
    locally provided effect is the right operand of [eplus], see effect.v. *)

Section with_semantics.
Context {Fx G : effect} {M : freerMonad (eplus Fx G)} {N : freerMonad Fx}.

Definition with_semantics_handler :
    eplus Fx G ~~> stateT (semantics G) N :=
  fun A cmd =>
    match cmd with
    | in_left cmd => liftS (freer.trigger A cmd : N A)
    | in_right cmd => effect_to_state A cmd
    end.

Definition with_semantics {A : UU0} (sem : semantics G) (p : M A) : N A :=
  denote _ with_semantics_handler A p sem >>= fun res => Ret res.1.

End with_semantics.

(** [with_store] locally provides a mutable variable. *)

Definition with_store {Fx : effect} {S : Type}
    {M : freerMonad (eplus Fx (STORE S))} {N : freerMonad Fx} {A : UU0}
    (s : S) (p : M A) : N A :=
  with_semantics (store s) p.

(** * Semantics Compliance *)

(** A semantics [sem] complies with a contract [c] from the witness [d] if it
    computes results which satisfy the promise of [c] for the primitives
    which satisfy the requirement of [c], and if the semantics it produces
    complies with [c] from the updated witness. *)

CoInductive compliant_semantics {R : realType} {Fx F : effect} `{F -<? Fx}
    {S : choiceType} (c : contract R F S) :
    R.-dist S -> semantics Fx -> Prop :=
| compliant_semantics_rec (d : R.-dist S) (sem : semantics Fx)
    (callee : forall (A : Type) (cmd : Fx A),
      gen_requirement c d cmd -> gen_promise c d cmd (eval_effect sem cmd))
    (next : forall (A : Type) (cmd : Fx A),
      gen_requirement c d cmd ->
      compliant_semantics c (gen_state_update c d cmd (eval_effect sem cmd))
        (exec_effect sem cmd)) :
  compliant_semantics c d sem.

Section compliant_semantics_facts.
Context {R : realType} {Fx F : effect} `{F -<? Fx} {S : choiceType}
  (c : contract R F S).

Lemma compliant_semantics_promise (d : R.-dist S) (sem : semantics Fx)
    {A : UU0} (cmd : Fx A) (req : gen_requirement c d cmd) :
  compliant_semantics c d sem -> gen_promise c d cmd (eval_effect sem cmd).
Proof. by move=> comp; case: d sem / comp req => d sem callee _ /callee. Qed.

Lemma compliant_semantics_next (d : R.-dist S) (sem : semantics Fx)
    {A : UU0} (cmd : Fx A) (req : gen_requirement c d cmd) :
  compliant_semantics c d sem ->
  compliant_semantics c (gen_state_update c d cmd (eval_effect sem cmd))
    (exec_effect sem cmd).
Proof. by move=> comp; case: d sem / comp req => d sem _ next /next. Qed.

End compliant_semantics_facts.

Arguments compliant_semantics_promise {R Fx F _ S c d sem A cmd} req comp.
Arguments compliant_semantics_next {R Fx F _ S c d sem A cmd} req comp.

(** Any semantics complies with [no_contract]. *)

Lemma no_contract_compliant_semantics {R : realType} {Fx F : effect}
    `{F -<? Fx} (d : R.-dist unit) (sem : semantics Fx) :
  compliant_semantics (no_contract R F) d sem.
Proof.
move: d sem; cofix no_contract_compliant=> d sem.
constructor=> A cmd _.
  by rewrite /gen_promise; case: prj.
exact: no_contract_compliant.
Qed.

(** Semantics obtained from the [store] function comply with [store_specs]. *)

Lemma store_complies_to_store_specs {R : realType} {S : choiceType} (s : S) :
  compliant_semantics (store_specs R S) (fsdist1 s) (store s).
Proof.
have store_compliant : forall (d : R.-dist S) (s : S), d = fsdist1 s ->
    compliant_semantics (store_specs R S) d (store s).
- cofix store_compliant=> d {}s ->.
  constructor=> A cmd _.
  + by exists s; split=> //; case: cmd.
  + by case: A / cmd=> [|s']; apply: store_compliant;
    rewrite /gen_state_update /= !fsdist1bind.
- exact: store_compliant.
Qed.

(** * Instrumented Runs *)

(** An instrumented run interprets a program with a semantics while
    updating the witness of a contract after each primitive. *)

Section instrument.
Context {R : realType} {Fx F : effect} `{F -<? Fx} {S : choiceType}
  (c : contract R F S).

Definition instrument_effect {N : stateMonad (R.-dist S * semantics Fx)} :
    Fx ~~> N :=
  fun A cmd => get >>= fun '(d, sem) =>
    let: (x, next) := run_effect sem cmd in
    put (gen_state_update c d cmd x, next) >> (Ret x : N A).

Definition run_instrument {M : freerMonad Fx} {A : UU0} (d : R.-dist S)
    (sem : semantics Fx) (p : M A) : A * (R.-dist S * semantics Fx) :=
  denote (StateMonad.acto _) instrument_effect A p (d, sem).

Section inductive_runs.
Context {M : inductiveFreerMonad Fx}.

Lemma run_instrument_trigger_bind {A B : UU0} (d : R.-dist S)
    (sem : semantics Fx) (cmd : Fx A) (k : A -> M B) :
  run_instrument d sem (freer.trigger A cmd >>= k) =
  run_instrument (gen_state_update c d cmd (eval_effect sem cmd))
    (exec_effect sem cmd) (k (eval_effect sem cmd)).
Proof.
rewrite /run_instrument denote_bind denote_trigger state_bindE up_compE /=.
by rewrite /instrument_effect state_bindE up_compE /= run_effectE.
Qed.

(** The instrumentation does not change the result nor the semantics. *)

Lemma run_instrumentE {A : UU0} (d : R.-dist S) (sem : semantics Fx)
    (p : M A) :
  ((run_instrument d sem p).1, (run_instrument d sem p).2.2) =
  run_freer sem p.
Proof.
move: A p d sem; apply: f_ind=> [A x | A B cmd k IHk] d sem.
  by rewrite /run_instrument denote_ret run_freer_ret.
rewrite run_instrument_trigger_bind IHk run_freer_bind run_freer_trigger.
by rewrite run_effectE.
Qed.

Lemma run_instrument_post {A : UU0} (d : R.-dist S) (sem : semantics Fx)
    (p : M A) :
  compliant_semantics c d sem -> pre (c |~ p) d ->
  post (c |~ p) d (run_instrument d sem p).1 (run_instrument d sem p).2.1.
Proof.
move: A p d sem; apply: f_ind=> [A x | A B cmd k IHk] d sem comp.
  by rewrite pre_ret post_ret /run_instrument denote_ret.
rewrite run_instrument_trigger_bind freer_to_hoare_bindE to_hoare_triggerE.
move=> [req pre_k] /=.
exists (eval_effect sem cmd), (gen_state_update c d cmd (eval_effect sem cmd)).
have promise_x := compliant_semantics_promise req comp.
split=> //.
apply: IHk; first exact: compliant_semantics_next.
exact: pre_k.
Qed.

Lemma run_instrument_compliant {A : UU0} (d : R.-dist S)
    (sem : semantics Fx) (p : M A) :
  compliant_semantics c d sem -> pre (c |~ p) d ->
  compliant_semantics c (run_instrument d sem p).2.1
    (run_instrument d sem p).2.2.
Proof.
move: A p d sem; apply: f_ind=> [A x | A B cmd k IHk] d sem comp.
  by rewrite /run_instrument denote_ret.
rewrite run_instrument_trigger_bind freer_to_hoare_bindE to_hoare_triggerE.
move=> [req pre_k].
apply: IHk; first exact: compliant_semantics_next.
apply: pre_k; split=> //.
exact: compliant_semantics_promise.
Qed.

End inductive_runs.

End instrument.
