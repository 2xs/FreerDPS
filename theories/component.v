(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)


(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import init effect freer contract hoare semantics.
From monae Require Import hierarchy.
From mathcomp Require Import ssreflect ssrfun reals choice classical_sets.
From infotheo Require Import fsdist realType_ext.

(** * Definition *)

(** In FreeSpec, a _component_ is an entity which exposes an effect [F],
    and uses primitives of an effect [E] to compute the results of primitives
    of [F].  Besides, a component is likely to carry its own internal state (of
    type [s]).

<<
                           F +-------------------+      E
                           | |                   |      |
                   +------>| | c : component F E |----->|
                           | |                   |      |
                             +-------------------+
>>

    Thus, a component [c : component F E] is a polymorphic function which
    maps primitives of [F] to impure computations using [E]. *)

Definition component (Fin Fout : effect) `{M : freerMonad Fout} : Type :=
  Fin ~~> M.

Definition correct_component {R : realType} {Fx Fin Fout : effect}
    `{Fout -<? Fx} {M : freerMonad Fx} {Sin Sout : choiceType}
    (compo : component Fin Fx) (cin : contract R Fin Sin)
    (cout : contract R Fout Sout)
    (rel_inv : R.-dist Sin -> R.-dist Sout -> Prop) :
  Prop :=
  forall (sin : R.-dist Sin) (sout : R.-dist Sout) (init : rel_inv sin sout)
      (T : Type) (cmd : Fin T) (req : requirement cin sin cmd),
    pre (cout |~ compo T cmd) sout /\
    forall (t : T) (sout' : R.-dist Sout),
      post (cout |~ (compo T cmd : M _)) sout t sout' ->
      promise cin sin cmd t /\
        rel_inv (fsdistbind sin (fun s=>state_update cin s cmd t)) sout'.

(* This should probably go in some other file and have a different name*)
Definition dist_inv {R : realType} {S : choiceType} (P : set S)
    (d : R.-dist S) : Prop :=
  exists s, d = fsdist1 s /\ P s.

Lemma dist_inv1P {R : realType} {S : choiceType} (P : set S) (s : S) :
  dist_inv P (fsdist1 s : R.-dist S) <-> P s.
Proof.
split=> [[s' [/fsdist1_inj <- //]] | P_s].
by exists s.
Qed.

(** * Semantics Derivation *)

(* CLAUDE: new.  Origin: FreeSpec theories/Core/Component.v
   ([derive_semantics], [bootstrap], [with_component]) and ComponentFacts.v
   ([correct_component_derives_compliant_semantics]).  [derive_semantics] is
   the definition FreeSpec calls [derive_semantics'] in ComponentFacts.v: one
   step unfolds by computation, so FreeSpec's setoid on semantics is not
   needed. *)

(** Given a semantics for [Fout], we derive from a component
    [c : component Fin Fout] an operational semantics for [Fin]: each
    primitive of [Fin] is interpreted by running its implementation in [c].
    [derive_semantics] composes components vertically, and [semprod]
    composes semantics horizontally. *)

CoFixpoint derive_semantics {Fin Fout : effect} {M : freerMonad Fout}
    (c : component (M := M) Fin Fout) (sem : semantics Fout) :
    semantics Fin :=
  mk_semantics (fun A cmd =>
    (eval_freer sem (c A cmd), derive_semantics c (exec_freer sem (c A cmd)))).

Section derive_semantics_facts.
Context {Fin Fout : effect} {M : freerMonad Fout}
  (c : component (M := M) Fin Fout) (sem : semantics Fout).

Lemma eval_derive_semantics {A : UU0} (cmd : Fin A) :
  eval_effect (derive_semantics c sem) cmd = eval_freer sem (c A cmd).
Proof. by []. Qed.

Lemma exec_derive_semantics {A : UU0} (cmd : Fin A) :
  exec_effect (derive_semantics c sem) cmd =
  derive_semantics c (exec_freer sem (c A cmd)).
Proof. by []. Qed.

End derive_semantics_facts.

(** A component which uses no effect is enough to build a semantics. *)

Definition bootstrap {Fin : effect} {M : freerMonad eempty}
    (c : component (M := M) Fin eempty) : semantics Fin :=
  derive_semantics c eempty_semantics.

(** * In-place Primitives Handling *)

(** [with_component] locally provides the effect [G] within a program, its
    primitives being handled by the component [c].  [init] runs before the
    program and [final] after it. *)

Section with_component.
Context {Fx G : effect} {M : freerMonad (eplus Fx G)} {N : freerMonad Fx}.

Definition with_component_handler (c : component (M := N) G Fx) :
    eplus Fx G ~~> N :=
  fun A cmd =>
    match cmd with
    | in_left cmd => freer.trigger A cmd
    | in_right cmd => c A cmd
    end.

Definition with_component {A : UU0} (init : N unit)
    (c : component (M := N) G Fx) (final : N unit) (p : M A) : N A :=
  init >> (denote _ (with_component_handler c) A p >>= fun res =>
    final >> Ret res).

End with_component.

(** * Compositional Correctness *)

(** If [compo] is correct with respect to [cin] and [cout], with [rel_inv]
    relating their witnesses, then the semantics derived from [compo] and a
    semantics complying with [cout] complies with [cin]. *)

Lemma correct_component_derives_compliant_semantics {R : realType}
    {Fx Fin Fout : effect} `{Fout -<? Fx} {M : inductiveFreerMonad Fx}
    {Sin Sout : choiceType} (compo : component (M := M) Fin Fx)
    (cin : contract R Fin Sin) (cout : contract R Fout Sout)
    (rel_inv : R.-dist Sin -> R.-dist Sout -> Prop)
    (correct : correct_component compo cin cout rel_inv)
    (sin : R.-dist Sin) (sout : R.-dist Sout) (init : rel_inv sin sout)
    (sem : semantics Fx) (comp : compliant_semantics cout sout sem) :
  compliant_semantics cin sin (derive_semantics compo sem).
Proof.
move: sin sout sem init comp.
cofix derives_compliant=> sin sout sem init comp.
(* The corecursive call must come first, directly under the constructor. *)
constructor=> A cmd req; last first.
  apply: (derives_compliant _ (run_instrument cout sout sem (compo A cmd)).2.1).
    have [pre_c post_c] := correct sin sout init A cmd req.
    have [_ inv_next] :=
      post_c _ _ (run_instrument_post cout sout sem _ comp pre_c).
    by rewrite eval_derive_semantics /eval_freer -(run_instrumentE cout sout).
  have [pre_c _] := correct sin sout init A cmd req.
  rewrite /exec_freer -(run_instrumentE cout sout).
  exact: run_instrument_compliant.
have [pre_c post_c] := correct sin sout init A cmd req.
have [promise_x _] :=
  post_c _ _ (run_instrument_post cout sout sem _ comp pre_c).
by rewrite eval_derive_semantics /eval_freer -(run_instrumentE cout sout).
Qed.
