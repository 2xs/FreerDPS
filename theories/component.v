(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import init effect freer contract hoare.
From monae Require Import hierarchy.

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

Definition correct_component {Fx Fin Fout : effect} `{Fout -<? Fx}
    {M : freerMonad Fx} {Sin Sout : Type}
    (compo : component Fin Fx) (cin : contract Fin Sin)
    (cout : contract Fout Sout) (rel_inv : Sin -> Sout -> Prop) :
  Prop :=
  forall (sin : Sin) (sout : Sout) (init : rel_inv sin sout) (T : Type)
      (cmd : Fin T) (req : requirement cin sin cmd),
    pre (cout |~ compo T cmd) sout /\
    forall (t : T) (sout' : Sout),
      post (cout |~ (compo T cmd : M _)) sout t sout' ->
      promise cin sin cmd t /\
      rel_inv (state_update cin sin cmd t) sout'.
