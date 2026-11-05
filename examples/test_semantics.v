From mathcomp Require Import ssreflect ssrfun ssrnat.
From monae Require Import hierarchy.
From FreerDPS Require Import all_freerdps.

(* CLAUDE: new.  Computed checks of the operational semantics ported from
   FreeSpec (theories/semantics.v and the derivation part of component.v). *)

Local Open Scope semantics_scope.

(** [with_store] handles its primitives in place; the example comes from the
    documentation of FreeSpec's Semantics.v. *)

Goal with_store (M := freer _) (N := freer eempty) 0%N
    (with_store (N := freer _) 1%N
      (iget : freer (eplus (eplus eempty (STORE nat)) (STORE nat)) nat)) =
  Ret 1%N.
Proof. by []. Qed.

(** [semprod] dispatches each primitive to the matching semantics. *)

Goal eval_freer (store 1%N * store true)
    (iput 2%N >> (iget >>= fun n => iget >>= fun b =>
       Ret (if b then n else 0%N)) : freer (eplus (STORE nat) (STORE bool)) nat)
  = 2%N.
Proof. by []. Qed.

(** A component without lower effect gives a semantics with [bootstrap]; a
    component is plugged in place with [with_component]. *)

Definition answer : component (M := freer eempty) (STORE nat) eempty :=
  fun A cmd =>
    match cmd in STORE _ A return freer eempty A with
    | Get => Ret 42%N
    | Put _ => Ret tt
    end.

Goal eval_effect (bootstrap answer) Get = 42%N.
Proof. by []. Qed.

Goal with_component (Ret tt) answer (Ret tt)
    (iget : freer (eplus eempty (STORE nat)) nat) = Ret 42%N :> freer _ _.
Proof. by []. Qed.

Goal eval_effect (exec_effect (bootstrap answer) (Put 0%N)) Get = 42%N.
Proof. by rewrite exec_derive_semantics eval_derive_semantics. Qed.
