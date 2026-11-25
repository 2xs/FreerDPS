(******************************************************************************)
(*            Generic monadic combinators that could go into monae.           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrnat.
From monae Require Import hierarchy.

Local Open Scope monae_scope.

Definition when {X} {M : monad} (b : bool) (m : M X) : M unit :=
  if b then m >> skip else skip.

Fixpoint retry_until {M : monad} {A : UU0} (stop : pred A) (run : M A)
    (fuel : nat) : M A :=
  if fuel is fuel'.+1 then
    run >>= fun r => if stop r then Ret r else retry_until stop run fuel'
  else run.
