From HB Require Import structures.
From mathcomp Require Import boot boolp.
From monae Require Import hierarchy.
From FreerDPS Require Import init effect freer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

HB.mixin Record isMonadAltFreer (F : effect) (M : UU0 -> UU0)
    of MonadAlt M := {
  trigger : F ~~> M ;
  denote (N : altMonad) (h : F ~~> N) : M ~~> N ;
  denote_ret : forall (N : altMonad) (h : F ~~> N) X (x : X),
    denote N h X (Ret x) = Ret x ;
  denote_bind : forall (N : altMonad) (h : F ~~> N) X Y m (f : X -> M Y),
    denote N h Y (m >>= f) = denote N h X m >>= (denote N h Y \o f) ;
  denote_trigger : forall (N : altMonad) (h : F ~~> N) X (cmd : F X),
    denote N h X (trigger X cmd) = h X cmd ;
  denote_alt : forall (N : altMonad) (h : F ~~> N) X (a b : M X),
    denote N h X (a [~] b) = denote N h X a [~] denote N h X b ;
  denote_unique : forall (N : altMonad) (h : F ~~> N) (denote' : M ~~> N),
      (forall X (x : X), denote' X (Ret x) = Ret x) ->
      (forall X Y (m : M X) (f : X -> M Y), denote' Y (m >>= f) =
         denote' X m >>= (denote' Y \o f)) ->
      (forall X (cmd : F X), denote' X (trigger X cmd) = h X cmd) ->
      (forall X (a b : M X),
         denote' X (a [~] b) = denote' X a [~] denote' X b) ->
    forall X (m : M X), denote' X m = denote N h X m }.

#[short(type=altFreerMonad)]
HB.structure Definition MonadAltFreer (F : effect) :=
  {M of isMonadAltFreer F M & }.

(** * Scheduler *)

(* par p q: every interleaving of the commands of p and q; shared_par: the
   parallel composition of two programs computing the same kind of result.
   Their laws are not fixed yet. *)
HB.mixin Record isFreerScheduler (F : effect) (M : UU0 -> UU0)
    of MonadAltFreer F M := {
  par : forall X Y : UU0, M X -> M Y -> M (X * Y)%type ;
  shared_par : forall X : UU0, M X -> M X -> M X }.

#[short(type=freerScheduler)]
HB.structure Definition MonadFreerScheduler (F : effect) :=
  {M of isFreerScheduler F M & }.

Arguments par {_ _ _ _}.
Arguments shared_par {_ _ _}.

(* p || q, for par p q; it shadows the boolean or of bool_scope, which
   is then written (b || c)%B *)
Declare Scope par_scope.
Delimit Scope par_scope with par.
Notation "p || q" := (@par _ _ _ _ p q) : par_scope.

Module AltFreerModel.

Inductive alt_freer (F : effect) (A : Type) :=
| pure (x : A)
| impure {B} (cmd : F B) (k : B -> branch F A)
with branch (F : effect) (A : Type) :=
| single (b : alt_freer F A)
| more (b : alt_freer F A) (bs : branch F A).

Arguments pure [F A] (x).
Arguments impure [F A B] (cmd k).
Arguments single [F A] (b).
Arguments more [F A] (b bs).

(* Induction principle for a tree-like inductive : *)
(* https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#generation-of-induction-principles-with-scheme *)
Scheme alt_freer_mut := Induction for alt_freer Sort Prop
  with branch_mut := Induction for branch Sort Prop.

Section monad_s.

Context (F : effect).
Abbreviation acto := (@branch F).

Fixpoint branch_cat {A} (m1 m2 : acto A) : acto A :=
  match m1 with
  | single b => more b m2
  | more b bs => more b (branch_cat bs m2)
  end.

Lemma branch_catA A : associative (@branch_cat A).
Proof. by move=> m1 m2 m3; elim: m1=> [b|b bs ih] //=; rewrite ih. Qed.

Fixpoint alt_freer_bind {A B} (b : alt_freer F A) (f : A -> acto B) : acto B :=
  match b with
  | pure x => f x
  | impure _ cmd k => single (impure cmd (fun x => branch_bind (k x) f))
  end
with branch_bind {A B} (m : acto A) (f : A -> acto B) : acto B :=
  match m with
  | single b => alt_freer_bind b f
  | more b bs => branch_cat (alt_freer_bind b f) (branch_bind bs f)
  end.

Lemma alt_freer_bind_impure A B C (cmd : F C) (g : C -> acto A)
    (f : A -> acto B) :
  alt_freer_bind (impure cmd g) f =
    single (impure cmd (fun x => branch_bind (g x) f)).
Proof. by []. Qed.

Lemma branch_bind1 A B (b : alt_freer F A) (f : A -> acto B) :
  branch_bind (single b) f = alt_freer_bind b f.
Proof. by []. Qed.

Lemma branch_bind_more A B (b : alt_freer F A) bs (f : A -> acto B) :
  branch_bind (more b bs) f =
    branch_cat (alt_freer_bind b f) (branch_bind bs f).
Proof. by []. Qed.

Lemma branch_bind_cat A B (m1 m2 : acto A) (f : A -> acto B) :
  branch_bind (branch_cat m1 m2) f =
    branch_cat (branch_bind m1 f) (branch_bind m2 f).
Proof. by elim: m1=> [b|b bs ih] //=; rewrite ih branch_catA. Qed.


Let ret : idfun ~~> acto := fun A x => single (pure x).

Let left_neutral : BindLaws.left_neutral (@branch_bind) ret.
Proof. by []. Qed.

Let right_neutral : BindLaws.right_neutral (@branch_bind) ret.
Proof.
move=> A.
apply: (@branch_mut F A (fun b => alt_freer_bind b (@ret A) = single b))
  => [x|B cmd k ihk|b ih|b ih bs ihs] //.
- rewrite alt_freer_bind_impure.
  by congr (single (impure _ _)); exact/funext.
by rewrite branch_bind_more ih ihs.
Qed.

Let assoc : BindLaws.associative (@branch_bind).
Proof.
move=> A B C + f g.
apply: (@branch_mut F A (fun b => branch_bind (alt_freer_bind b f) g =
    alt_freer_bind b (fun x => branch_bind (f x) g)))
  => [x|D cmd k ihk|b ih|b ih bs ihs] //.
- rewrite alt_freer_bind_impure branch_bind1 !alt_freer_bind_impure.
  by congr (single (impure _ _)); exact/funext.
by rewrite !branch_bind_more branch_bind_cat ih ihs.
Qed.

#[export]
HB.instance Definition _ := @isMonad_ret_bind.Build acto ret
  (@branch_bind) left_neutral right_neutral assoc.

Lemma branch_bindE A B (m : acto A) (f : A -> acto B) :
  m >>= f = branch_bind m f.
Proof. by []. Qed.
End monad_s.
End AltFreerModel.
HB.export AltFreerModel.

Module AltMod.
Import AltFreerModel.

Section alt_s.
Context (F: effect).
Abbreviation acto := (@branch F).

Let alt : forall A, acto A -> acto A -> acto A := @branch_cat F.

Let altA : forall A, associative (@alt A).
Proof. exact: branch_catA. Qed.

Let alt_bindDl : BindLaws.left_distributive (@bind acto) alt.
Proof. by move=> *; exact: branch_bind_cat. Qed.

#[export]
HB.instance Definition _ := isMonadAlt.Build acto altA alt_bindDl.

Lemma branch_catE A (m1 m2 : acto A) :
  branch_cat m1 m2 = m1 [~] m2.
Proof. by []. Qed.
End alt_s.
End AltMod.
HB.export AltMod.

Module AltFreer.
Import AltFreerModel AltMod.

Section alt_freer.
Context (F : effect).

Abbreviation acto := (@branch F).

Definition trigger_effect : F ~~> acto := fun A cmd =>
  single (impure cmd (fun x => single (pure x))).

Fixpoint dnt_alt_freer (N : altMonad) (h : F ~~> N) A (b : alt_freer F A) :
    N A :=
  match b with
  | pure x => Ret x
  | impure _ cmd k => h _ cmd >>= fun x => dnt h (k x)
  end
with dnt (N : altMonad) (h : F ~~> N) A (m : acto A) : N A :=
  match m with
  | single b => dnt_alt_freer h b
  | more b bs => dnt_alt_freer h b [~] dnt h bs
  end.

Section dnt_lemmas.
Variables (N : altMonad) (h : F ~~> N).

Lemma dnt1 A (b : alt_freer F A) : dnt h (single b) = dnt_alt_freer h b.
Proof. by []. Qed.

Lemma dnt_alt_freer_impure A B (cmd : F B) (f : B -> acto A) :
  dnt_alt_freer h (impure cmd f) = h cmd >>= (fun x => dnt h (f x)).
Proof. by []. Qed.

Lemma dnt_cat A (m1 m2 : acto A) :
  dnt h (m1 [~] m2) = dnt h m1 [~] dnt h m2.
Proof.
rewrite -branch_catE.
by elim: m1=> [b|b bs ih] //=; rewrite ih altA.
Qed.

End dnt_lemmas.

Lemma trigger_bindE A B (cmd : F B) (f : B -> acto A) :
  trigger_effect cmd >>= f = single (impure cmd f).
Proof. by []. Qed.

Let dnt_ret (N : altMonad) (h : F ~~> N) X (x : X) :
  dnt h (Ret x : acto X) = Ret x.
Proof. by []. Qed.

Let dnt_bind (N : altMonad) (h : F ~~> N) X Y (m : acto X)
    (f : X -> acto Y) :
  dnt h (m >>= f) = dnt h m >>= (fun x => dnt h (f x)).
Proof.
rewrite branch_bindE; move: m.
apply: (@branch_mut F X (fun b => dnt h (alt_freer_bind b f) =
    dnt_alt_freer h b >>= (fun x => dnt h (f x))))
  => [x|B cmd k ihk|b ih|b ih bs ihs] //.
- by rewrite bindretf.
- rewrite alt_freer_bind_impure dnt1 !dnt_alt_freer_impure bindA.
  by apply: eq_bind=> y; exact: ihk.
by rewrite branch_bind_more branch_catE dnt_cat ih ihs /= alt_bindDl.
Qed.

Let dnt_trigger (N : altMonad) (h : F ~~> N) X (cmd : F X) :
  dnt h (trigger_effect cmd) = h X cmd.
Proof. by rewrite dnt1 dnt_alt_freer_impure; exact: bindmret. Qed.

Let dnt_alt (N : altMonad) (h : F ~~> N) X (a b : acto X) :
  dnt h (a [~] b) = dnt h a [~] dnt h b.
Proof. exact: dnt_cat. Qed.

Let dnt_unique (N : altMonad) (h : F ~~> N) (h' : acto ~~> N) :
    (forall X (x : X), h' X (Ret x) = Ret x) ->
    (forall X Y (m : acto X) (f : X -> acto Y),
       h' Y (m >>= f) = h' X m >>= (h' Y \o f)) ->
    (forall X (cmd : F X), h' X (trigger_effect cmd) = h X cmd) ->
    (forall X (a b : acto X), h' X (a [~] b) = h' X a [~] h' X b) ->
  forall X (m : acto X), h' X m = dnt h m.
Proof.
move=> dret' dbind' dtrigger' dalt' X.
apply: (@branch_mut F X (fun b => h' X (single b) = dnt_alt_freer h b))
  => [x|B cmd k ihk|b ih|b ih bs ihs] //.
- exact: dret'.
- rewrite -trigger_bindE dbind' dtrigger' dnt_alt_freer_impure.
  by apply: eq_bind=> x; exact: ihk.
by rewrite -[more b bs]/(single b [~] bs) dalt' ih ihs.
Qed.

#[export]
HB.instance Definition _ := isMonadAltFreer.Build F acto
  dnt_ret dnt_bind dnt_trigger dnt_alt dnt_unique.

End alt_freer.
End AltFreer.
HB.export AltFreer.

(*******************)

Section freer_to_alt_freer.
Context {F : effect} {M : freerMonad F} {N : altFreerMonad F}.

Definition freer_to_alt_freer : M ~~> N := freer.denote N trigger.

Lemma denote_freer_to_alt_freer (K : altMonad) (h : F ~~> K) X
    (m : M X) :
  denote K h X (freer_to_alt_freer m) = freer.denote K h X m.
Proof.
apply: (@freer.denote_unique F M K h
  (fun X m => denote K h X (freer_to_alt_freer m)))=> [Y y|Y Z m' f|Y cmd].
- by rewrite /freer_to_alt_freer freer.denote_ret denote_ret.
- by rewrite /freer_to_alt_freer freer.denote_bind denote_bind.
by rewrite /freer_to_alt_freer freer.denote_trigger denote_trigger.
Qed.

End freer_to_alt_freer.

(* as ptrigger in freer.v: trigger a primitive of an effect provided by Fx *)
Definition alt_ptrigger {Fx F : effect} `{F -< Fx} {M : altFreerMonad Fx} :
    F ~~> M :=
  fun a cmd => trigger a (inj cmd).
Arguments alt_ptrigger {_ _ _ _ _} _.


Module AltFreerScheduler.
Import AltFreerModel AltMod AltFreer.

Section alt_freer_scheduler.
Context (F : effect).

Abbreviation acto := (@branch F).

End alt_freer_scheduler.
End AltFreerScheduler.
HB.export AltFreerScheduler.
