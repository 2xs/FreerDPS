(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import boot functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer freer_alt contract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** To reason about impure computations, we introduce the “Hoare
    monad,” also called the “specification monad.” An instance of the
    specification monad is a couple of [pre] and [post] conditions,
    such that [pre p T] means the program specified by [p] can be
    executed safely from a state [T], and [post p T x T'] means the
    execution of [p] from [T] may compute a result [x] and bring the
    system to a state [T'].

    We equip this couple of predicate with a [bind] function to
    sequentially compose specifications. *)

Local Open Scope classical_set_scope.

(* model *)
Module Hoare.

Record hoare (T U : Type) : Type := mk_hoare {
  pre : set T ;
  post : T -> U -> set T }.

Ltac hoare_ext :=
  congr mk_hoare;
  [ apply: funext=> ?; apply: propext
  | apply: eq3_fun=> ? ? ?; apply: propext ].

Arguments mk_hoare {T U} (pre post).
Arguments pre {T U} (_ _).
Arguments post {T U} (_ _ _).

Definition hoare_ret {T U} (x : U) : hoare T U :=
  mk_hoare [set: T] (fun s y s' => (x = y) /\ (s = s')).

Definition hoare_bind {T U V}
    (m : hoare T U) (k : U -> hoare T V) : hoare T V :=
  mk_hoare (fun s => pre m s /\ (forall x, post m s x `<=` pre (k x)))
           (fun s x s2 => exists y s', post m s y s' /\ post (k y) s' x s2).

Section hm.
Variable T : Type.
Let ret := @hoare_ret T.
Let bind := @hoare_bind T.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /hoare_bind /hoare_ret/=; hoare_ext.
  by split=> [[]//|pr_s]; split=> // x s' _.
under eq2_exists do rewrite andA.
by rewrite ex2C ex2_eqr ex_eqr.
Qed.

(* Local Open Scope ssripat_scope. *)

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind /ret /hoare_bind /hoare_ret/=.
move fa : (f a) => [pr po]; hoare_ext.
  rewrite andTP; split.
  + by move=> /(_ a _); rewrite fa/=; exact.
  + by move=> prs _ _ [<- <-]; rewrite fa.
under eq2_exists do rewrite andC andA.
rewrite ex2C.
under eq_exists do rewrite ex_andl.
by rewrite ex_eqr_sym ex_eqr_sym fa.
Qed.

Let assoc : BindLaws.associative bind.
Proof.
move=> A B C m f g; rewrite /bind /ret /hoare_bind /hoare_ret/=.
case: m => prA poA/=; congr mk_hoare.
- apply/funext => s; apply/propext; split.
  + move=> [[prAs poApre postpre]].
    split => // a s1 sas1; split=> [|b s2 s'bs2].
      exact: poApre.
    by apply: postpre; exists a, s1.
  + move=> [prAs poApre]; split.
      by split=> // a s1 /poApre[].
    move=> b s1 [x [s2]] [] /poApre [fxs2] /[swap] s2bs1.
    exact.
- apply: eq3_fun => s c s1.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3C; apply: eq_exists => a.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3C; apply: eq_exists => s2.
  rewrite -ex_andr.
  under [in RHS]eq_exists do rewrite -ex_andr.
  by under [in RHS]eq2_exists do rewrite andA.
Qed.

HB.instance Definition _ := isMonad_ret_bind.Build (hoare T)
  left_neutral right_neutral assoc.

End hm.

End Hoare.

(** ** Monad *)

(** Easier to had future laws from there. *)
(*
HB.mixin Record isMonadHoare (S : Type)
    (M : Type -> Type) of Monad M := {}.

#[short(type=hoareMonad)]
HB.structure Definition MonadHoare (S : Type) :=
  {M of isMonadHoare S M &}.
*)

HB.export Hoare.

(*HB.instance Definition _ (S : Type) :=
  isMonadHoare.Build S (hoare S).*)

Module HoareAlt.
Section nd_s.

Variable T : UU0.

Definition hoare_alt {A} (a b : hoare T A) : hoare T A :=
  mk_hoare (pre a `&` pre b) (fun s x => post a s x `|` post b s x).

Definition hoare_fail {A} : hoare T A :=
  mk_hoare setT (fun _ _ => set0).

Lemma hoare_altA A (a b c : hoare T A) :
  hoare_alt a (hoare_alt b c) = hoare_alt (hoare_alt a b) c.
Proof. by hoare_ext; rewrite /=; tauto. Qed.

Lemma hoare_altC A (a b : hoare T A) : hoare_alt a b = hoare_alt b a.
Proof. by hoare_ext; rewrite /=; tauto. Qed.

Lemma hoare_altmm A (a : hoare T A) : hoare_alt a a = a.
Proof. by case: a=> pr po; hoare_ext; rewrite /=; tauto. Qed.

Lemma hoare_altfailm A (a : hoare T A) : hoare_alt hoare_fail a = a.
Proof. by case: a=> pr po; hoare_ext; rewrite /=; tauto. Qed.

Lemma hoare_altmfail A (a : hoare T A) : hoare_alt a hoare_fail = a.
Proof. by rewrite hoare_altC hoare_altfailm. Qed.

Lemma hoare_bindfailf A B (k : A -> hoare T B) :
  hoare_fail >>= k = hoare_fail.
Proof.
hoare_ext.
- by split=> // _; split=> // ? ? [].
by split=> // -[? [? []]].
Qed.

Lemma hoare_alt_bindDl A B (a b : hoare T A) (k : A -> hoare T B) :
  hoare_alt a b >>= k = hoare_alt (a >>= k) (b >>= k).
Proof.
hoare_ext; rewrite /=.
  split=> [[[pre_a pre_b] sub]|[[pre_a sub_a] [pre_b sub_b]]].
    by split; split=> // x s' po; apply: sub; [left|right].
  by split=> // x s' [po|po]; [exact: sub_a|exact: sub_b].
split=> [[x [s' [[po|po] k_post]]]|[[x [s' [po k_post]]]|]].
- by left; exists x, s'.
- by right; exists x, s'.
- by exists x, s'; split=> //; left.
case=> x [s' [po k_post]].
by exists x, s'; split=> //; right.
Qed.

Lemma hoare_alt_bindDr A B (m : hoare T A) (k1 k2 : A -> hoare T B) :
  m >>= (fun x => hoare_alt (k1 x) (k2 x)) = hoare_alt (m >>= k1) (m >>= k2).
Proof.
hoare_ext; rewrite /=.
  split=> [[pre_m sub]|[[pre_m sub1] [_ sub2]]].
    by split; split=> // x s' po; case: (sub x s' po).
  by split=> // x s' po; split; [exact: sub1|exact: sub2].
split=> [[x [s' [po [k_post|k_post]]]]|[[x [s' [po k_post]]]|]].
- by left; exists x, s'.
- by right; exists x, s'.
- by exists x, s'; split=> //; left.
case=> x [s' [po k_post]].
by exists x, s'; split=> //; right.
Qed.

HB.instance Definition _ :=
  isMonadFail.Build (hoare T) (@hoare_bindfailf).

HB.instance Definition _ :=
  isMonadAlt.Build (hoare T) (@hoare_altA) (@hoare_alt_bindDl).

HB.instance Definition _ :=
  isMonadAltCI.Build (hoare T) (@hoare_altmm) (@hoare_altC).

HB.instance Definition _ :=
  isMonadNondet.Build (hoare T) (@hoare_altfailm) (@hoare_altmfail).

End nd_s.
End HoareAlt.

HB.export HoareAlt.

(** ** Invariant Preservation *)

Definition preserves_invariant {S A}
    (invariant : set S) (h : hoare S A) :=
  forall state result state',
    pre h state ->
    post h state result state' ->
    invariant state ->
    invariant state'.

Lemma preserves_invariant_ret {S A}
    (invariant : set S) (result : A) :
  preserves_invariant invariant (@ret (hoare S) A result).
Proof. by move=>???? [_ <-]. Qed.

Lemma preserves_invariant_bind {S A B} (invariant : set S)
    (h : hoare S A) (k : A -> hoare S B) :
  preserves_invariant invariant h ->
  (forall result, preserves_invariant invariant (k result)) ->
  preserves_invariant invariant (h >>= k).
Proof.
move=> h_preserves k_preserves ??? [h_pre k_pre] [? [? [h_post k_post]]] Hsafe.
apply: k_preserves.
- exact/k_pre/h_post.
- exact: k_post.
by move: h_pre h_post Hsafe; exact: h_preserves.
Qed.

Lemma denote_preserves_invariant {Fx : effect} {M : inductiveFreerMonad Fx}
  {S : UU0} (invariant : set S) (handler : Fx ~~> hoare S) (A : UU0) (p : M A) :
  (forall (X : Type) (cmd : Fx X),
    preserves_invariant invariant (handler _ cmd)) ->
  preserves_invariant invariant
    (freer.denote (hoare S) handler A p).
Proof.
move=> H s a s'.
apply: (@denote_ind _ _ _ _  (fun X => preserves_invariant invariant)).
- move=> X x.
  exact: preserves_invariant_ret.
- move=> X Y h k h_preserves k_preserves.
  exact: preserves_invariant_bind h_preserves k_preserves.
- exact: H.
Qed.

From mathcomp Require Import reals.
From infotheo Require Import fsdist realType_ext.

Section hoare_of_contract.
Context {R : realType} {Fx F : effect} `{F -<? Fx} (S : choiceType) (c : contract R F S).

Local Open Scope classical_set_scope.

Definition hoare_of_contract : Fx ~~> hoare S :=
  fun U cmd => mk_hoare
    (gen_requirement R c ^~ cmd)
    (fun s (x : U) s' => fsdist1 s' = gen_state_update R c s cmd x /\
                         gen_promise R c s cmd x).

Definition freer_to_hoare {M : freerMonad Fx} : M ~~> hoare S :=
  freer.denote _ hoare_of_contract.

End hoare_of_contract.
Arguments hoare_of_contract : simpl never.
Arguments freer_to_hoare {R Fx F _ M S} c {U} : rename, simpl never.

(** A Hoare triple can be interpreted from the program `p`
  * through the contract `c`.
  *)
Notation "c |~ p" := (@freer_to_hoare _ _ _ _ _ c _ _ p)
  (at level 60, no associativity).

Module FreerHoare.
Section freer_to_hoare_lemmas.
Context {R : realType} {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
 (S : choiceType) (c : contract R F S).

(* Context {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx} *)
    (* (S : Type) (c : contract F S). *)

Local Open Scope classical_set_scope.
Check c.
Lemma pre_ret {U : Type} (u : U) : pre (c |~ (Ret u : M _)) = [set: S].
Proof. by rewrite /freer_to_hoare freer.denote_ret. Qed.

Lemma pre_skip : pre (c |~ (skip : M _)) = [set: S].
Proof. by rewrite pre_ret. Qed.

Lemma post_ret {U : Type} (u v : U) (s s' : S) :
  post (c |~ (Ret u : M _)) s v s' <-> u = v /\ s = s'.
Proof. by rewrite /freer_to_hoare freer.denote_ret. Qed.

Lemma post_skip (s s' : S) (x : unit) :
  post (c |~ (skip : M _)) s x s' <-> s = s'.
Proof.
by rewrite /freer_to_hoare/= post_ret; split=> [[]//|<-]; case: x.
Qed.

End freer_to_hoare_lemmas.

Section GenericToHoareSection.
Context {R : realType} {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (S : choiceType) (c : contract R F S).

Lemma to_hoare_triggerE (a : Type) (cmd : Fx a) :
  (c |~ (freer.trigger a cmd : M _)) = hoare_of_contract c cmd.
Proof. exact: freer.denote_trigger. Qed.

Lemma freer_to_hoare_bindE {a b : Type} (p : M a) (f : a -> M b) :
  c |~ (p >>= f) = (c |~ p) >>= fun x => (c |~ (f x)).
Proof. exact: freer.denote_bind. Qed.

Section BindFacts.
Context {A B : Type} (p : M A) (f : A -> M B).

Lemma pre_bindmskip : pre (c |~ p >> skip) = pre (c |~ p).
Proof.
apply/funext => s; rewrite freer_to_hoare_bindE.
apply/propext; split=> [[]//|cps/=]; split => //.
by rewrite pre_skip.
Qed.

Lemma post_bindmskip s s' u (x : unit) :
  post (c |~ p) s u s' -> post (c |~ p >> skip) s x s'.
Proof.
move=> tut'; rewrite freer_to_hoare_bindE/=.
by exists u, s'; split => //; rewrite post_skip.
Qed.

End BindFacts.

Section WhenFacts.
Context {U : Type} (p : M U).

Lemma pre_to_hoare_whenP b (s : S) :
  pre (c |~ when b p) s <-> if b then pre (c |~ p) s else True.
Proof. by case: b => /=; [rewrite pre_bindmskip|rewrite pre_skip]. Qed.

Lemma post_to_hoare_whenP b (s : S) (x : unit) (s' : S) :
  post (c |~ when b p) s x s' <->
  if b
  then exists y, post (c |~ p) s y s'
  else s' = s.
Proof.
case: x.
case: b => /=; last by rewrite post_skip; split => /esym.
split.
  rewrite freer_to_hoare_bindE/= => -[u' [t2 [H1 H2]]].
  exists u'.
  by move: H2; rewrite post_skip => <-.
move=> [u tut'].
rewrite freer_to_hoare_bindE/=.
exists u, s'; split => //.
by rewrite post_skip.
Qed.

End WhenFacts.

End GenericToHoareSection.

Lemma to_hoare_preserves_invariant {R : realType} {Fx F : effect} `{F -<? Fx}
  {M : inductiveFreerMonad Fx} {S : choiceType}
  (invariant : set S) (c : contract R F S)
  (handler_preserves : forall (A : UU0) (cmd : Fx A),
    preserves_invariant invariant (hoare_of_contract c cmd)) (A : UU0) (p : M A) :
  preserves_invariant invariant (c |~ p).
Proof. exact: denote_preserves_invariant. Qed.

(** ** Trigger Views *)

Section contract_trigger_helpers.
Context {R : realType} {Fx F : effect} `{F -< Fx} {M : freerMonad Fx}
    (S : choiceType) (c : contract R F S) {A : Type}.

Lemma pre_to_hoare_triggerP (cmd : F A) (s : S) :
  pre (c |~ (ptrigger cmd : M _)) s <->
  requirement c s cmd.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Lemma post_to_hoare_triggerP (cmd : F A) (s : S) (a : A) (s' : S) :
  post (c |~ (ptrigger cmd : M _)) s a s' <->
  fsdist1 s' = state_update c s cmd a /\ promise c s cmd a.
Proof. by rewrite to_hoare_triggerE /= provided_calleeP. Qed.

End contract_trigger_helpers.

(* Frame rule machinery *)
Module frame_rule.
Module Export SyntaxFreer.

Inductive fSyntax {F : effect} : Type -> Type :=
| ret : forall A, A -> fSyntax A
| bind : forall B A, fSyntax B -> (B -> fSyntax A) -> fSyntax A
| trigger : forall A, F A -> fSyntax A.

Fixpoint fSem {Fx F : effect} `{F -< Fx} {M : freerMonad Fx} {A}
    (m : @fSyntax F A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => fSem m >>= (fSem \o f)
  | trigger A cmd => ptrigger cmd
  end.

Abbreviation freerSyntax := fSyntax.
Abbreviation frRet := ret.
Abbreviation frBind := bind.
Abbreviation frTrigger := trigger.
Abbreviation freerSem := fSem.
End SyntaxFreer.

(** A witness records that a program uses only one of the two effects. *)
Section split_effects.
Context {Fx F : effect} `{F -< Fx}.
Context {M : freerMonad Fx} {A : UU0}.

Definition providesOnlyF (n : M A) := {m | freerSem (F := F) m = n}.
End split_effects.

Section contract_correspondance.
Context {R : realType} {Fx F G : effect} `{F ;; G -<< Fx} {M : freerMonad Fx}
  {T : choiceType} {U : UU0} (cf : contract R F T) (cg : contract R G T).

Lemma freer_contract_left (m : M U) :
  providesOnlyF (F:=F) m -> (cf -^- cg |~ m) = (cf |~ m).
Proof.
rewrite /freer_to_hoare.
case=> syntax; elim: syntax m=>
    [X x m <- | X Y prefix IHprefix suffix IHsuffix m <- | X cmd m <-] /=.
- by rewrite !freer.denote_ret.
- rewrite !freer.denote_bind.
  under eq_bind=> x do rewrite !compE (IHsuffix x) //=.
  by rewrite IHprefix.
- rewrite !freer.denote_trigger /hoare_of_contract /sharedcontractprod /=.
  rewrite /gen_state_update /gen_requirement /gen_promise /=.
  rewrite injK_Some injK_None.
  congr mk_hoare.
  + by apply/funext=> s; rewrite andPT.
  + by apply/eq3_fun=> s b s'; rewrite andPT.
Qed.

Lemma freer_contract_right (m : M U) :
  providesOnlyF (F:=G) m -> (cf -^- cg |~ m) = (cg |~ m).
Proof.
rewrite /freer_to_hoare.
case=> syntax; elim: syntax m=>
    [X x m <- | X Y prefix IHprefix suffix IHsuffix m <- | X cmd m <-] /=.
- by rewrite !freer.denote_ret.
- rewrite !freer.denote_bind.
  under eq_bind=> x do rewrite !compE (IHsuffix x) //=.
  by rewrite IHprefix.
- rewrite !freer.denote_trigger /hoare_of_contract /sharedcontractprod /=.
  rewrite /gen_state_update /gen_requirement /gen_promise /=.
  rewrite injK_Some injK_None.
  congr mk_hoare.
  + by apply/funext=> s; rewrite andTP.
  + by apply/eq3_fun=> s b s'; rewrite andTP.
Qed.

End contract_correspondance.
Section syntax_inclusion.
Context {Fx F G : effect} `{F -< G} `{G -< Fx}.
Context {M : freerMonad Fx} {A : Type}.

Lemma providesOnlyFT (m : M A) :
  providesOnlyF (F:=F) m -> providesOnlyF (F:=G) m.
Proof.
case=> syntax <-.
elim: syntax=>
    [X x | X Y prefix [prefix' prefixE] suffix IHsuffix | X cmd].
- by exists (frRet x).
- exists (frBind prefix' (fun x=> sval (IHsuffix x))).
  rewrite /= prefixE.
  congr (_ >>= _).
  apply: boolp.funext=> x.
  exact: svalP (IHsuffix x).
- by exists (frTrigger (inj cmd)).
Qed.
End syntax_inclusion.
Section lift_shared_contract.
Context {R : realType} {Fx Fg F G : effect} `{F ;; G -<< Fg} `{Fg -< Fx}.
Context {M : freerMonad Fx} {T : choiceType}  {U : Type}.
Variables (cf : contract R F T) (cg : contract R G T).

Lemma freer_contract_prodT (m : M U) :
  ((cf -^- cg : contract R Fg T) |~ m) =
  ((cf -^- cg : contract R Fx T) |~ m).
Proof.
rewrite /freer_to_hoare.
congr (freer.denote _ _ U m).
apply: functional_extensionality_dep=> A.
apply: boolp.funext=> cmd.
rewrite /hoare_of_contract /sharedcontractprod /gen_requirement
   /gen_state_update /gen_promise /=.
case: (prj cmd)=> [op|] //=.
hoare_ext; tauto.
Qed.
End lift_shared_contract.

#[export] Hint Extern 0 (providesOnlyF _) =>
  multimatch goal with
  | inner : ?F -< ?Fx |- @providesOnlyF _ ?Fx _ _ _ _ =>
      solve [by apply: (providesOnlyFT (F:=F))]
  | inner : ?F;;?G -<< ?Fx
      |- @providesOnlyF _ ?Fx _ _ _ _ =>
      solve [by apply: (providesOnlyFT (F:=F))
            | by apply: (providesOnlyFT (F:=G))]
  end : core.
End frame_rule.
Export frame_rule.
End FreerHoare.

Section alt_freer_hoare_of_contract.
Context {R : realType} {Fx F : effect} `{F -<? Fx} (S : choiceType)
  (c : contract R F S).

Definition alt_freer_to_hoare {M : altFreerMonad Fx} : M ~~> hoare S :=
  denote _ (hoare_of_contract c).

End alt_freer_hoare_of_contract.
Arguments alt_freer_to_hoare {R Fx F _ S} c {M A} : simpl never.

(** TODO: See if we can use the default notation instead of packaging a
  *       second one *)
Notation "c |~~ p" := (@alt_freer_to_hoare _ _ _ _ _ c _ _ p)
  (at level 60, no associativity).

(* TODO: See if we can remove as much duplicate as possible. *)
Module NonDetFreerHoare.
Section alt_freer_to_hoare_lemmas.
Context {R : realType} {Fx F : effect} `{F -<? Fx} {M : altFreerMonad Fx}
  (S : choiceType) (c : contract R F S).

Lemma alt_pre_ret {U : Type} (u : U) : pre (c |~~ (Ret u : M _)) = [set: S].
Proof. by rewrite /alt_freer_to_hoare denote_ret. Qed.

Lemma alt_pre_skip : pre (c |~~ (skip : M _)) = [set: S].
Proof. by rewrite alt_pre_ret. Qed.

Lemma alt_post_ret {U : Type} (u v : U) (s s' : S) :
  post (c |~~ (Ret u : M _)) s v s' <-> u = v /\ s = s'.
Proof. by rewrite /alt_freer_to_hoare denote_ret. Qed.

Lemma alt_post_skip (s s' : S) (x : unit) :
  post (c |~~ (skip : M _)) s x s' <-> s = s'.
Proof.
by rewrite /alt_freer_to_hoare/= alt_post_ret; split=> [[]//|<-]; case: x.
Qed.

End alt_freer_to_hoare_lemmas.

Section GenericAltToHoareSection.
Context {R : realType} {Fx F : effect} `{F -<? Fx} {M : altFreerMonad Fx}
    (S : choiceType) (c : contract R F S).

Lemma alt_to_hoare_triggerE (a : Type) (cmd : Fx a) :
  (c |~~ (trigger a cmd : M _)) = hoare_of_contract c cmd.
Proof. exact: denote_trigger. Qed.

Lemma alt_freer_to_hoare_bindE {a b : Type} (p : M a) (f : a -> M b) :
  c |~~ (p >>= f) = (c |~~ p) >>= fun x => (c |~~ (f x)).
Proof. exact: denote_bind. Qed.

(* alternatives are interpreted as the demonic choice of hoare_bonus.v *)
Lemma alt_freer_to_hoare_altE {a : Type} (p q : M a) :
  c |~~ (p [~] q) = (c |~~ p) [~] (c |~~ q).
Proof. exact: denote_alt. Qed.

Lemma alt_pre_alt {a : Type} (p q : M a) (s : S) :
  pre (c |~~ (p [~] q)) s <-> pre (c |~~ p) s /\ pre (c |~~ q) s.
Proof. by rewrite alt_freer_to_hoare_altE. Qed.

Lemma alt_post_alt {a : Type} (p q : M a) (s : S) (x : a) (s' : S) :
  post (c |~~ (p [~] q)) s x s' <->
    post (c |~~ p) s x s' \/ post (c |~~ q) s x s'.
Proof. by rewrite alt_freer_to_hoare_altE. Qed.

Section BindFacts.
Context {A B : Type} (p : M A) (f : A -> M B).

Lemma alt_pre_bindmskip : pre (c |~~ p >> skip) = pre (c |~~ p).
Proof.
apply/funext => s; rewrite alt_freer_to_hoare_bindE.
apply/propext; split=> [[]//|cps/=]; split => //.
by rewrite alt_pre_skip.
Qed.

Lemma alt_post_bindmskip s s' u (x : unit) :
  post (c |~~ p) s u s' -> post (c |~~ p >> skip) s x s'.
Proof.
move=> tut'; rewrite alt_freer_to_hoare_bindE/=.
by exists u, s'; split => //; rewrite alt_post_skip.
Qed.

End BindFacts.

Section WhenFacts.
Context {U : Type} (p : M U).

Lemma alt_pre_to_hoare_whenP b (s : S) :
  pre (c |~~ when b p) s <-> if b then pre (c |~~ p) s else True.
Proof.
by case: b => /=; [rewrite alt_pre_bindmskip|rewrite alt_pre_skip].
Qed.

Lemma alt_post_to_hoare_whenP b (s : S) (x : unit) (s' : S) :
  post (c |~~ when b p) s x s' <->
  if b
  then exists y, post (c |~~ p) s y s'
  else s' = s.
Proof.
case: x.
case: b => /=; last by rewrite alt_post_skip; split => /esym.
split.
  rewrite alt_freer_to_hoare_bindE/= => -[u' [t2 [H1 H2]]].
  exists u'.
  by move: H2; rewrite alt_post_skip => <-.
move=> [u tut'].
rewrite alt_freer_to_hoare_bindE/=.
exists u, s'; split => //.
by rewrite alt_post_skip.
Qed.

End WhenFacts.

End GenericAltToHoareSection.

(** ** Trigger Views *)

Section alt_contract_trigger_helpers.
Context {R : realType} {Fx F : effect} `{F -< Fx} {M : altFreerMonad Fx}
    (S : choiceType) (c : contract R F S) {A : Type}.

Lemma alt_pre_to_hoare_triggerP (cmd : F A) (s : S) :
  pre (c |~~ (alt_ptrigger cmd : M _)) s <->
  requirement c s cmd.
Proof. by rewrite alt_to_hoare_triggerE /= provided_callerP. Qed.

Lemma alt_post_to_hoare_triggerP (cmd : F A) (s : S) (a : A) (s' : S) :
  post (c |~~ (alt_ptrigger cmd : M _)) s a s' <->
  fsdist1 s' = state_update c s cmd a /\ promise c s cmd a.
Proof. by rewrite alt_to_hoare_triggerE /= provided_calleeP. Qed.

End alt_contract_trigger_helpers.

(* Frame rule machinery, as in hoare.v, with alternatives in the syntax *)
Module alt_frame_rule.
Module Export AltSyntaxFreer.

Inductive afSyntax {F : effect} : Type -> Type :=
| afret : forall A, A -> afSyntax A
| afbind : forall B A, afSyntax B -> (B -> afSyntax A) -> afSyntax A
| aftrigger : forall A, F A -> afSyntax A
| afalt : forall A, afSyntax A -> afSyntax A -> afSyntax A.

Fixpoint afSem {Fx F : effect} `{F -< Fx} {M : altFreerMonad Fx} {A}
    (m : @afSyntax F A) : M A :=
  match m with
  | afret A a => Ret a
  | afbind A B m f => afSem m >>= (afSem \o f)
  | aftrigger A cmd => alt_ptrigger cmd
  | afalt A a b => afSem a [~] afSem b
  end.

Abbreviation altFreerSyntax := afSyntax.
Abbreviation afRet := afret.
Abbreviation afBind := afbind.
Abbreviation afTrigger := aftrigger.
Abbreviation afAlt := afalt.
Abbreviation altFreerSem := afSem.
End AltSyntaxFreer.

(** A witness records that a program uses only one of the two effects. *)
Section alt_split_effects.
Context {Fx F : effect} `{F -< Fx}.
Context {M : altFreerMonad Fx} {A : UU0}.

Definition altProvidesOnlyF (n : M A) := {m | altFreerSem (F := F) m = n}.
End alt_split_effects.

Section alt_contract_correspondance.
Context {R : realType} {Fx F G : effect} `{F ;; G -<< Fx}
  {M : altFreerMonad Fx} {T : choiceType} {U : UU0}
  (cf : contract R F T) (cg : contract R G T).

Lemma alt_freer_contract_left (m : M U) :
  altProvidesOnlyF (F:=F) m -> (cf -^- cg |~~ m) = (cf |~~ m).
Proof.
rewrite /alt_freer_to_hoare.
case=> syntax; elim: syntax m=> [X x m <- | X Y prefix IHprefix suffix
  IHsuffix m <- | X cmd m <- | X a IHa b IHb m <-] /=.
- by rewrite !denote_ret.
- rewrite !denote_bind.
  under eq_bind=> x do rewrite !compE (IHsuffix x) //=.
  by rewrite IHprefix.
- rewrite !denote_trigger /hoare_of_contract /sharedcontractprod /=.
  rewrite /gen_state_update /gen_requirement /gen_promise /=.
  rewrite injK_Some injK_None.
  congr mk_hoare.
  + by apply/funext=> s; rewrite andPT.
  + by apply/eq3_fun=> s b s'; rewrite andPT.
- by rewrite !denote_alt (IHa _ erefl) (IHb _ erefl).
Qed.

Lemma alt_freer_contract_right (m : M U) :
  altProvidesOnlyF (F:=G) m -> (cf -^- cg |~~ m) = (cg |~~ m).
Proof.
rewrite /alt_freer_to_hoare.
case=> syntax; elim: syntax m=> [X x m <- | X Y prefix IHprefix suffix
  IHsuffix m <- | X cmd m <- | X a IHa b IHb m <-] /=.
- by rewrite !denote_ret.
- rewrite !denote_bind.
  under eq_bind=> x do rewrite !compE (IHsuffix x) //=.
  by rewrite IHprefix.
- rewrite !denote_trigger /hoare_of_contract /sharedcontractprod /=.
  rewrite /gen_state_update /gen_requirement /gen_promise /=.
  rewrite injK_Some injK_None.
  congr mk_hoare.
  + by apply/funext=> s; rewrite andTP.
  + by apply/eq3_fun=> s b s'; rewrite andTP.
- by rewrite !denote_alt (IHa _ erefl) (IHb _ erefl).
Qed.

End alt_contract_correspondance.
Section alt_syntax_inclusion.
Context {Fx F G : effect} `{F -< G} `{G -< Fx}.
Context {M : altFreerMonad Fx} {A : Type}.

Lemma altProvidesOnlyFT (m : M A) :
  altProvidesOnlyF (F:=F) m -> altProvidesOnlyF (F:=G) m.
Proof.
case=> syntax <-.
elim: syntax=> [X x | X Y prefix [prefix' prefixE] suffix IHsuffix | X cmd
  | X a [a' aE] b [b' bE]].
- by exists (afRet x).
- exists (afBind prefix' (fun x=> sval (IHsuffix x))).
  rewrite /= prefixE.
  congr (_ >>= _).
  apply: boolp.funext=> x.
  exact: svalP (IHsuffix x).
- by exists (afTrigger (inj cmd)).
by exists (afAlt a' b'); rewrite /= aE bE.
Qed.
End alt_syntax_inclusion.
Section alt_lift_shared_contract.
Context {R : realType} {Fx Fg F G : effect} `{F ;; G -<< Fg} `{Fg -< Fx}.
Context {M : altFreerMonad Fx} {T : choiceType}  {U : Type}.
Variables (cf : contract R F T) (cg : contract R G T).

Lemma alt_freer_contract_prodT (m : M U) :
  ((cf -^- cg : contract R Fg T) |~~ m) =
  ((cf -^- cg : contract R Fx T) |~~ m).
Proof.
rewrite /alt_freer_to_hoare.
congr (denote _ _ U m).
apply: functional_extensionality_dep=> A.
apply: boolp.funext=> cmd.
rewrite /hoare_of_contract /sharedcontractprod /gen_requirement
   /gen_state_update /gen_promise /=.
case: (prj cmd)=> [op|] //=.
congr mk_hoare.
- by apply/funext=> s; apply: propext; tauto.
by apply/eq3_fun=> s x s'; apply: propext; tauto.
Qed.
End alt_lift_shared_contract.

#[export] Hint Extern 0 (altProvidesOnlyF _) =>
  multimatch goal with
  | inner : ?F -< ?Fx |- @altProvidesOnlyF _ ?Fx _ _ _ _ =>
      solve [by apply: (altProvidesOnlyFT (F:=F))]
  | inner : ?F;;?G -<< ?Fx
      |- @altProvidesOnlyF _ ?Fx _ _ _ _ =>
      solve [by apply: (altProvidesOnlyFT (F:=F))
            | by apply: (altProvidesOnlyFT (F:=G))]
  end : core.
End alt_frame_rule.
Export alt_frame_rule.
End NonDetFreerHoare.

Export FreerHoare NonDetFreerHoare.

Module FreerAltBridge.
Import FreerHoare.frame_rule NonDetFreerHoare.alt_frame_rule.

Section freer_syntax_inclusion.
Context {Fx F : effect} `{F -< Fx}.

Fixpoint fs_to_af {A} (m : @freerSyntax F A) : @altFreerSyntax F A :=
  match m with
  | frRet A a => afRet a
  | frBind B A m f => afBind (fs_to_af m) (fun x => fs_to_af (f x))
  | frTrigger A cmd => afTrigger cmd
  end.

Context {M : freerMonad Fx} {N : altFreerMonad Fx}.

Lemma altFreerSem_fs_to_af {A} (m : @freerSyntax F A) :
  altFreerSem (fs_to_af m) = freer_to_alt_freer (freerSem m : M A) :> N A.
Proof.
elim: m=> [X x|X Y m IHm f IHf|X cmd] /=.
- by rewrite /freer_to_alt_freer freer.denote_ret.
- rewrite /freer_to_alt_freer freer.denote_bind /= IHm /freer_to_alt_freer.
  congr (_ >>= _); apply: boolp.funext=> x /=.
  exact: IHf.
by rewrite /freer_to_alt_freer freer.denote_trigger.
Qed.

Lemma altProvidesOnlyF_freer {A} (m : M A) :
  providesOnlyF (F:=F) m ->
  altProvidesOnlyF (F:=F) (freer_to_alt_freer m : N A).
Proof.
by case=> syntax <-; exists (fs_to_af syntax); rewrite altFreerSem_fs_to_af.
Qed.

End freer_syntax_inclusion.
End FreerAltBridge.

Export FreerAltBridge.
