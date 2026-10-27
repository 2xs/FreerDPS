From mathcomp Require Import
  all_ssreflect ssralg poly ssrnum ssrint interval finmap mathcomp_extra boolp
  classical_sets functions cardinality fsbigop.

From mathcomp Require Import (canonicals) Rstruct.
From mathcomp.analysis_stdlib Require Import Rstruct_topology.
From mathcomp Require Import
  reals ereal interval_inference topology normedtype sequences realfun convex
  real_interval derive esum measure exp numfun lebesgue_measure
  measurable_realfun lebesgue_integral kernel probability hoelder unstable
  archimedean.
Require Reals Interval.Tactic.
From HB Require Import structures.
From AUChain Require Import
  sampling Network Protocol GlobalState Blocks Messages MessageTuple Parameters
  BlockTree Schedule LocalState MemEq SsrFacts TreeChain CG CP CQ
  additional_lemmas.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import hoelder ess_sup_inf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PoSProbabilityBounds.

Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope schedule_scope.

Let R := Rdefinitions.R.
Context {d} (T : measurableType d) (P : probability T R).

(* -------------------------------------------------------------------- *)
(* Shared probabilistic model                                            *)
(* -------------------------------------------------------------------- *)

Variable Sc : nat.
Hypothesis n_sup_O : (0 < Sc)%N.

Variable pLs pSs pAs : R.
Hypothesis pLs01 : (0 <= pLs <= 1)%R.
Hypothesis pSs01 : (0 <= pSs <= 1)%R.
Hypothesis pAs01 : (0 <= pAs <= 1)%R.

Variable LS : Sc.-tuple (bernoulliRV P pLs).
Variable SS : Sc.-tuple (bernoulliRV P pSs).
Variable AS : Sc.-tuple (bernoulliRV P pAs).

Definition LS_r := bool_trial_value LS.
Definition SS_r := bool_trial_value SS.
Definition AS_r := bool_trial_value AS.

Variable deltaLs deltaSs deltaAs : R.
Hypothesis delta_range_Ls : (0 < deltaLs < 1)%R.
Hypothesis delta_range_Ss : (0 < deltaSs < 1)%R.
Hypothesis delta_range_As : (0 < deltaAs < 1)%R.

(* -------------------------------------------------------------------- *)
(* Tuple utilities                                                       *)
(* -------------------------------------------------------------------- *)
(*fonction qui permet de récuperer un sous tuple de taille b - a , en gardant du
  tuple t passé en parametre,  b premiers éléments
  et en retirant les a premiers éléments*)
Definition tuple_interval_index {T : Type} (a b n : nat) (t : n.-tuple T) :=
  drop a (take b t).


(*Preuve qu'on connait la taille d'un tuple t de taille n après en avoir retiré
  les b premiers éléments et en en retirant les a premiers,
  la taille est (b - a)

  Hypothèses : a < b et b <= n*)
Lemma tuple_interval_size {X : Type} (a b n : nat) (t : n.-tuple X) (Hab : (a <
  b)%N) (Hb : (b <= n)%N) :
  size (drop a (take b (tval t))) == (b - a)%N.
Proof.
by rewrite size_drop size_take size_tuple -/(minn b n) (minn_idPl Hb).
Qed.

(*Fonction qui forme un tuple a partir de l'interval a b donné*)
Definition tuple_interval_index_fun ( a b n : nat) (t : n.-tuple T)
    (Hab : (a < b)%N) (Hb : (b <= n)%N) : ((b - a)%N).-tuple T :=
  Tuple (tuple_interval_size t Hab Hb).

Lemma Sc_pos_R : (0 < (Sc%:R : R))%R.
Proof. by rewrite ltr0n. Qed.

(* -------------------------------------------------------------------- *)
(* Shared interval tuples                                               *)
(* -------------------------------------------------------------------- *)

(*Extrait du tuple LS les slots d'indices a à b - 1 et contruit un tuple de
  taille b - a*)
Definition LS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pLs) :=
  Tuple (tuple_interval_size LS Hab Hb).

(*Extrait du tuple SS les slots d'indices a à b - 1 et contruit un tuple de
  taille b - a*)
Definition SS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pSs) :=
  Tuple (tuple_interval_size SS Hab Hb).

(*Extrait du tuple AS les slots d'indices a à b - 1 et contruit un tuple de
  taille b - a*)
Definition AS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pAs) :=
  Tuple (tuple_interval_size AS Hab Hb).

(* -------------------------------------------------------------------- *)
(* Shared Chernoff/complement bounds                                     *)
(* -------------------------------------------------------------------- *)

(*
Nous allons faire un point sur les notations et les éléments utilisés dans les
  suivants dans le fichier

La notation let A := B in n'est qu'une notation qui permet de simplifier
  l'onglet de preuve de l'assisstant, elle
effectue une simple substitution de texte qu'on peut introduire avec move => A.

On note X' comme fonction qui somme les variables aléatoires d'un tuple d'une
  réalisation donnée.

La notatation (\X_Sc P) construit la loi de Sc tirages indépendants chacun
  suivant la probabilité P, cette notation
est appliquée a des ensemble qui dans le monde des probabilités sont des
  événements, elle dénote grossierement la
probabilité qu'un élément donné appartient à lensemble sur le quel cette
  probabilité est appliquée.

La notation 'E_(\X_Sc P)[X'] dénote l'ésperance probabiliste où (\X_Sc P) décrit
  les Sc tirages indépendants et [X']
décrit la fonction qui est utilisée pour sommer les variables aléatoires.

La notation en ensemble se fait de la sorte :
[set i | Prop]

Les ensembles peuvent être vus un peu comme des fonction qui renvoie True si le
  i qui est donné à cet ensemble appartient
bien à l'ensemble et False sinon.

Point important: si i n'apparait pas dans la propriété de séléction d'un
  ensemble , alors l'ensemble est détérministe et vaut donc
soit setT soit set0 et revoiera soit True pour tout i donné soit False pour tout
  i donné.

Les lemmes et théorèmes de mathcomp possèdent souvent des variables ayant des
  types spécifiques que rocq ne peut pas convertir automatiquement,
Il faut donc très souvent faire des conversions de types explicites ou bien
  spécifier le type que rocq n'arrive pas a inférer.

Pour faire une conversion de type on utilise la notation :  %:(TYPE VOULU)

Pour spécifier un type on utilise la notaiton : %(TYPE SPECIFIE)

Dans la majorité des preuves suivantes nous n'utiliserons globalement que les
  types suivants :

N : entier naturel

R : réel

E : réel étendus (avec +infini et -infini)

Pour faire un Search il faut spécifiquement faire un Search en précisant le
  type.

Les opérateurs de comparaisons : < > <= >= sont aussi spécifiques par types il
  faut donc spécifier par exemple (a < b)%:R.

*)

(*Lemme qui fait sortir la négation de la condition de l'ensemble en une forme
  complémentaire de proba (1 - X) pour la borne sur les
lucky slots*)
Let XLS := bool_trial_value LS.
Let muLS := 'E_(\X_Sc P)[XLS].
Lemma complementary_specialized_LS :
  (\X_Sc P) [set i | ~~ (XLS i <= (1 - deltaLs) * fine muLS)%R ]%R
  =
  (((1%R)%:E - (\X_Sc P) [set i | XLS i <= (1 - deltaLs) * fine muLS ]%R))%E.
Proof. by rewrite complementary_specialized_le. Qed.

 (*Changment de sens de l'inégalité dans l'événement en écrivant l'ensemble sous
  forme complémentaire*)
Lemma complementary_Ls_Bound :
  (\X_Sc P) [set i | (1 - deltaLs) * fine muLS <  XLS i ]%R
  = (((1%R)%:E - (\X_Sc P) [set i | XLS i <= (1 - deltaLs) * fine muLS ]%R))%E.
Proof.
by rewrite -complementary_specialized_LS set_gt_as_compl_le.
Qed.

(*borne inférieure exprimée sur le rapport elle est le résultat de
  transformations de la borne
(sampling_ineq3 pLs01 LS delta_range_Ls).*)
Lemma complementary_LS_event :
  (((1%R)%:E - (expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E)%E
  <=
  (\X_Sc P) [set i | (1 - deltaLs) * fine muLS < XLS i]%R)%E.
Proof.
have /= := (sampling_ineq3 pLs01 LS delta_range_Ls).
by rewrite complementary_Ls_Bound -leeN2; exact: leeD2l.
Qed.

Let XSS := bool_trial_value SS.
Let muSS := 'E_(\X_Sc P)[XSS].
(*Lemme qui fait sortir la négation de la condition de l'ensemble en une forme
  complémentaire de proba (1 - X) pour la borne sur les
super slots*)
Lemma complementary_specialized_SS :
  (\X_Sc P) [set i | ~~ (XSS i <= (1 - deltaSs) * fine muSS)%R ]%R
  = (((1%R)%:E - (\X_Sc P) [set i | XSS i <= (1 - deltaSs) * fine muSS ]%R))%E.
Proof. by rewrite complementary_specialized_le. Qed.

(*Changment de sens de l'inégalité dans l'événement en écrivant l'ensemble sous
  forme complémentaire*)
Lemma complementary_SS_bound :
  (\X_Sc P) [set i | (1 - deltaSs) * fine muSS <  XSS i ]%R
  = (((1%R)%:E - (\X_Sc P) [set i | XSS i <= (1 - deltaSs) * fine muSS ]%R))%E.
Proof.
by rewrite -complementary_specialized_SS -set_gt_as_compl_le.
Qed.

(*borne inférieure exprimée sur le rapport elle est le résultat de
  transformations de la borne
(sampling_ineq3 pSs01 SS delta_range_Ss).*)
Theorem complementary_SS_event :
  (((1%R)%:E -
    (expR (-(fine muSS * deltaSs ^+ 2) / 2)%R)%:E)%E
  <=
  (\X_Sc P)
    [set i | (1 - deltaSs) * fine muSS < XSS i]%R)%E.
Proof.
have /= := (sampling_ineq3 pSs01 SS delta_range_Ss).
by rewrite complementary_SS_bound -leeN2; exact: leeD2l.
Qed.


Let XAS := bool_trial_value AS.
Let muAS := 'E_(\X_Sc P)[XAS].
(*Lemme qui fait sortir la négation de la condition de l'ensemble en une forme
  complémentaire de proba (1 - X) pour la borne sur les
adversarial slots*)
Lemma complementary_specialized_AS :
  (\X_Sc P) [set i | ~~ (XAS i >= (1 + deltaAs) * fine muAS)%R ]%R
  = (((1%R)%:E - (\X_Sc P) [set i | XAS i >= (1 + deltaAs) * fine muAS ]%R))%E.
Proof.
set B :=  (1 + deltaAs) * fine muAS.
set A := [set i | XAS i >= B ].
have [/= ->] : [set i | ~~ (XAS i >= B )] = ~` A
  by apply/seteqP; split=> /= i /negP.
apply: probability_setC; rewrite -(ST_Set A).
exact: (measurable_fun_le (D := setT) (f := fun _ => B) (g :=XAS)).
Qed.

(*Changment de sens de l'inégalité dans l'événement en écrivant l'ensemble sous
  forme complémentaire*)
Lemma complementary_AS_bound:
  (\X_Sc P) [set i | XAS i < (1 + deltaAs) * fine muAS]%R
  =
    (((1%R)%:E -
      (\X_Sc P) [set i | XAS i >= (1 + deltaAs) * fine muAS]%R))%E.
Proof.
rewrite -complementary_specialized_AS /=.
set B := ((1 + deltaAs) * fine muAS)%R.
by rewrite set_lt_as_compl_ge.
Qed.

(*borne inférieure exprimée sur le rapport elle est le résultat de
  transformations de la borne
(sampling_ineq2 pAs01 AS n_sup_O delta_range_As).*)
Theorem complementary_AS_event :
  (((1%R)%:E -
    (expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E)%E
  <=
  (\X_Sc P)
    [set i | XAS i < (1 + deltaAs) * fine muAS]%R)%E.
Proof.
have /= := (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
rewrite complementary_AS_bound -leeN2.
exact: leeD2l.
Qed.

(* ==================================================================== *)
(* Chain Growth                                                         *)
(* ==================================================================== *)

Section ChainGrowth.
 (* Protocol assumptions specific to Chain Growth. *)
 (*GlobalStates assumptions*)
 Variables (N_from_r N'_from_r : Sc.-tuple T -> GlobalState).
 Hypothesis N_from_initial : forall r, N0 ⇓ N_from_r r .
 Hypothesis N_is_ready : forall r, N_from_r r @ Ready.
 Hypothesis N'_from_N :  forall r, N_from_r r  ⇓^+ N'_from_r r.

(*party assumptions corresponding to CG assumptions for now*)
Variables (p1 p2 : Party).
Hypothesis p1_honest : is_honest p1.
Hypothesis p2_honest : is_honest p2.

(*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
Variable (l1_from_r l2_from_r : Sc.-tuple T -> LocalState).
Hypothesis l1_p1_state : forall r, has_state p1 (N_from_r r) (l1_from_r r).
Hypothesis l2_p2_state : forall r, has_state p2 (N'_from_r r) (l2_from_r r).

(*Assumption to link the bool_trial_value LS to the amount of lucky slots
  between N and N'*)
Hypothesis LS_r_eq_slotrange : forall r, (LS_r r  = | lucky_slots_range
  (t_now (N_from_r r)) ((t_now (N'_from_r r)) - 1) |%:R)%N.

Definition Chain_growth_ls_Good_event :=
  [set r | ((1 - deltaLs) * fine muLS < XLS r)%R].

Definition chain_growth_parties_event (w : nat)  :=
  [set r : Sc.-tuple T |
    ((|bestChain (t_now (N_from_r r) - 1)%N (tree (l1_from_r r))| + w)%N
      <= |bestChain (t_now (N'_from_r r) - 1)%N (tree (l2_from_r r))|)%N].

(*if you want to make a chain growth event that takes in condiseration a
  given r, you are in the obligation
to define functions on Global state and LocalState that depends on a given
  r, those functions are abstract
, meaning that no mater what we won't be apple to prove they are
  measurable*)
Hypothesis chain_growth_parties_event_measurable :
  forall w : nat, measurable (chain_growth_parties_event w).

(*Lemme qui montre que pour tout r si w%:r <= (1 - deltals) * fine mu
  alors l'événement probabiliste implique l'événement du protocole*)
(** application du théorème chain growth du fichier CG.v , la plupart des
  * hypothèses non probabilistes son triviales et donc résolues par easy
  * il ne reste plus que w <= |lucky_slots_range (t_now N) (t_now N' - 1)| à
  * démontrer
  *)
Lemma Good_Ls_implies_chain_growth w
  (H: w%:R <= (1 - deltaLs) * fine muLS) :
forall r, Chain_growth_ls_Good_event r -> chain_growth_parties_event w r.
Proof.
move=> r=> /ltW H' /=.
apply: (chain_growth_parties (p1:=p1) (p2:=p2))=>//.
rewrite -(ler_nat R) -LS_r_eq_slotrange.
exact/(le_trans H)/H'.
Qed.

(*Lemme qui utilise l'implication des événement pour démontrerque
  l'événement a une probabiltié supérieure
  On utilise la formule avec le lemme précédent : (A -> B) -> Pr[A] <=
    Pr[B] avec A et B deux événements.
*)
Lemma probability_implication (w : nat) :
  w%:R <= (1 - deltaLs) * fine muLS ->
  ((\X_Sc P) Chain_growth_ls_Good_event
    <= (\X_Sc P) (chain_growth_parties_event w))%E .
Proof.
move=> H1.
set B := ((1 - deltaLs) * fine muLS)%R.
(** Permet de démontrer que si on a deux événement A et B mesurables avec
  * A -> B alors (\X_x P) B >= (\X_x P) A.
  * Ici le théorème est appliqué a [Chain_growth_ls_Good_event] et a
  *  [chain_growth_parties_event w]
   on va ainsi démontrer que les deux événement sont mesurables et que
   [Chain_growth_ls_Good_event] -> [chain_growth_parties_event w]
  *)
apply: le_measure.
- rewrite /Chain_growth_ls_Good_event set_lt_eq_neg_le.
  have Hle :
      (measurable_structure.measure_tuple_display d).-measurable [set r |
        (XLS r <= B)%R].
      rewrite -(ST_Set [set r | XLS r <= B]).
      by apply (measurable_fun_le (D := setT) (f := XLS) (g := fun _ => B)).
   by rewrite inE; apply: measurableC; exact: Hle.
- by rewrite inE; apply chain_growth_parties_event_measurable.
- exact/Good_Ls_implies_chain_growth/H1.
Qed.


(*A partir des Lemmes précédents on montre par transitivité une borne sur
  Chain Growth*)
Theorem Chernoff_bound_chain_growth_parties_even (w:nat):
  w%:R <= (1 - deltaLs) * fine muLS ->
  (
    ((1%R)%:E - (expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E)%E
    <=
    ((\X_Sc P) (chain_growth_parties_event w))%E
  )%E.
Proof.
move=> H.
exact/(le_trans complementary_LS_event)/probability_implication.
Qed.

End ChainGrowth.

(* ==================================================================== *)
(* Chain Quality                                                        *)
(* ==================================================================== *)

Section ChainQuality.

Variable (N : GlobalState).
Hypothesis N_from_initial : N0 ⇓ N.
Hypothesis N_forging_free : forging_free N.
Hypothesis N_collision_free : collision_free N.

Variable (p : Party).
Hypothesis p_is_honest : is_honest p.

Variable (l : LocalState).

Hypothesis p_has_state_l: has_state p N l.

Variable (b_i b_j : Block).
Variable (c : Chain).
Hypothesis interval_is_fragment_of_best :
  fragment ([:: b_j] ++ c ++ [:: b_i]) (bestChain ((t_now N)-1)%N (tree
    l)).

Variable (w_cq : nat) (r_cq : Sc.-tuple T).
Variable (ds : nat).

(*assumption that ds is of size slot of B_j - slot of B_i*)
Hypothesis ds_eq_fragment_size : ds = (sl b_j - (sl b_i + 1))%N.

(*hypothèse de lien entre le modèle probabiliste et le modèle du protocole
  sur le fait qu'on ait  un comptage équivalent
  de lucky slots et adversarial slots sur un intervalle [a, b) avec a < b
    et b <= Sc, dans le protocole et le modèle probabiliste*)
Hypothesis Ls_r_range_link :
  forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
    bool_trial_value (LS_sub Hab Hb)
      (tuple_interval_index_fun r_cq Hab Hb)
    = | lucky_slots_range a b |%:R.

Hypothesis As_r_range_link :
  forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
    bool_trial_value (AS_sub Hab Hb)
      (tuple_interval_index_fun r_cq Hab Hb)
    = | adv_slots_range a b |%:R.

(** Hypothese qui sera à recréer de manière implicite à partir de la
  * condition sur la lottery(il existe epsilon tel que : pLs >= pAs +
  * epsilon)
  * elle dit globalement que pour tout sous intervalle de taille plus grande
  * que ds d'un tuple de base de taille Sc, On a a partir de
  * deltaAs deltaLs et pAs pLs qu'on a une domination de l'eperence sur cet
  * intervalle d'au moins w_cq.
  *)
Hypothesis w_cq_bound : forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
    (ds <= b - a)%N ->
((1 + deltaAs) * fine 'E_(\X_(b - a) P)[bool_trial_value (AS_sub Hab Hb)]
     + w_cq%:R
      <=
 (1 - deltaLs) * fine 'E_(\X_(b - a) P)[bool_trial_value (LS_sub Hab Hb)])%R.

(*there is enough lucky slots*)
Definition LS_good_event_CQ (a b : nat) (Hab : (a < b)%N) (Hb : (b <=
  Sc)%N) :=
  let X' := bool_trial_value (LS_sub Hab Hb) in
  let muLS := 'E_(\X_(b - a)%N P)[X'] in
  [set r | (1 - deltaLs) * fine muLS < X' r].

(* there is a satisfying number of adversarial slots*)
Definition AS_good_event_CQ (a b : nat) (Hab : (a < b)%N) (Hb : (b <=
  Sc)%N) :=
  let X' := bool_trial_value (AS_sub Hab Hb) in
  let muAS := 'E_(\X_(b - a)%N P)[X'] in
  [set r | (1 + deltaAs) * fine muAS > X' r].
(*conjonction entre les deux intervalles probabilistes sur les lucky slots
  et les adversarial slots sur un intervalle [a,b)*)
Definition CQ_good_event (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
  :=
  (LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ  Hab Hb).

(*
   événement probabiliste CQ_good_event replongé dans l'espace
     probabiliste des Sc slots.
   L'événement est défini de la sorte (match with) pour offir des preuves
     plus simples dans les preuves
   ultérieures

    Grace à ce type de définition on peut ainsi définir un événement qui
      contient un forall implicite
   Sans cette forme on définirait cet événement comme étant
   [set r | forall  a b (Hab : a < b)%N (Hb : b <= Sc) CQ_good_event Hab
     Hb (tuple_interval_index_fun r Hab Hb)]

*)
Definition CQ_interval_good_event (a b : nat) : set (Sc.-tuple T) :=
  match boolP (a < b)%N with
  | AltTrue Hab =>
      match boolP (b <= Sc)%N  with
      | AltTrue Hb =>
          [set r : Sc.-tuple T | CQ_good_event Hab Hb
            (tuple_interval_index_fun r Hab Hb)]
      | _ => setT
      end
  | _ => setT
  end.

(*événement qui définit que pour tout intervalle [a,b[ avec a < b et b <=
  Sc
  et d <= b - a, on a un avantage d'au moins w lucky slots sur les
    adversarial lucky_slots_range

   C'est l'événement qui représente la partie protocole de la
     modélisation, si cet événement est
   reussi alors, on peut appliquer chain chain_quality
*)
Definition CQ_slot_advantage (w d : nat) : Prop :=
  forall (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
    (d <= b - a)%N ->
    ((| adv_slots_range  a b| + w) <= | lucky_slots_range a b |)%N.

(* Lemme qui verifie que pour a et b donnés qui verifient a < b , b <= Sc
  et ds <= b - a,
   on a que notre événement probabiliste sur l'intervalle [a,b[ de
     l'execution fixe r_cq
   implique qu'on a un avantage de au moins w_cq lucky slots sur les
     adversarial slots

   Cet événement fait directement rapport avec la preuve mathématique de
     chain quality
   dans la première partie où on travaille d'abord sur un intervalle donné
     [a,b[

*)
Lemma CQ_good_interval_implies_advantage (a b : nat) (Hab : (a < b)%N) (Hb
  : (b <= Sc)%N) (Hsize : (ds <= b - a)%N) :
  CQ_good_event Hab Hb (@tuple_interval_index_fun a b Sc r_cq Hab Hb)
  -> ((| adv_slots_range  a b| + w_cq) <= | lucky_slots_range a b |)%N.
Proof.
rewrite /CQ_good_event /LS_good_event_CQ /AS_good_event_CQ /=.
rewrite As_r_range_link Ls_r_range_link=> -[HLS HAS].
rewrite -(ler_nat R) natrD.
  (*on instancie l'hypothèse sur la borne w_cq spécialisée sur notre
    intervalle [a,b[ *)
have [/= Hw] := w_cq_bound Hab Hb Hsize.
  (*transformation de l'inégalité entre entiers naturels en une inégalités
    de réels*)
  (*définitions et application d'alias pour simplifier l'affichage*)
set muAS_sub := fine 'E_(\X_(b - a) P)[(\sum_(i < b - a) Tnth (real_of_bool
    (AS_sub Hab Hb)) i)].
set muLS_sub := fine 'E_(\X_(b - a) P)[(\sum_(i < b - a) Tnth (real_of_bool
    (LS_sub Hab Hb)) i)].
have Htrans1 := le_lt_trans Hw HLS.
have HASw : (| adv_slots_range a b |)%:R + w_cq%:R < (1 + deltaAs) *
    muAS_sub + w_cq%:R by rewrite ltrD2r.
by have /ltW := lt_trans HASw Htrans1.
Qed.

(*if for every sub interval of size at least static variable ds of the
  static interval r_cq,
  we have that forall interval [a b] where the interval is ge than the
    fixed variable ds that
  the number of lucky slot is greater than the fixed  variable w_cq *)
Lemma CQ_all_interval_good_implies_advantage
  (HAIG: forall a b, CQ_interval_good_event a b r_cq) :
CQ_slot_advantage w_cq ds.
Proof.
rewrite /CQ_slot_advantage.
move=> a b Hab Hb Hds.
move: HAIG; rewrite /CQ_interval_good_event=>/(_ a b) /=.
case (boolP (a < b)%N)=> [Hab' |].
- case (boolP (b <= Sc)%N)=> [Hb' HAIG|].
  + have Habs : Hab = Hab' by done.
    have Hbs : Hb = Hb' by done.
    apply: (@CQ_good_interval_implies_advantage a b Hab Hb Hds).
    by move: HAIG;
      rewrite /CQ_good_event Habs Hbs /=.
  + by rewrite Hb.
- by rewrite Hab.
Qed.


(*preuve de la mesurailité de la fonction qui extrait les sous tuples, en
  démontrant que les projections du sous tuple sur le tuple initial
   son mesurables (globalement on démontre que l'indice d'un élément dans
     le tuple initial d'un a + m avec m l'indice de l'élément dans le
   tuple obtenu)*)
Lemma measurable_tuple_interval_index_fun
    (a b : nat)
    (Hab : (a < b)%N)
    (Hb : (b <= Sc)%N) :
  measurable_fun [set: Sc.-tuple T]
    (fun r : Sc.-tuple T =>
      tuple_interval_index_fun r Hab Hb).
Proof.
apply/measurable_fun_tnthP => -[m i].
have ty : (a + m < b)%N
  by rewrite -ltn_subRL.
have HSc_ai := ltn_leq_trans ty Hb.
pose j : 'I_Sc := @Ordinal Sc (a + m) HSc_ai.
have Hcoord (x : Sc.-tuple T) :
  tnth (Tuple (tuple_interval_size x Hab Hb)) (Ordinal i) = tnth x j
  by rewrite [LHS](tnth_nth (tnth x j)) /= nth_drop nth_take;
    [ exact: ty | exact: esym (tnth_nth (tnth x j) x j) ].
have Hfun :
  (fun x: Sc.-tuple T => tnth (Tuple (tuple_interval_size x Hab Hb)) (Ordinal i))
    = (fun x: Sc.-tuple T => tnth x j)
  by exact/funext/Hcoord.
by rewrite /= /comp Hfun; exact: measurable_tnth.
Qed.


(*preuve de mesurabilité du bon événement probabiliste sur les lucky slots
  sur un intervale [a,b)*)
Lemma LS_measurable_good_event_CQ (a b : nat) (Hab : (a < b)%N) (Hb : (b
  <= Sc)%N) :
  measurable (LS_good_event_CQ Hab Hb).
Proof.
  rewrite /LS_good_event_CQ.
  set X' := bool_trial_value (LS_sub Hab Hb).
  set mu := 'E_(\X_(b - a) P)[X'].
  set B := (1 - deltaLs) * fine mu.
  rewrite set_lt_eq_neg_le.
  apply: measurableC.
  rewrite -(ST_Set [set r |  X' r <= B]).
  apply: (measurable_fun_le (D := setT) (f := X' ) (g := fun _ => B))=>//.
Qed.

(*preuve de mesurabilité du bon événement probabiliste sur les adversarial
  slots sur un intervale [a,b)*)
Lemma AS_measurable_good_event_CQ (a b : nat) (Hab : (a < b)%N) (Hb : (b
  <= Sc)%N):
  measurable (AS_good_event_CQ Hab Hb).
Proof.
rewrite /AS_good_event_CQ.
set X' := bool_trial_value (AS_sub Hab Hb).
set mu := 'E_(\X_(b - a) P)[X'].
set B := (1 + deltaAs) * fine mu.
rewrite set_lt_as_compl_ge.
have -> : [set r | ~~ (B <= X' r)] = ~` [set r | B <= X' r]
  by apply/seteqP; split=> r /= /negP; exact.
apply: measurableC.
rewrite -(ST_Set ([set r | B <= X' r])).
by apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g := X')).
Qed.


(*preuve de mesurabilité sur le bon événement gloabal de chain quality sur
  un intervale [a,b) (conjonction du bon événement sur lucky et
  adversarial slots)*)
Lemma CQ_good_event_measurable (a b : nat) (Hab : (a < b)%N) (Hb : (b <=
  Sc)%N):
  measurable (CQ_good_event Hab Hb).
Proof.
apply:measurableI.
- exact: LS_measurable_good_event_CQ.
- exact: AS_measurable_good_event_CQ.
Qed.

Variable (epsilon : R).


(*Lemme qui permet d'isoler epsilon dans la partie gauche de l'inéquation
  depuis la première inéquation*)
Lemma epsilon_condition_CQ :
  (1 - deltaLs) * (pAs + epsilon) >
  (1 + deltaAs) * pAs <->
  epsilon > (((1 + deltaAs) / (1 - deltaLs)) - 1) * pAs.
Proof.
split.
(* both proofs are just reverted, there might be a way to invert this *)
- rewrite (mulrC (1 - deltaLs) (pAs + epsilon)) -(ltr_pdivrMr (pAs + epsilon)).
  + by rewrite subr_gt0; move/andP: delta_range_Ls=>[_ ].
  rewrite (mulrC (1 + deltaAs)) (mulrC pAs)=> H.
  by rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA
          (mulrC ((1 - deltaLs)^-1)) mulrA.
- rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA
          (mulrC ((1 - deltaLs)^-1))  mulrA=>H.
  rewrite (mulrC (1 - deltaLs) (pAs + epsilon)) -(ltr_pdivrMr (pAs + epsilon)).
  + by rewrite subr_gt0; move/andP: delta_range_Ls=>[_ ].
  by rewrite (mulrC (1 + deltaAs)) (mulrC pAs).
Qed.


(*Lemme qui permet d'exprimer l'intersection entre LS_good_event_CQ et
  AS_good_event_CQ
  en une forme "complémentaire", en exprimant l'intersection comme 1 -
    [probabilité qu'un des deux événements échoue]
*)
Lemma union_bound_LS_AS_CQ (a b : nat) (Hab : (a < b)%N) (Hb : (b <=
  Sc)%N):
  (\X_(b - a) P) ((LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ Hab Hb))
  =
  (1%R%:E - (\X_(b - a) P) ((~` (LS_good_event_CQ Hab Hb)) `|` (~`
    (AS_good_event_CQ Hab Hb))))%E.
Proof.
rewrite -probability_setC.
- apply:measurableU; apply: measurableC.
  + exact: LS_measurable_good_event_CQ.
  + exact: AS_measurable_good_event_CQ.
- congr ((\X_(b - a) P) _).
  apply/seteqP; split=> [r [??] [] //= | r H].
  by split; apply:Classical_Prop.NNPP=>?; apply: H; [left | right].
Qed.


(*Lemme qui applique l'inégalité de boole (union bound) à l'union des
  mauvais événement probabilistes pour pouvoir la borner par une somme*)
Lemma bad_event_union_bound_CQ (a b : nat) (Hab : (a < b)%N) (Hb : (b <=
  Sc)%N) :
  ((\X_(b - a)%N P) ((~` LS_good_event_CQ Hab Hb) `|` (~` AS_good_event_CQ
    Hab Hb))%E
  <=
  ((\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb)) + ((\X_(b - a)%N P) (~`
    AS_good_event_CQ Hab Hb)))%E.
Proof.
apply: measureU2; apply: measurableC.
- exact: LS_measurable_good_event_CQ.
- exact: AS_measurable_good_event_CQ.
Qed.

Section CQIntervalTrialStats.

Context (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N).

Let XLS' := bool_trial_value (LS_sub Hab Hb).
Let XAS' := bool_trial_value (AS_sub Hab Hb).
Let muLS' := 'E_(\X_(b - a)%N P)[XLS'].
Let muAS' := 'E_(\X_(b - a)%N P)[XAS'].

(*preuve pour l'instant inutile mais à potentiellement exploiter plus
  tard, dit que si l'esperance de LS est strictement plus
grande que l'esperance de AS, alors pour tout r si la valeure calculée du
  modèe probabiliste sur la réalisation r est plus grande que
son esperance pour les deux types de slots , alors on a un avantage de la
  valeure calculée du modèle probabiliste des lucky slots sur
les adversarial slots*)
Lemma LS_gt_AS :
  (1 + deltaAs) * fine muAS' < (1 - deltaLs) * fine muLS' ->
  forall r,
    (1 + deltaAs) * fine muAS' > AS_r r ->
    ((1 - deltaLs) * fine muLS') < LS_r r ->
    (LS_r r > AS_r r).
Proof.
move=> H r /= HAS HLS.
exact/(lt_trans HAS)/(lt_trans H).
Qed.


(*Borne supérieure de la somme des probabilités des mauvais événements
  probabilistes, en utilisant les inéquations de concentration*)
Lemma bad_event_chernoff_bound :
  (((\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb)) +
   ((\X_(b - a)%N P) (~` AS_good_event_CQ Hab Hb))
  <=
  (((expR (-(fine muLS' * deltaLs ^+ 2) / 2)%R)%:E) +
   ((expR (-(fine muAS' * deltaAs ^+ 2) / 3)%R)%:E))%E)%E.
Proof.
have HLS :
    (((\X_(b - a) P) (~` LS_good_event_CQ Hab Hb))%E
    <=
    (expR (-(fine muLS' * deltaLs ^+ 2) / 2)%R)%:E)%E.
- by rewrite -try3; exact: sampling_ineq3.
have HAS :
    (((\X_(b - a) P) (~` AS_good_event_CQ Hab Hb))%E
    <=
    (expR (-(fine muAS' * deltaAs ^+ 2) / 3)%R)%:E)%E.
- rewrite -try2; apply: sampling_ineq2=>//.
  have : (a < b)%N by done.
  by move/(ltn_sub2r (p:=a))=> /(_ a); rewrite subnn; exact.
exact: leeD.
Qed.


(*Borne inférieure sur la probabilté que le bon événement probabiliste de
  Chain quality (bon événement probabiliste sur les lucky et adversarial
  slots)
  soit réussi sur l'invervalle [a,b) en utilsant encore une fois les borne
    de concentration*)
Theorem CQ_good_event_lower_bound :
  ((1%R%:E -
  ((expR (-(fine muLS' * deltaLs ^+ 2) / 2)%R)%:E) -
  ((expR (-(fine muAS' * deltaAs ^+ 2) / 3)%R)%:E))%E
  <=
  (\X_(b - a)%N P) (CQ_good_event Hab Hb))%E.
Proof.
rewrite union_bound_LS_AS_CQ.
set U := (\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb `|` ~`
    AS_good_event_CQ Hab Hb).
cbv zeta.
rewrite -addeA leeD2l //.
rewrite -oppeD // leeN2.
apply: (le_trans (bad_event_union_bound_CQ Hab Hb)).
rewrite leeD //.
(*    rewrite /LS_good_event_CQ.*)
apply: (le_trans _ (sampling_ineq3 pLs01 (LS_sub Hab Hb) delta_range_Ls)).
- apply: le_measure.
  + rewrite inE -try3 -(ST_Set ([set r | XLS' r <= (1 - deltaLs) * fine muLS'])).
    by apply: (measurable_fun_le (D := setT)).
  + rewrite inE -(ST_Set ([set i | XLS' i <= (1 - deltaLs) * fine muLS'])).
    by apply: (measurable_fun_le (D := setT)).
  + by move=> r; rewrite -try3; exact.
- rewrite -try2.
  have : (a < b)%N by done.
  move/(ltn_sub2r (p:=a))=> /(_ a Hab); rewrite subnn=>?.
  exact: sampling_ineq2.
Qed.

End CQIntervalTrialStats.

 (*the event thatthere is probabilisticly enough lucky slot and less
  adversarial slots is measurable for every subinterval [a,b] where d >= a
  b*)
Lemma measurable_interval_good :
  forall a b , measurable (CQ_interval_good_event a b).
Proof.
move=> a b.
rewrite /CQ_interval_good_event.
case (boolP (a < b)%N)=> Hab;
  last by exact: measurableT.
case (boolP (b <= Sc)%N)=> Hb;
  last by exact: measurableT.
have Hfun := measurable_tuple_interval_index_fun Hab Hb.
have Hgood_event := CQ_good_event_measurable Hab Hb.
have := Hfun measurableT (CQ_good_event Hab Hb) Hgood_event.
by rewrite setTI;
  exact.
Qed.

(*Définition replongeant l'événement CQ_good_event dans son espace sur Sc
  , en y rajoutant la condition
   que ds <= b - a*)
Definition CQ_interval_good_event_d (a b d : nat) : set (Sc.-tuple T) :=
  match boolP (a < b)%N with
  | AltTrue Hab =>
      match boolP (b <= Sc)%N with
      | AltTrue Hb =>
          match boolP (d <= b - a)%N with
          | AltTrue Hd => [set r | CQ_good_event Hab Hb
            (tuple_interval_index_fun r Hab Hb)]
          | _ => setT
          end
      | _ => setT
      end
  | _ => setT
  end.


(*On montre que le l'événement prenant en compte ds <= b - a est
  mesurable*)
Lemma CQ_interval_good_event_d_measurable :
  forall a b d, measurable (CQ_interval_good_event_d a b d).
Proof.
move=> a b d'.
have := measurable_interval_good a b.
rewrite /CQ_interval_good_event_d /CQ_interval_good_event.
case (boolP (a < b)%N)=> // Hab.
case (boolP (b <= Sc)%N)=> // HbSc.
by case (boolP (d' <= b - a)%N).
Qed.

(*événement correspondant  à l'intersection de tout les sous intervalles
  [a,b) qui est
réalisé si pour chaque intervalle admissible , l'événement
  CQ_interval_good_event_d a b d , est réalisé*)
Definition fall_ab_CQ_prob (d : nat) :=
   \bigcap_(a < Sc)
   ( \bigcap_(b < Sc.+1) CQ_interval_good_event_d a b d).

(*l'événement de l'intersection de tout les sous intervalles est
  mesurable*)
Lemma  fall_ab_CQ_prob_measurable d':
  measurable (fall_ab_CQ_prob d').
Proof.
apply: bigcap_measurable;
  first by (exists (Ordinal n_sup_O)).
move=> k Hk.
apply: bigcap_measurable;
  first by (exists 0).
move=> k' H'.
exact: CQ_interval_good_event_d_measurable.
Qed.


(*Preuve non finie de l'implication entre fall_ab_CQ_prob et
  CQ_slot_advantage qui dénote que pour tout sous intervalle on a un
  avantage honnete*)
Lemma fall_ab_CQ_prob_implies_CQ_slot_advantage_all  :
  fall_ab_CQ_prob ds r_cq
  -> CQ_slot_advantage w_cq ds.
Proof.
rewrite /fall_ab_CQ_prob.
move=> + a b Hab Hb Hds.
have HaSc : (a < Sc)%N.
  apply: (ltn_leq_trans Hab Hb).
have HbSc : (b < Sc.+1)%N.
  by rewrite (ltnS b Sc).
pose ia := Ordinal HaSc.
pose ib := Ordinal HbSc.
(*rewrite -(ler_nat R).*)
(*rewrite -(Ls_r_range_link Hab Hb). *)
(*Search ( (_ + _ )%:R = (_ : R) + (_ : R)). *)
(*rewrite (natrD R (| adv_slots_range a b |) w_cq). *)
(*rewrite-(As_r_range_link Hab Hb). *)
rewrite /bigcap /=.
(*rewrite *)
(*specialize (Hfp a b )*)
Abort.
(*t*)
End ChainQuality.

(* ==================================================================== *)
(* Common Prefix                                                        *)
(* ==================================================================== *)

Section CommonPrefix.

Variables (N N' : GlobalState).
Hypothesis N_from_initial : N0 ⇓ N .
Hypothesis N'_from_N :  N ⇓^+ N'.
Hypothesis N'_is_forgin_free : forging_free N'.
Hypothesis N'_is_collision_free : collision_free N'.
Hypothesis N'_now_is_Sc : (t_now N' = Sc)%N.
(*party assumptions corresponding to CG assumptions for now*)
Variables (p1 p2 : Party).
Hypothesis p1_honest : is_honest p1.
Hypothesis p2_honest : is_honest p2.

(*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
Variable (l1 l2 : LocalState).
Hypothesis l1_p1_state : has_state p1 N l1.
Hypothesis l2_p2_state : has_state p2 N' l2.

Variables (k : nat).

Variable epsilon : R.

(*Lemme qui permet de verifier que si on à l'esperance de superslots
  superieure a 2 fois l'esperance d'adversarial
   , alors , si le nombre compté par le modèle probabiliste de super slot
     est plus grand que son esperance, et que le nombre
   d'adversarial slots est inférieur à son esperance, alors on peut en
     déduire par transitivité que le nombre
   de super slot est supérieur a 2 fois le nombre d'adversarial slots*)
Lemma SS_gt_2AS :
  ( ((1 + deltaAs) * fine muAS) *+ 2) < (1 - deltaSs) * fine muSS ->
  forall r,
    (1 + deltaAs) * fine muAS > AS_r r ->
    ((1 - deltaSs) * fine muSS) < SS_r r ->
    (SS_r r> (AS_r r) *+ 2).
Proof.
move=> H1 r H11 H12.
have H112T : AS_r r *+ 2< ((1 + deltaAs) * fine muAS) *+ 2
  by apply: (ltr_wpMn2r (n:=2)).
apply: (lt_trans H112T).
exact: (lt_trans H1).
Qed.


(*lemme d'isolation de epsilon à gaiche de l'inéquation, le calcul est
  retrouvable dans le papier*)
Lemma epsilon_condition_CP :
  (1 - deltaSs) * ((pAs *+ 2) + epsilon) >
  (1 + deltaAs) * (pAs *+ 2) <->
  epsilon > (((1 + deltaAs) / (1 - deltaSs)) - 1) * (pAs *+ 2).
Proof.
split.
- rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon))
          -(ltr_pdivrMr (pAs *+ 2 + epsilon)).
    by rewrite subr_gt0; move/andP : delta_range_Ss; case.
  rewrite (mulrC (1 + deltaAs)) (mulrC (pAs *+ 2))=>H.
  rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA
          (mulrC ((1 - deltaSs)^-1))  mulrA.
  exact: H.
- rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA
          (mulrC ((1 - deltaSs)^-1)) mulrA=> H.
  rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon))
          -(ltr_pdivrMr (pAs *+ 2 + epsilon)).
    by rewrite subr_gt0; move/andP : delta_range_Ss; case.
  exact: H.
Qed.

(*Bon événenement probabiliste sur le nombre de superslots*)
Definition SS_good_event :=
  [set r | (1 - deltaSs) * fine muSS < XSS r].

(*mesurabilité du bon événement probabiliste sur le nombre de super
  slots*)
Lemma SS_measurable_good_event_CP :
  measurable SS_good_event.
Proof.
rewrite /SS_good_event.
set B := (1 - deltaSs) * fine muSS.
rewrite set_lt_eq_neg_le; apply: measurableC.
rewrite -(ST_Set [set r | XSS r <= B]).
by apply: (measurable_fun_le (D := setT) (f := XSS) (g := fun _ => B)).
Qed.


(*bon événement probabiliste sur le nombre d'adversarial slots*)
Definition AS_good_event_CP :=
  [set r | (1 + deltaAs) * fine muAS > XAS r].

(*mesurabilité du bon événement probabiliste sur le nombre d'adversarial
  slots*)
Lemma AS_measurable_good_event_CP :
  measurable AS_good_event_CP.
Proof.
rewrite /AS_good_event_CP.
set B := (1 + deltaAs) * fine muAS.
rewrite set_lt_as_compl_ge.
have -> : [set r | ~~ (B <= XAS r)] = ~` [set r | B <= XAS r]
  by apply/seteqP; split=> r /= /negP; exact.
apply: measurableC.
rewrite -(ST_Set ([set r | B <= XAS r])).
by apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g := XAS)).
Qed.


(*Intersection entre les deux bons événements probabilistes*)
Definition CP_good_event :=
  SS_good_event `&` AS_good_event_CP.

(*réecriture d'une union sous sa forme complémentaire (1 - union des deux
  événement complémentaires)*)
Lemma union_bound_SS_AS_CP :
  (\X_Sc P) (SS_good_event `&` AS_good_event_CP)
  =
  (1%R%:E - (\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP)))%E.
Proof.
rewrite -probability_setC.
- apply: measurableU; apply: measurableC.
  + exact: SS_measurable_good_event_CP.
  + exact: AS_measurable_good_event_CP.
- congr ((\X_Sc P) _).
  apply/seteqP; split=> [r [??] [] | r H] //.
  by split; apply: Classical_Prop.NNPP=> ?; apply: H; [ left | right ].
Qed.

(* ------------------------------------------------------------------ *)
(* Interval model used by timed common prefix                          *)
(* ------------------------------------------------------------------ *)

Lemma b_le_t_now_N2_implies_b_le_SC (b : nat):
  (b <= t_now N')%N -> (b <= Sc)%N.
Proof. by rewrite N'_now_is_Sc. Qed.

Lemma sub1_leq (a b : nat):
  (a <= b)%N -> ((a - 1) <= b)%N.
Proof.
have : ((a - 1) <= a)%N
  by exact: leq_subr.
exact: leq_trans.
Qed.


(*Hypothèses de liaison sur le nombre de super et adversarial slots entre
  le protocole et le modèle probabiliste
sur un intervalle [a,b)*)
Hypothesis Ss_r_range_link :
  forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
         (r : Sc.-tuple T),
    bool_trial_value (SS_sub Hab Hb)
      (tuple_interval_index_fun r Hab Hb)
    = | super_slots_range a b |%:R.

Hypothesis As_r_range_link_CP :
  forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
         (r : Sc.-tuple T),
    bool_trial_value (AS_sub Hab Hb)
      (tuple_interval_index_fun r Hab Hb)
    = | adv_slots_range a b |%:R.

(*réécriture du bon événement bon événement probabiliste pour Common
  Prefix sur un intervalle [a,b) donné*)
Definition CP_good_event_interval
   (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :=
  [set r : Sc.-tuple T |
    ((bool_trial_value (AS_sub Hab Hb)
        (tuple_interval_index_fun r Hab Hb)) *+ 2
     < bool_trial_value (SS_sub Hab Hb)
        (tuple_interval_index_fun r Hab Hb))%R].

(*réécriture sous forme (match with) pour avoir des preuves plus simples*)
Definition CP_good_event_interval' (a b : nat)  :=
  match boolP (a < b)%N with
  | AltTrue Hab =>
      match boolP (b <= Sc)%N with
      | AltTrue Hb => CP_good_event_interval Hab Hb
      | _ => setT
      end
  | _ => setT
  end.

(*événment du protocole qu'il y ait plus de super slots que 2 fois le
  nombre d'adversarial slots sur un intervale [a,b)*)
Definition interval_advantage_CP (a b : nat) : Prop :=
  ((((| adv_slots_range a b |)%:R : R) *+ 2
      < ((| super_slots_range a b |)%:R : R)))%R.

(*événement du protocole qui dénote la précondition quantitative (mais
  probabiliste car on untilise CP_good_event_intervalle)
   sur le nombre de slots de timed_common_prefix, il contient un forall ce
     qui pourra rendre les preuves de mesurabilité et
   d'implication compliquées , un passage à un événement de la forme
     bigcap serait probablement bénéfique
*)
Definition CP_good_event_set : set (Sc.-tuple T) :=
  [set r : Sc.-tuple T |
    forall (t1 t2 : nat)
           (Htk : (t1 <= k)%N)
           (Ht2 : (t_now N <= t2 <= t_now N')%N)
           (Ht1t2 : ((t1 + 1) < (t2 - 1))%N)
           (Ht2Sc : ((t2 - 1) <= Sc)%N),
      CP_good_event_interval Ht1t2 Ht2Sc r
  ].

(*Lemme d'implication entre la partie probabiliste et la partie protocole
  sur un intervalle fixé*)
Lemma CP_good_interval_implies_advantage
    (a b : nat) (r : Sc.-tuple T)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
  CP_good_event_interval Hab Hb r -> interval_advantage_CP a b.
Proof.
move=> H.
by rewrite /interval_advantage_CP -(Ss_r_range_link Hab Hb r)
          -(As_r_range_link_CP Hab Hb r).
Qed.
(*
(*Lemme non fini d'implication entre le bon événement probabiliste sur
  tout les intervales , vers l'événement du protocole qui dénote
la précondition quantitative de Common Prefix*)
Lemma CP_good_event_implies_TCP (r : Sc.-tuple T) :
  CP_good_event_set r -> TCP_Good_event k.
Proof.
  move => H.
  apply  timed_common_prefix' with (p1 := p1) (p2 := p2) ; try easy.
  rewrite /CP_good_event_set //= in H.
  move => t0 t3 Ht0 Ht3.

  have Ht0t3 : ((t0 - 1) < (t3 - 1))%N.
  {

  }

  have Ht3sc : ((t3 - 1) <= Sc)%N.
  {
    case /andP : Ht3 =>  Ht31 Hr32.
    rewrite N'_now_is_Sc in Hr32.
    have Ht3't3 : (t3 - 1 <= t3)%N.
    {
      by rewrite sub1_leq.
    }
    apply (leq_trans  Ht3't3 Hr32).
  }

  eapply H.
Abort.
 *)

(*inégalité de boole sur les deux événements complémentaire transformant
  ainsi l'union en un addition*)
Lemma bad_event_union_bound_CP :
  ((\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP))%E
   <=
  ((\X_Sc P) (~` SS_good_event)) + ((\X_Sc P) (~` AS_good_event_CP)))%E.
Proof.
apply: measureU2 ; apply: measurableC.
- exact: SS_measurable_good_event_CP.
- exact: AS_measurable_good_event_CP.
Qed.

(*Borne inférieure sur la prorbabilité qu'on ait sur Sc
  l'intersection des deux bons événements proabbilistes*)
Theorem CP_good_event_lower_bound :
  ((1%R%:E -
  ((expR (-(fine muSS * deltaSs ^+ 2) / 2)%R)%:E) -
  ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E
  <=
  (\X_Sc P) CP_good_event)%E.
Proof.
rewrite union_bound_SS_AS_CP.
set U := (\X_Sc P) (~` SS_good_event `|` ~` AS_good_event_CP).
cbv zeta.
rewrite -addeA leeD2l // -oppeD // leeN2.
apply (le_trans bad_event_union_bound_CP).
rewrite leeD //.
- apply: (le_trans _ (sampling_ineq3 pSs01 SS delta_range_Ss)).
  apply: le_measure;
    last by move=>?; rewrite -try3; exact.
  + rewrite inE -try3 -(ST_Set ([set r | XSS r <= (1 - deltaSs) * fine muSS])).
    by apply: (measurable_fun_le (D := setT)).
  + rewrite inE -(ST_Set ([set i | XSS i <= (1 - deltaSs) * fine muSS])).
    by apply: (measurable_fun_le (D := setT)).
- by rewrite -try2; exact: sampling_ineq2.
Qed.
End CommonPrefix.
End PoSProbabilityBounds.
