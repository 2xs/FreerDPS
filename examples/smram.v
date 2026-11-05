(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* CLAUDE: new file.  Port of FreeSpec's examples/smram.v (lthms/FreeSpec
   d4e2f3a), the example which uses [derive_semantics].  Changes: the
   [Parameters] are section variables; [StrictProvide3] becomes
   [DRAM ;; STORE bool -<< Fx] plus [VGA -< Fx] and two [Distinguish]
   instances; the inductive callee obligations are written as functions;
   witnesses are point masses, as everywhere in FreerDPS. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
From mathcomp Require Import boolp reals Rstruct.
From infotheo Require Import fsdist.
From monae Require Import hierarchy.
From FreerDPS Require Import all_freerdps.

Local Abbreviation R := Rdefinitions.R.

Local Open Scope contract_scope.

(** This library introduces the starting point of the FreeSpec framework,
    that is the original example that has motivated everything else. *)

(** * The Verification Problem *)

(** We model a small subset of a x86 architecture, where a Memory Controller
    (now integrated inside the CPU) receives memory accesses from cores, and
    dispatches these accesses to different controllers.  In our case, we only
    consider the DRAM and VGA controllers.

    From a FreeSpec perspective, we therefore consider three components and
    as many effects, with the memory controller exposing its own effect and
    relying on the effects of the two other controllers.

    The DRAM contains a special-purpose memory region called the SMRAM,
    dedicated to the x86 System Management Mode (SMM).  It is expected that
    only a CPU in SMM can access the SMRAM.  The CPU sets a dedicated pin
    (SMIACT) when it is in SMM, for the Memory Controller to know. *)

(** * Specifying the Subsystem *)

(** The overview of the system we want to model is the following:

<<
             |
             |
             v
      -----------------
     +-----------------+
     |Memory Controller|
     +-----------------+
       |            |
       |            |
       v            v
 ----------     ----------
+----------+   +----------+
|   DRAM   |   |   VGA    |
|Controller|   |Controller|
+----------+   +----------+
>>
    We will focus on the Memory Controller, and only model the effects of the
    DRAM and VGA controllers. *)

Section smram.

(** ** Addressing Memories *)

(** We leave how the memory is actually addressed (in terms of memory cell
    addresses and contents) as a parameter of the model. *)

Variables (address cell : Type)
  (address_eq : address -> address -> Prop)
  (address_eq_dec : forall addr addr' : address,
    {address_eq addr addr'} + {~ address_eq addr addr'})
  (in_smram : address -> bool)
  (in_smram_morphism : forall addr addr' : address,
    address_eq addr addr' -> in_smram addr = in_smram addr').

(** ** VGA and DRAM Controllers *)

(** We consider that the DRAM and VGA controllers expose the same effect
    which allows for reading from and writing to memory cells. *)

Inductive MEMORY : effect :=
| ReadFrom (addr : address) : MEMORY cell
| WriteTo (addr : address) (value : cell) : MEMORY unit.

Inductive DRAM : effect :=
| MakeDRAM {A : Type} (cmd : MEMORY A) : DRAM A.

Inductive VGA : effect :=
| MakeVGA {A : Type} (cmd : MEMORY A) : VGA A.

Section memory_programs.
Context {Fx : effect} {M : freerMonad Fx}.

Definition dram_read_from `{DRAM -< Fx} (addr : address) : M cell :=
  ptrigger (MakeDRAM (ReadFrom addr)).

Definition dram_write_to `{DRAM -< Fx} (addr : address) (val : cell) :
    M unit :=
  ptrigger (MakeDRAM (WriteTo addr val)).

Definition vga_read_from `{VGA -< Fx} (addr : address) : M cell :=
  ptrigger (MakeVGA (ReadFrom addr)).

Definition vga_write_to `{VGA -< Fx} (addr : address) (val : cell) :
    M unit :=
  ptrigger (MakeVGA (WriteTo addr val)).

End memory_programs.

(** ** Memory Controller *)

Inductive smiact := smiact_set | smiact_unset.

Inductive MEMORY_CONTROLLER : effect :=
| Read (pin : smiact) (addr : address) : MEMORY_CONTROLLER cell
| Write (pin : smiact) (addr : address) (value : cell) :
    MEMORY_CONTROLLER unit.

Section memory_controller.
Context {Fx : effect} `{DRAM ;; STORE bool -<< Fx} `{VGA -< Fx}
  {M : freerMonad Fx}.

Definition dispatch {A : Type} (addr : address)
    (unpriv priv : address -> M A) : M A :=
  iget >>= fun reg => if reg && in_smram addr then unpriv addr else priv addr.

Definition memory_controller : component (M := M) MEMORY_CONTROLLER Fx :=
  fun _ op =>
    match op with

(** When SMIACT is set, the CPU is in SMM.  According to its specification,
    the Memory Controller can simply forward the memory access to the
    DRAM. *)

    | Read smiact_set addr => dram_read_from addr
    | Write smiact_set addr val => dram_write_to addr val

(** On the contrary, when the SMIACT is not set, the CPU is not in SMM.  As
    a consequence, the memory controller implements a dedicated access
    control mechanism.  If the requested address belongs to the SMRAM and if
    the SMRAM lock has been set, then the memory access is forwarded to the
    VGA.  Otherwise, it is forwarded to the DRAM by default.  This is
    specified in the [dispatch] function. *)

    | Read smiact_unset addr => dispatch addr vga_read_from dram_read_from
    | Write smiact_unset addr val =>
        dispatch addr (fun x => vga_write_to x val)
          (fun x => dram_write_to x val)
    end.

End memory_controller.

(** * Verifying our Subsystem *)

(** ** Memory View *)

Definition memory_view : Type := address -> cell.

HB.instance Definition _ := gen_eqMixin memory_view.
HB.instance Definition _ := gen_choiceMixin memory_view.

Definition update_memory_view_address (view : memory_view) (addr : address)
    (content : cell) : memory_view :=
  fun addr' => if address_eq_dec addr addr' then content else view addr'.

(** ** Specification *)

(** *** DRAM Controller Specification *)

Definition update_dram_view (view : memory_view) (A : Type) (cmd : DRAM A)
    (_ : A) : memory_view :=
  match cmd with
  | MakeDRAM _ (WriteTo addr val) => update_memory_view_address view addr val
  | _ => view
  end.
Arguments update_dram_view view [A] cmd _.

Definition dram_promise (view : memory_view) (A : Type) (cmd : DRAM A) :
    A -> Prop :=
  match cmd in DRAM A return A -> Prop with
  | MakeDRAM _ cmd =>
      match cmd in MEMORY A return A -> Prop with
      | ReadFrom addr => fun val => val = view addr
      | WriteTo _ _ => fun _ => True
      end
  end.
Arguments dram_promise view [A] cmd _.

Definition dram_specs : contract R DRAM memory_view :=
  make_det_contract update_dram_view no_requirement dram_promise.

(** *** Memory Controller Specification *)

Definition update_memory_controller_view (view : memory_view) (A : Type)
    (cmd : MEMORY_CONTROLLER A) (_ : A) : memory_view :=
  match cmd with
  | Write smiact_set addr val => update_memory_view_address view addr val
  | _ => view
  end.
Arguments update_memory_controller_view view [A] cmd _.

Definition memory_controller_promise (view : memory_view) (A : Type)
    (cmd : MEMORY_CONTROLLER A) : A -> Prop :=
  match cmd in MEMORY_CONTROLLER A return A -> Prop with
  | Read pin addr => fun content =>
      pin = smiact_set -> in_smram addr = true -> view addr = content
  | Write _ _ _ => fun _ => True
  end.
Arguments memory_controller_promise view [A] cmd _.

Definition mc_specs : contract R MEMORY_CONTROLLER memory_view :=
  make_det_contract update_memory_controller_view no_requirement
    memory_controller_promise.

(** ** Main Theorem *)

(** The view of the memory controller and the view of the DRAM agree on the
    SMRAM, and the SMRAM lock is set. *)

Definition smram_pred (view_mc : memory_view)
    (view_mem : memory_view * bool) : Prop :=
  view_mem.2 = true /\
  forall addr, in_smram addr = true -> view_mc addr = view_mem.1 addr.

Section memory_controller_correct.
Context {Fx : effect} {mem : DRAM ;; STORE bool -<< Fx} {vga : VGA -< Fx}.
Context {vga_dram : @Distinguish Fx VGA DRAM vga mem.(p1).(may_prov)}.
Context {vga_store : @Distinguish Fx VGA (STORE bool) vga mem.(p2).(may_prov)}.
Context {M : inductiveFreerMonad Fx}.

Local Abbreviation mem_specs :=
  (dram_specs -*- store_specs R bool : contract R Fx (memory_view * bool)).

(** Each primitive, run from a point mass. *)

Lemma dram_trigger_pre {A : Type} (cmd : DRAM A) (view : memory_view)
    (lock : bool) :
  pre (mem_specs |~ (ptrigger cmd : M A)) (fsdist1 (view, lock)).
Proof.
rewrite to_hoare_triggerE /=; apply/contractprod_requirement1.
split; last exact: distinguished_caller.
by rewrite provided_callerP; exists view.
Qed.

Lemma dram_trigger_post {A : Type} (cmd : DRAM A) (view : memory_view)
    (lock : bool) (x : A) (d : R.-dist (memory_view * bool)) :
  post (mem_specs |~ (ptrigger cmd : M A)) (fsdist1 (view, lock)) x d ->
  d = fsdist1 (update_dram_view view cmd x, lock) /\ dram_promise view cmd x.
Proof.
rewrite to_hoare_triggerE /= => -[->] /contractprod_promise1 [].
rewrite /gen_promise injK_Some => -[_ [/fsdist1_inj <- promise_x]] _.
split=> //.
rewrite /gen_state_update /= fsdist1bind /gen_state_update injK_Some injK_None.
by rewrite /= !fsdist1bind dist_pair1.
Qed.

Lemma vga_trigger_pre {A : Type} (cmd : VGA A) (view : memory_view)
    (lock : bool) :
  pre (mem_specs |~ (ptrigger cmd : M A)) (fsdist1 (view, lock)).
Proof.
rewrite to_hoare_triggerE /=; apply/contractprod_requirement1.
by split; exact: distinguished_caller.
Qed.

Lemma vga_trigger_post {A : Type} (cmd : VGA A) (view : memory_view)
    (lock : bool) (x : A) (d : R.-dist (memory_view * bool)) :
  post (mem_specs |~ (ptrigger cmd : M A)) (fsdist1 (view, lock)) x d ->
  d = fsdist1 (view, lock).
Proof.
rewrite to_hoare_triggerE /= => -[-> _].
by rewrite /gen_state_update /= fsdist1bind /gen_state_update !injK_None
  dist_pair1.
Qed.

Lemma get_lock_pre (view : memory_view) (lock : bool) :
  pre (mem_specs |~ (iget : M bool)) (fsdist1 (view, lock)).
Proof.
rewrite to_hoare_triggerE /=; apply/contractprod_requirement1.
split; first exact: distinguished_caller.
by rewrite provided_callerP; exists lock.
Qed.

Lemma get_lock_post (view : memory_view) (lock reg : bool)
    (d : R.-dist (memory_view * bool)) :
  post (mem_specs |~ (iget : M bool)) (fsdist1 (view, lock)) reg d ->
  reg = lock /\ d = fsdist1 (view, lock).
Proof.
rewrite to_hoare_triggerE /= => -[->] /contractprod_promise1 [_].
rewrite /gen_promise injK_Some => -[_ [/fsdist1_inj <- <-]].
split=> //.
rewrite /gen_state_update /= fsdist1bind /gen_state_update injK_None.
by rewrite injK_Some /= !fsdist1bind dist_pair1.
Qed.

Local Abbreviation smram_inv d_mc d_mem :=
  (exists view_mc view_mem,
    d_mc = fsdist1 view_mc /\ d_mem = fsdist1 view_mem /\
    smram_pred view_mc view_mem).

Lemma memory_controller_correct_component :
  correct_component (memory_controller (M := M)) mc_specs mem_specs
    (fun d_mc d_mem => smram_inv d_mc d_mem).
Proof.
move=> _ _ [view_mc [[view lock] [-> [-> [/= -> agree]]]]] A cmd _.
case: cmd=> [[] addr | [] addr val] /=.
- split; first exact: dram_trigger_pre.
  move=> x d /(dram_trigger_post (MakeDRAM (ReadFrom addr))) [-> /= ->].
  rewrite !fsdist1bind; split; first by exists view_mc; split=> // _ /agree.
  by exists view_mc, (view, true).
- split.
    rewrite freer_to_hoare_bindE; split; first exact: get_lock_pre.
    move=> reg d /get_lock_post [-> ->] /=.
    case: (in_smram addr); first exact: vga_trigger_pre.
    exact: dram_trigger_pre.
  rewrite freer_to_hoare_bindE=> x d' [reg [d [/get_lock_post [-> ->] post_k]]].
  rewrite !fsdist1bind; split; first by exists view_mc; split=> // -[].
  move: post_k => /=; case: (in_smram addr).
    move/(vga_trigger_post (MakeVGA (ReadFrom addr)))=> ->.
    by exists view_mc, (view, true).
  move/(dram_trigger_post (MakeDRAM (ReadFrom addr)))=> [-> _].
  by exists view_mc, (view, true).
- split; first exact: dram_trigger_pre.
  move=> x d /(dram_trigger_post (MakeDRAM (WriteTo addr val))) [-> _].
  rewrite !fsdist1bind; split; first by exists view_mc.
  exists (update_memory_view_address view_mc addr val).
  exists (update_memory_view_address view addr val, true).
  do 3!split=> //.
  move=> addr' /agree; rewrite /update_memory_view_address /=.
  by case: address_eq_dec.
split.
  rewrite freer_to_hoare_bindE; split; first exact: get_lock_pre.
  move=> reg d /get_lock_post [-> ->] /=.
  case: (in_smram addr); first exact: vga_trigger_pre.
  exact: dram_trigger_pre.
rewrite freer_to_hoare_bindE=> x d' [reg [d [/get_lock_post [-> ->] post_k]]].
rewrite !fsdist1bind; split; first by exists view_mc.
move: post_k => /=; case smram_addr: (in_smram addr).
  move/(vga_trigger_post (MakeVGA (WriteTo addr val)))=> ->.
  by exists view_mc, (view, true).
move/(dram_trigger_post (MakeDRAM (WriteTo addr val)))=> [-> _].
exists view_mc, (update_memory_view_address view addr val, true).
do 3!split=> //.
move=> addr' smram_addr'; rewrite /update_memory_view_address /=.
case: (address_eq_dec addr addr')=> [same_addr | diff_addr] /=.
  by move: smram_addr; rewrite (in_smram_morphism _ _ same_addr) smram_addr'.
exact: agree.
Qed.

Theorem memory_controller_correct (view : memory_view) (sem : semantics Fx)
    (comp : compliant_semantics mem_specs (fsdist1 (view, true)) sem) :
  compliant_semantics mc_specs (fsdist1 view)
    (derive_semantics (memory_controller (M := M)) sem).
Proof.
apply: correct_component_derives_compliant_semantics comp.
  exact: memory_controller_correct_component.
by exists view, (view, true).
Qed.

End memory_controller_correct.

End smram.
