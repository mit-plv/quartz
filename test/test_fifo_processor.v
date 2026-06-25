From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind Constructor. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt BinNat String.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.examples.Processor.
Import InterfaceExample.


Import (coercions) domain.BV.
Import (notations) type expr eexpr.

Local Open Scope string_scope.
Local Open Scope N_scope.
Import fn.

Definition fifo_Bits8 {var} : @Fifo var (fifo1.State (type.Bits 8)) (type.Bits 8) := @fifo1.impl (type.Bits 8) var.

Definition fifo_first {var} := @fifo1.first (type.Bits 8) var.
Definition fifo_empty {var} := @fifo1.empty (type.Bits 8) var.
Definition fifo_full {var} := @fifo1.full (type.Bits 8) var.
Definition fifo_enq {var} := @fifo1.enq (type.Bits 8) var.
Definition fifo_deq {var} := @fifo1.deq (type.Bits 8) var.

Definition test_fifo_processor_inner {var : type -> Type} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st := #p .1 in
  let is_empty := $(expr.Call (@fifo_empty var) (expr.Var st)) in
  let is_full := $(expr.Call (@fifo_full var) (expr.Var st)) in
  let first_val := $(expr.Call (@fifo_first var) (expr.Var st)) in
  let st_enqed := $(expr.Call (@fifo_enq var) (expr.Var p)) in
  let st_deqed := $(expr.Call (@fifo_deq var) (expr.Var st)) in
  return (#is_empty, #is_full, #first_val, #st_enqed, #st_deqed)
)).

Print test_fifo_processor_inner.
Print fifo_enq.

Definition test_fifo_processor {var : type -> Type} {f : type -> type -> Type} :
  fns.fns var f
    (type.Pair (fifo1.State (type.Bits 8)) (type.Bits 8))
    (type.Pair (type.Pair (type.Pair (type.Pair type.Bool type.Bool) (type.Bits 8)) (fifo1.State (type.Bits 8))) (fifo1.State (type.Bits 8))) :=
  fns.package_global_fns'' var f (@test_fifo_processor_inner).

Lemma interp_test_fifo_processor :
  fns.interp test_fifo_processor = fn.interp (@test_fifo_processor_inner type.interp).
Proof. exact eq_refl. Qed.
