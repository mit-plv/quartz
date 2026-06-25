From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind Constructor. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import type.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.lang.Processor.


Import (coercions) domain.Zmod.
Import (notations) type expr eexpr.

Local Open Scope string_scope.
Import fn.

Definition rf_Bits8 {var} := @rfScored.impl 2 (type.Bits 8) var.

Definition rf_acquire {var} := @rfScored.acquireLock 2 (type.Bits 8) var.
Definition rf_release {var} := @rfScored.releaseLock 2 (type.Bits 8) var.
Definition rf_write {var} := @rfScored.writeAndRelease 2 (type.Bits 8) var.
Definition rf_read {var} := @rfScored.read 2 (type.Bits 8) var.
Definition rf_isLocked {var} := @rfScored.isLocked 2 (type.Bits 8) var.

Definition test_rfscored_processor_inner {var} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st := #p .1 in
  let idx := #p .2 in
  let is_locked := $(expr.Call (@rf_isLocked var) (expr.Var p)) in
  let read_val := $(expr.Call (@rf_read var) (expr.Var p)) in
  let st_acquired := $(expr.Call (@rf_acquire var) (expr.Var p)) in
  let st_released := $(expr.Call (@rf_release var) (expr.Var p)) in
  let st_written := $(expr.Call (@rf_write var) (expr.Binop binop.MkPair (expr.Var st) (expr.Binop binop.MkPair (expr.Var idx) (expr.Const (t:=type.Bits 8) (Zmod.of_Z _ 42))))) in
  return (#is_locked, #read_val, #st_acquired, #st_released, #st_written)
)).

Definition test_rfscored_processor {var fn} :=
  fns.package_global_fns'' var fn (@test_rfscored_processor_inner).

Lemma interp_test_rfscored_processor :
  fns.interp test_rfscored_processor = fn.interp (@test_rfscored_processor_inner type.interp).
Proof. exact eq_refl. Qed.
