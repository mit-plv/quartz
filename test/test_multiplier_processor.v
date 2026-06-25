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

Definition mul_Bits64 {var} : @Multiplier var 32 (@multiplier.Req) (@multiplier.State 4) := @multiplier.impl 4 var.

Definition mul_peek {var} := @multiplier.peek 4 var.
Definition mul_full {var} := @multiplier.full 4 var.
Definition mul_ready {var} := @multiplier.respReady 4 var.
Definition mul_enq {var} := @multiplier.enq 4 var.
Definition mul_deq {var} := @multiplier.deq 4 var.
Definition mul_tick {var} := @multiplier.tick 4 var.

Definition test_multiplier_processor_inner {var} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st := #p .1 in
  let req := #p .2 in
  let is_full := $(expr.Call (@mul_full var) (expr.Var st)) in
  let is_ready := $(expr.Call (@mul_ready var) (expr.Var st)) in
  let peek_val := $(expr.Call (@mul_peek var) (expr.Var st)) in
  let st_enqed := $(expr.Call (@mul_enq var) (expr.Var p)) in
  let st_deqed := $(expr.Call (@mul_deq var) (expr.Var st)) in
  let st_ticked := $(expr.Call (@mul_tick var) (expr.Var st)) in
  return (#is_full, #is_ready, #peek_val, #st_enqed, #st_deqed, #st_ticked)
)).

Definition test_multiplier_processor {var fn} :=
  fns.package_global_fns'' var fn (@test_multiplier_processor_inner).

Lemma interp_test_multiplier_processor :
  fns.interp test_multiplier_processor = fn.interp (@test_multiplier_processor_inner type.interp).
Proof. exact eq_refl. Qed.
