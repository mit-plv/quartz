From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind Constructor. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt String.
Require Import quartz.lang.Syntax. Import type.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.lang.Processor.


Import (notations) type expr eexpr.

Local Open Scope string_scope.
Import fn.

Definition btb_32_16_8 {var} : @Btb var 32 (@btb.State 32 16 8) := @btb.impl 32 16 8 var.

Definition btb_update {var} := @btb.update 32 16 8 var.
Definition btb_predPc {var} := @btb.predPc 32 16 8 var.

Definition test_btb_processor_inner {var} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st := #p .1 in
  let pc := #p .2 .1 in
  let next_pc := #p .2 .2 in

  let st_updated := $(expr.Call (@btb_update var) (expr.Binop binop.MkPair (expr.Var st) (expr.Binop binop.MkPair (expr.Var pc) (expr.Var next_pc)))) in
  let predicted_pc := $(expr.Call (@btb_predPc var) (expr.Binop binop.MkPair (expr.Var st) (expr.Var pc))) in
  return (#st_updated, #predicted_pc)
)).

Definition test_btb_processor {var fn} :=
  fns.package_global_fns'' var fn (@test_btb_processor_inner).

Lemma interp_test_btb_processor :
  fns.interp test_btb_processor = fn.interp (@test_btb_processor_inner type.interp).
Proof.  trivial.  Qed.
