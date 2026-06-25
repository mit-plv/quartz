From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind Constructor. Set Default Proof Mode "Classic".
From Coq Require Import BinInt String.
Require Import quartz.lang.Syntax. Import type.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.lang.Processor.


Import (notations) type expr eexpr.

Local Open Scope string_scope.
Import fn.

Definition bht_4_32 {var} : @Bht var 32 (@bht.State 4) := @bht.impl 4 32 var.

Definition bht_update {var} := @bht.update 4 32 var.
Definition bht_ppcDp {var} := @bht.ppcDp 4 32 var.

Definition test_bht_processor_inner {var} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st := #p .1 in
  let pc := #p .2 .1 in
  let target := #p .2 .2 in

  let st_updated := $(expr.Call (@bht_update var) (expr.Binop binop.MkPair (expr.Var st) (expr.Binop binop.MkPair (expr.Var pc) expr.true))) in
  let next_pc := $(expr.Call (@bht_ppcDp var) (expr.Var p)) in
  return (#st_updated, #next_pc)
)).

Definition test_bht_processor {var fn} :=
  fns.package_global_fns'' var fn (@test_bht_processor_inner).

Lemma interp_test_bht_processor :
  fns.interp test_bht_processor = fn.interp (@test_bht_processor_inner type.interp).
Proof.  trivial.  Qed.
