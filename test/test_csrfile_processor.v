From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind Constructor. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt BinNat String.
Require Import quartz.lang.Syntax. Import type.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.examples.Processor.
Import InterfaceExample.
Local Open Scope N_scope.


Import (notations) type expr eexpr.

Local Open Scope string_scope.
Import fn.

Definition csrfile_32_12 {var} : @CsrFile var 12 32 (@csrFile.State) := @csrFile.impl var.

Definition csrfile_readCsr {var} := @csrFile.readCsr var.
Definition csrfile_writeCsr {var} := @csrFile.writeCsr var.


Definition test_csrfile_processor_inner {var} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st := #p .1 in
  let csr := #p .2 .1 in
  let val := #p .2 .2 in

  let st_updated := $(expr.Call (@csrfile_writeCsr var) (expr.Binop binop.MkPair (expr.Var st) (expr.Binop binop.MkPair (expr.Var csr) (expr.Var val)))) in
  let read_val := $(expr.Call (@csrfile_readCsr var) (expr.Binop binop.MkPair (expr.Var st_updated) (expr.Var csr))) in
  return (#st_updated, #read_val)
)).

Definition test_csrfile_processor {var fn} :=
  fns.package_global_fns'' var fn (@test_csrfile_processor_inner).

Lemma interp_test_csrfile_processor :
  fns.interp test_csrfile_processor = fn.interp (@test_csrfile_processor_inner type.interp).
Proof.  trivial.  Qed.
