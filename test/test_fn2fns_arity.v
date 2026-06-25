From Stdlib Require Import BinInt BinNat String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope N_scope.

Definition inner_extract {var} : fn.fn var (Bits 32) (Bits 12) :=
  @fn.Fn var _ _ (fun inst => eexpr.Ret (expr.Unop unop.UnsignedResize (expr.Var inst))).

Definition test_fn2fns_arity_inner {var} := @fn.Fn var _ _ (fun inst => quartz_eexpr:(
  let extracted := $(expr.Call (@inner_extract var) (expr.Var inst)) in
  return #extracted
)).

Definition test_fn2fns_arity {var fn} :=
  fns.package_global_fns'' var fn (@test_fn2fns_arity_inner).

Lemma interp_test_fn2fns_arity :
  fns.interp test_fn2fns_arity = fn.interp (@test_fn2fns_arity_inner type.interp).
Proof. exact eq_refl. Qed.
