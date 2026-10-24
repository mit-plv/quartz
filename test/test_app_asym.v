From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_app_asym_inner {var} := @fn.Fn var type.Unit (Bits 5) (fun _ =>
  eexpr.Ret (expr.Binop binop.App (expr.Const (t:=Bits 2) (bits.of_Z _ 1)) (expr.Const (t:=Bits 3) (bits.of_Z _ 5)))
).

Definition test_app_asym {var fn} := fns.package_global_fns'' var fn (@test_app_asym_inner).
