From Stdlib Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_mul_diff_inner {var} := @fn.Fn var type.Unit (Bits 8) (fun _ =>
  eexpr.Ret (expr.Binop (@binop.Mul 4 4 8) (expr.Const (t:=Bits 4) (bits.of_Z _ 15)) (expr.Const (t:=Bits 4) (bits.of_Z _ 15)))
).

Definition test_mul_diff {var fn} := fns.package_global_fns'' var fn (@test_mul_diff_inner).
