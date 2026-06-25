From Coq Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_shift_zero_inner {var} := @fn.Fn var type.Unit (Bits 4) (fun _ =>
  eexpr.Ret (expr.Binop binop.Slu (expr.Const (t:=Bits 4) (Zmod.of_Z _ 8)) (expr.Const (t:=Bits 4) (Zmod.of_Z _ 0)))
).

Definition test_shift_zero {var fn} := fns.package_global_fns'' var fn (@test_shift_zero_inner).
