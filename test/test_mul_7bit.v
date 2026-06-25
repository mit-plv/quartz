From Coq Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_mul_7bit_inner {var} := @fn.Fn var type.Unit (Bits 7) (fun _ =>
  eexpr.Ret (expr.Binop (@binop.Mul 7 7 7) (expr.Const (t:=Bits 7) (Zmod.of_Z _ 100)) (expr.Const (t:=Bits 7) (Zmod.of_Z _ 100)))
).

Definition test_mul_7bit {var fn} := fns.package_global_fns'' var fn (@test_mul_7bit_inner).
