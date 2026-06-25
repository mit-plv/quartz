From Coq Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_signed_cmp_corner_inner {var} := @fn.Fn var type.Unit (Bool) (fun _ =>
  eexpr.Ret (expr.Binop (binop.Compare true binop.cLt) (expr.Const (t:=Bits 4) (Zmod.of_Z _ 7)) (expr.Const (t:=Bits 4) (Zmod.of_Z _ 8)))
).

Definition test_signed_cmp_corner {var fn} := fns.package_global_fns'' var fn (@test_signed_cmp_corner_inner).
