From Coq Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_app_shift_inner {var} := @fn.Fn var type.Unit (Bits 4) (fun _ =>
  eexpr.Ret (expr.Binop binop.Sru (expr.Binop binop.App (expr.Const (t:=Bits 2) (Zmod.of_Z _ 3)) (expr.Const (t:=Bits 2) (Zmod.of_Z _ 3))) (expr.Const (t:=Bits 2) (Zmod.of_Z _ 1)))
).

Definition test_app_shift {var fn} := fns.package_global_fns'' var fn (@test_app_shift_inner).
