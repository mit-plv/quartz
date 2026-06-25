From Coq Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_srs_lt_inner {var} := @fn.Fn var type.Unit (Bool) (fun _ =>
  eexpr.Ret (expr.Binop (binop.Compare true binop.cLt) (expr.Binop binop.Srs (expr.Const (t:=Bits 4) (Zmod.of_Z _ 8)) (expr.Const (t:=Bits 2) (Zmod.of_Z _ 1))) (expr.Const (t:=Bits 4) (Zmod.of_Z _ 0)))
).

Definition test_srs_lt {var fn} := fns.package_global_fns'' var fn (@test_srs_lt_inner).
