(*! sv:reject *)
From Coq Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_array_unit_inner {var} := @fn.Fn var type.Unit (Array Unit 16) (fun _ =>
  eexpr.Ret (expr.Const (t:=Array Unit 16) (type.default _))
).

Definition test_array_unit {var fn} := fns.package_global_fns'' var fn (@test_array_unit_inner).
