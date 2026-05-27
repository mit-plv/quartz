(*! sv:reject cpp:reject *)
From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_either_unit_unit_inner {var} := @fn.Fn var type.Unit (Either Unit Unit) (fun _ =>
  eexpr.Ret (expr.Unop unop.Left (expr.Const (t:=Unit) (bv_0 _)))
).

Definition test_either_unit_unit {var fn} := fns.package_global_fns'' var fn (@test_either_unit_unit_inner).
