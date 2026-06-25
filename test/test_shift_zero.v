From Stdlib Require Import BinInt String List.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_shift_zero_inner {var} := @fn.Fn var type.Unit (Bits 4%N) (fun _ =>
  eexpr.Ret (expr.Binop binop.Slu (expr.Const (t:=Bits 4%N) (Z_to_bv _ 8)) (expr.Const (t:=Bits 4%N) (Z_to_bv _ 0)))
).

Definition test_shift_zero {var fn} := fns.package_global_fns'' var fn (@test_shift_zero_inner).
