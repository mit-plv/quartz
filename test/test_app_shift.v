From Stdlib Require Import BinInt String List.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_app_shift_inner {var} := @fn.Fn var type.Unit (Bits 4%N) (fun _ =>
  eexpr.Ret (expr.Binop binop.Sru (expr.Binop (binop.App 4%N) (expr.Const (t:=Bits 2%N) (Z_to_bv _ 3)) (expr.Const (t:=Bits 2%N) (Z_to_bv _ 3))) (expr.Const (t:=Bits 4%N) (Z_to_bv _ 1)))
).

Definition test_app_shift {var fn} := fns.package_global_fns'' var fn (@test_app_shift_inner).
