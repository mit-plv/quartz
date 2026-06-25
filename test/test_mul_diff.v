From Stdlib Require Import BinInt.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_mul_diff_inner {var} := @fn.Fn var type.Unit (Bits 8%N) (fun _ =>
  eexpr.Ret (expr.Binop (@binop.Mul 4%N 4%N 8%N) (expr.Const (t:=Bits 4%N) (Z_to_bv _ 15)) (expr.Const (t:=Bits 4%N) (Z_to_bv _ 15)))
).

Definition test_mul_diff {var fn} := fns.package_global_fns'' var fn (@test_mul_diff_inner).
