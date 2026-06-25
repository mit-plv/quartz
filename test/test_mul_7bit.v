From Stdlib Require Import BinInt String List.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_mul_7bit_inner {var} := @fn.Fn var type.Unit (Bits 7%N) (fun _ =>
  eexpr.Ret (expr.Binop (@binop.Mul 7%N 7%N 7%N) (expr.Const (t:=Bits 7%N) (Z_to_bv _ 100)) (expr.Const (t:=Bits 7%N) (Z_to_bv _ 100)))
).

Definition test_mul_7bit {var fn} := fns.package_global_fns'' var fn (@test_mul_7bit_inner).
