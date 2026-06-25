From Stdlib Require Import BinInt String List.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_signed_cmp_corner_inner {var} := @fn.Fn var type.Unit (Bool) (fun _ =>
  eexpr.Ret (expr.Binop (binop.Compare true binop.cLt) (expr.Const (t:=Bits 4%N) (Z_to_bv _ 7)) (expr.Const (t:=Bits 4%N) (Z_to_bv _ 8)))
).

Definition test_signed_cmp_corner {var fn} := fns.package_global_fns'' var fn (@test_signed_cmp_corner_inner).
