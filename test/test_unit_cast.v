From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_unit_cast_inner {var} := @fn.Fn var type.Unit (Either Unit (Bits 1)) (fun _ =>
  eexpr.Ret (expr.Unop unop.Right (expr.Const (t:=Bits 1) (Z_to_bv _ 1%Z)))
).

Definition test_unit_cast {var fn} := fns.package_global_fns'' var fn (@test_unit_cast_inner).
