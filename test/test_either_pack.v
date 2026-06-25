From Stdlib Require Import BinInt.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_either_pack_inner {var} := @fn.Fn var type.Unit (Either (Bits 1%N) (Bits 1%N)) (fun _ =>
  eexpr.Ret (expr.Unop unop.Left (expr.Const (t:=Bits 1%N) (Z_to_bv _ 1)))
).

Definition test_either_pack {var fn} := fns.package_global_fns'' var fn (@test_either_pack_inner).
