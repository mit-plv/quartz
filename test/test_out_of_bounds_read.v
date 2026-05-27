From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_out_of_bounds_read_inner {var} := @fn.Fn var type.Unit (Bits 32%N) (fun _ => quartz_eexpr:(
  let arr := $(expr.Const (t:=Array (Bits 32%N) 4%nat) (Vector.const (Z_to_bv _ 42%Z) 4)) in
  let i := $(expr.Const (t:=Bits 8%N) (Z_to_bv _ 10%Z)) in
  let val := #arr[#i] in
  return #val)).

Definition test_out_of_bounds_read {var fn} := fns.package_global_fns'' var fn (@test_out_of_bounds_read_inner).
