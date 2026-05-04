From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_out_of_bounds_read_inner {var} := @fn.Fn var type.Unit (Bits 32%Z) (fun _ => quartz_eexpr:(
  let arr := $(expr.Const (t:=Array (Bits 32%Z) 4%nat) (Vector.const (bits.of_Z _ 42) 4)) in
  let i := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 10)) in
  let val := #arr[#i] in
  return #val)).

Definition test_out_of_bounds_read {var fn} := fns.package_global_fns'' var fn (@test_out_of_bounds_read_inner).
