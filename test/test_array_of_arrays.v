From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_array_of_arrays_inner {var} := @fn.Fn var type.Unit (Array (Array (Bits 32%Z) 3%nat) 2%nat) (fun _ => quartz_eexpr:(
  let arr := $(expr.Const (t:=Array (Array (Bits 32%Z) 3%nat) 2%nat) (Vector.const (Vector.const (bits.of_Z _ 42%Z) 3%nat) 2%nat)) in
  let i := $(expr.Const (t:=Bits 1%Z) (bits.of_Z _ 1%Z)) in
  let j := $(expr.Const (t:=Bits 2%Z) (bits.of_Z _ 2%Z)) in
  let inner_arr := #arr[#i] in
  let cur_val := #inner_arr[#j] in
  let next_val := #cur_val + $(expr.Const (t:=Bits 32%Z) (bits.of_Z _ 1%Z)) in
  let inner_arr_new <- #inner_arr[#j] = #next_val in
  let arr_new <- #arr[#i] = #inner_arr_new in
  return #arr_new)).

Definition test_array_of_arrays {var fn} := fns.package_global_fns'' var fn (@test_array_of_arrays_inner).
