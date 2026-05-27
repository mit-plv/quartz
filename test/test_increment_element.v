From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_increment_element_inner {var} := @fn.Fn var type.Unit (Array (Bits 32%N) 4%nat) (fun _ => quartz_eexpr:(
  let arr := $(expr.Const (t:=Array (Bits 32%N) 4%nat) (Vector.const (Z_to_bv _ 42%Z) 4%nat)) in
  let i := $(expr.Const (t:=Bits 2%N) (Z_to_bv _ 1%Z)) in
  let cur_val := #arr[#i] in
  let next_val := #cur_val + $(expr.Const (t:=Bits 32%N) (Z_to_bv _ 1%Z)) in
  let arr_new <- #arr[#i] = #next_val in
  return #arr_new)).

Definition test_increment_element {var fn} := fns.package_global_fns'' var fn (@test_increment_element_inner).
