From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_shift_context_inner {var} := @fn.Fn var type.Unit (Bits 32%N) (fun _ => quartz_eexpr:(
  let a := $(expr.Const (t:=Bits 8%N) (bv_0 _)) in
  let b := $(expr.Const (t:=Bits 8%N) (Z_to_bv _ 255%Z)) in
  let c := $(expr.Const (t:=Bits 8%N) (Z_to_bv _ 12%Z)) in
  return $(expr.Unop (t1:=Bits 16%N) (@unop.Resize false 16%N 32%N) quartz_expr:(#a ++ (#b << #c))))).

Definition test_shift_context {var fn} := fns.package_global_fns'' var fn (@test_shift_context_inner).
