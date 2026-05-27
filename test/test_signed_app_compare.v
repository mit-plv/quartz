From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_signed_app_compare_inner {var fn} (u : var type.Unit) : eexpr.eexpr var fn Bool :=
  quartz_eexpr:(
    let a := $(expr.Const (t:=Bits 8) (Z_to_bv _ 255)) in
    let b := $(expr.Const (t:=Bits 8) (Z_to_bv _ 255)) in
    let ab := (#a ++ #b) in
    let zero := $(expr.Const (t:=Bits 16) (bv_0 _)) in
    return (#ab .< #zero)
  ).

Definition test_signed_app_compare {var fn} := @fns.Ret var fn _ _ "test_signed_app_compare_inner" "u" test_signed_app_compare_inner.
