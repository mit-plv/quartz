From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_srs_context_inner {var} := @fn.Fn var type.Unit (Bits 16%N) (fun _ =>
    quartz_eexpr:(
      let a := $(expr.Const (t:=Bits 8%N) (Z_to_bv _ 255%Z)) in
      let b := $(expr.Const (t:=Bits 8%N) (Z_to_bv _ 1%Z)) in
      return $(expr.Unop (t1:=Bits 8%N) (@unop.Resize false 8%N 16%N) quartz_expr:(#a .>> #b))
    )).

Definition test_srs_context {var fn} := fns.package_global_fns'' var fn (@test_srs_context_inner).
