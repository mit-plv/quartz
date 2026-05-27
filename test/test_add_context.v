From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_add_context_inner {var} := @fn.Fn var type.Unit (Bits 16%N) (fun _ =>
    quartz_eexpr:(
      let a := $(expr.Const (t:=Bits 8) (Z_to_bv _ 255)) in
      let b := $(expr.Const (t:=Bits 8) (Z_to_bv _ 1)) in
      return $(expr.Unop (t1:=Bits _) (@unop.Resize false _ 16) quartz_expr:(#a + #b))
    )).

Definition test_add_context {var fn} := fns.package_global_fns'' var fn (@test_add_context_inner).

