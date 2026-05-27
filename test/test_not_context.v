From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_not_context_inner {var} := @fn.Fn var type.Unit (Bits 16%N) (fun _ =>
    quartz_eexpr:(
      let x := $(expr.Const (t:=Bits 8%N) (bv_0 _)) in
      return $(expr.Unop (t1:=Bits 8%N) (@unop.Resize false 8%N 16%N) (expr.Unop (t1:=Bits 8%N) (@unop.Not 8%N) (expr.Var x)))
    )).

Definition test_not_context {var fn} := fns.package_global_fns'' var fn (@test_not_context_inner).
