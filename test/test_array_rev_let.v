From Stdlib Require Import BinInt String.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_array_rev_let_inner {var} := @fn.Fn var type.Unit (Bits 4%N) (fun _ =>
  eexpr.Let "arr_var" (expr.Const (t:=Array (Bits 4%N) 2) (@Vector.cons (bv 4%N) (Z_to_bv 4%N 15) 1 (@Vector.cons (bv 4%N) (Z_to_bv 4%N 0) 0 (@Vector.nil (bv 4%N))))) (fun arr =>
    eexpr.Ret (expr.Get (typeWithHole.Array 2 typeWithHole.HOLE 1%N) (expr.Var arr) (expr.Binop binop.MkPair (expr.Const (t:=Bits 1%N) (Z_to_bv _ 0)) (expr.Const (t:=Unit) tt)))
  )
).

Definition test_array_rev_let {var fn} := fns.package_global_fns'' var fn (@test_array_rev_let_inner).
