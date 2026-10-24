From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_array_rev_let_inner {var} := @fn.Fn var type.Unit (Bits 4) (fun _ =>
  eexpr.Let "arr_var" (expr.Const (t:=Array (Bits 4) 2) (@Vector.cons (bits 4) (bits.of_Z 4 15) 1 (@Vector.cons (bits 4) (bits.of_Z 4 0) 0 (@Vector.nil (bits 4))))) (fun arr =>
    eexpr.Ret (expr.Get (typeWithHole.Array 2 typeWithHole.HOLE 1) (expr.Var arr) (expr.Binop binop.MkPair (expr.Const (t:=Bits 1) (bits.of_Z _ 0)) (expr.Const (t:=Unit) tt)))
  )
).

Definition test_array_rev_let {var fn} := fns.package_global_fns'' var fn (@test_array_rev_let_inner).
