From Coq Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_add_overflow_diff_inner {var} := @fn.Fn var type.Unit (Bits 8) (fun _ =>
  eexpr.Ret (expr.Unop (@unop.UnsignedResize 4 8) (expr.Binop binop.Add (expr.Const (t:=Bits 4) (Zmod.of_Z _ 15)) (expr.Const (t:=Bits 4) (Zmod.of_Z _ 1))))
).

Definition test_add_overflow_diff {var fn} := fns.package_global_fns'' var fn (@test_add_overflow_diff_inner).
