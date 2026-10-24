From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_xor_inner {var} := @fn.Fn var type.Unit (Bits 4) (fun _ =>
  eexpr.Ret (expr.Binop binop.Xor (expr.Const (t:=Bits 4) (bits.of_Z _ 0xc)) (expr.Const (t:=Bits 4) (bits.of_Z _ 0xa)))
).

Definition test_xor {var fn} := fns.package_global_fns'' var fn (@test_xor_inner).
