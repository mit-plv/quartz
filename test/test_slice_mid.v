From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_slice_mid_inner {var} := @fn.Fn var type.Unit (Bits 4) (fun _ =>
  eexpr.Ret (expr.Unop (unop.Slice 3 4) (expr.Const (t:=Bits 8) (bits.of_Z _ 0xb5)))
).

Definition test_slice_mid {var fn} := fns.package_global_fns'' var fn (@test_slice_mid_inner).
