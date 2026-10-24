From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_slice_overrun_inner {var} := @fn.Fn var type.Unit (Bits 8) (fun _ =>
  eexpr.Ret (expr.Unop (unop.Slice 5 8) (expr.Const (t:=Bits 8) (bits.of_Z _ 0xb5)))
).

Definition test_slice_overrun {var fn} := fns.package_global_fns'' var fn (@test_slice_overrun_inner).
