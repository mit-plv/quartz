From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_app_resize_inner {var} := @fn.Fn var type.Unit (Bits 8) (fun _ =>
  eexpr.Ret (expr.Unop (@unop.UnsignedResize 5 8) (expr.Binop binop.App (expr.Const (t:=Bits 2) (bits.of_Z _ 1)) (expr.Const (t:=Bits 3) (bits.of_Z _ 5))))
).

Definition test_app_resize {var fn} := fns.package_global_fns'' var fn (@test_app_resize_inner).
