From Coq Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_either_pack_inner {var} := @fn.Fn var type.Unit (Either (Bits 1) (Bits 1)) (fun _ =>
  eexpr.Ret (expr.Unop unop.Left (expr.Const (t:=Bits 1) (Zmod.of_Z _ 1)))
).

Definition test_either_pack {var fn} := fns.package_global_fns'' var fn (@test_either_pack_inner).
