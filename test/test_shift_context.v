From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_shift_context_inner {var} := @fn.Fn var type.Unit (Bits 32%Z) (fun _ => quartz_eexpr:(
  let a := $(expr.Const (t:=Bits 8%Z) Zmod.zero) in
  let b := $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 255)) in
  let c := $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 12)) in
  return $(expr.Unop (t1:=Bits 16%Z) (@unop.Resize false 16%Z 32%Z) quartz_expr:(#a ++ (#b << #c))))).

Definition test_shift_context {var fn} := fns.package_global_fns'' var fn (@test_shift_context_inner).
