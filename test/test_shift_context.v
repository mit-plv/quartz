From Stdlib Require Import Bits.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_shift_context_inner {var} := @fn.Fn var type.Unit (Bits 32%Z) (fun _ => quartz_eexpr:(
  let a := $(expr.Const (t:=Bits 8%Z) Zmod.zero) in
  let b := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 255%Z)) in
  let c := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 12%Z)) in
  return $(expr.Unop (t1:=Bits 16%Z) (@unop.Resize false 16%Z 32%Z) quartz_expr:(#a ++ (#b << #c))))).

Definition test_shift_context {var fn} := fns.package_global_fns'' var fn (@test_shift_context_inner).
