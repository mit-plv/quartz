From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_not_context_inner {var} := @fn.Fn var type.Unit (Bits 16%Z) (fun _ =>
    quartz_eexpr:(
      let x := $(expr.Const (t:=Bits 8%Z) Zmod.zero) in
      return $(expr.Unop (t1:=Bits 8%Z) (@unop.Resize false 8%Z 16%Z) (expr.Unop (t1:=Bits 8%Z) (@unop.Not 8%Z) (expr.Var x)))
    )).

Definition test_not_context {var fn} := fns.package_global_fns'' var fn (@test_not_context_inner).
