From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_srs_context_inner {var} := @fn.Fn var type.Unit (Bits 16%Z) (fun _ =>
    quartz_eexpr:(
      let a := $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 255)) in
      let b := $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 1)) in
      return $(expr.Unop (t1:=Bits 8%Z) (@unop.Resize false 8%Z 16%Z) quartz_expr:(#a .>> #b))
    )).

Definition test_srs_context {var fn} := fns.package_global_fns'' var fn (@test_srs_context_inner).
