From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_and_sru_context_inner {var} := @fn.Fn var type.Unit (Bits 16%Z) (fun _ =>
    quartz_eexpr:(
      let a := $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 255)) in
      let b := $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 255)) in
      return $(expr.Unop (t1:=Bits 8%Z) (@unop.Resize false 8%Z 16%Z) quartz_expr:(
        (#a & #b) >> $(expr.Const (t:=Bits 8%Z) (Zmod.of_Z 256 4))
      ))
    )).

Definition test_and_sru_context {var fn} := fns.package_global_fns'' var fn (@test_and_sru_context_inner).
