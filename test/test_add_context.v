From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_add_context_inner {var} := @fn.Fn var type.Unit (Bits 16%Z) (fun _ =>
    quartz_eexpr:(
      let a := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 255)) in
      let b := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 1)) in
      return $(expr.Unop (t1:=Bits _%Z) (@unop.Resize false _ 16%Z) quartz_expr:(#a + #b))
    )).

Definition test_add_context {var fn} := fns.package_global_fns'' var fn (@test_add_context_inner).
