From Stdlib Require Import Bits.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_and_sru_context_inner {var} := @fn.Fn var type.Unit (Bits 16%Z) (fun _ =>
    quartz_eexpr:(
      let a := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 255%Z)) in
      let b := $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 255%Z)) in
      return $(expr.Unop (t1:=Bits 8%Z) (@unop.Resize false 8%Z 16%Z) quartz_expr:(
        (#a & #b) >> $(expr.Const (t:=Bits 8%Z) (bits.of_Z _ 4%Z))
      ))
    )).

Definition test_and_sru_context {var fn} := fns.package_global_fns'' var fn (@test_and_sru_context_inner).
