From Stdlib Require Import Bits.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_wrap_value2_inner {var} := @fn.Fn var type.Unit (Either (Bits 32) (Bits 8)) (fun _ =>
    quartz_eexpr:(
      let v := $(expr.Const (t:=Bits 32) (bits.of_Z _ 1%Z)) in
      return (if ! #v then left #v else right $(expr.Const (t:=Bits 8) (bits.of_Z _ 255%Z))))).

Definition test_wrap_value2 {var fn} := fns.package_global_fns'' var fn (@test_wrap_value2_inner).
