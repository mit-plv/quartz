From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_wrap_value2_inner {var} := @fn.Fn var type.Unit (Either (Bits 32) (Bits 8)) (fun _ =>
    quartz_eexpr:(
      let v := $(expr.Const (t:=Bits 32) (Zmod.of_Z 4294967296 1)) in
      return (if ! #v then left #v else right $(expr.Const (t:=Bits 8) (Zmod.of_Z 256 255))))).

Definition test_wrap_value2 {var fn} := fns.package_global_fns'' var fn (@test_wrap_value2_inner).
