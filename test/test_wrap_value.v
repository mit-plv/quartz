From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_wrap_value_inner {var} := @fn.Fn var type.Unit (Either (Bits 32) (Bits 8)) (fun _ =>
    quartz_eexpr:(
      let v := $(expr.Const (t:=Bits 32) Zmod.zero) in
      let is_z := ! #v in
      if #is_z
      then return left #v
      else return right $(expr.Const (t:=Bits 8) (Zmod.of_Z 256 255)))).

Definition test_wrap_value {var fn} := fns.package_global_fns'' var fn (@test_wrap_value_inner).
