From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_huge_bits_inner {var} := @fn.Fn var type.Unit (Bits 100000%Z) (fun _ =>
    quartz_eexpr:(
      return $(expr.Const (t:=Bits 100000%Z) Zmod.zero)
    )).

Definition test_huge_bits {var fn} := fns.package_global_fns'' var fn (@test_huge_bits_inner).
