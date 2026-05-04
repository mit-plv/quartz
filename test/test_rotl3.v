From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_rotl3_inner {var} := @fn.Fn var type.Unit (Bits 32) (fun _ =>
    quartz_eexpr:(
      let v := 32 'd 42 in
      let sl := #v << 32 'd 3 in
      let sr := #v >> 32 'd 29 in
      return ( #sl | #sr )
    )).

Definition test_rotl3 {var fn} := fns.package_global_fns'' var fn (@test_rotl3_inner).
