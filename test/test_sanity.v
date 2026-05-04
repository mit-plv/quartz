From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_sanity_inner {var} := @fn.Fn var type.Unit (Bits 32%Z) (fun _ => quartz_eexpr:(
  return (32 'd 10 + 32 'd 32))).

Definition test_sanity {var fn} := fns.package_global_fns'' var fn (@test_sanity_inner).
