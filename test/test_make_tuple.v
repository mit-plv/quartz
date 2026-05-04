From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_make_tuple_inner {var} := @fn.Fn var type.Unit (Pair (Pair (Bits 32) (Bits 32)) Bool) (fun _ => quartz_eexpr:(
  let v := 32 'd 42 in return ( #v , ~#v , ! #v ) )).

Definition test_make_tuple {var fn} := fns.package_global_fns'' var fn (@test_make_tuple_inner).
