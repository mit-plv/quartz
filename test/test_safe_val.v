From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition test_safe_val_inner {var} := @fn.Fn var type.Unit (Bits 32) (fun _ => quartz_eexpr:(
  let v := 32 'd 0 in
  let is_z := ! #v in
  if #is_z then return ( 32'd 1)
  else return #v)).

Definition test_safe_val {var fn} := fns.package_global_fns'' var fn (@test_safe_val_inner).
