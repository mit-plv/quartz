From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Definition succ {var} := @fn.Fn var (Bits 8) (Bits 8) (fun x => quartz_eexpr:(
  return ( #x + 8 'd 1 ))).

Definition pred {var} := @fn.Fn var (Bits 8) (Bits 8) (fun y => quartz_eexpr:(
  let _u := succ ($(expr.Unop unop.UnsignedResize (expr.Var y)) ) in
  return ( #y + 8 'd (-1) ))).

Definition test_global_fn_inner {var} := @fn.Fn var (Bits 8) (Bits 8) (fun z => quartz_eexpr:(
  let r := pred ( succ ( #z ) ) in return #r)).

Definition test_global_fn {var fn} := fns.package_global_fns'' var fn (@test_global_fn_inner).
