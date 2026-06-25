From Stdlib Require Import BinNat.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax.
Import type expr eexpr fn.

Definition isMMIOAddr {var} : fn var (Bits 32%N) Bool := Fn (fun pc => quartz_eexpr:(
  let shift_amt : Bits 32%N := $(expr.Const (t:=Bits 32%N) (Z_to_bv 32%N 31%Z)) in
  let shifted_pc := #pc >> #shift_amt in
  return $(expr.Unop unop.UnsignedResize (expr.Var shifted_pc))
)).
