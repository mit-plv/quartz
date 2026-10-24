From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax.
Import type expr eexpr fn.

Definition isMMIOAddr {var} : fn var (Bits 32) Bool := Fn (fun pc => quartz_eexpr:(
  let shift_amt : Bits 32 := $(expr.Const (t:=Bits 32) (bits.of_Z 32 31%Z)) in
  let shifted_pc := #pc >> #shift_amt in
  return $(expr.Unop unop.UnsignedResize (expr.Var shifted_pc))
)).
