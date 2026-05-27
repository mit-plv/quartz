From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Fixpoint bigexpr {var fn} (n : nat) (acc : expr var fn (Bits 32%N)) : expr var fn (Bits 32%N) :=
  match n with
  | O => acc
  | S n' => bigexpr n' (@expr.Binop var fn (Bits 32%N) (Bits 32%N) (Bits 32%N) (@binop.Add 32%N) acc (@expr.Const var fn (Bits 32%N) (Z_to_bv _ 1%Z)))
  end.

Definition test_huge_unroll_inner {var : type -> Type} {fn : type -> type -> Type} (u : var type.Unit) : eexpr.eexpr var fn (Bits 32%N) :=
  @eexpr.Ret var fn (Bits 32%N) (bigexpr 20 (@expr.Const var fn (Bits 32%N) (bv_0 _))).

Definition test_huge_unroll {var fn} := @fns.Ret var fn _ _ "test_huge_unroll_inner" "u" test_huge_unroll_inner.
