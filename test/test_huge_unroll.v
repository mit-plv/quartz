From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Fixpoint bigexpr {var fn} (n : nat) (acc : expr var fn (Bits 32%Z)) : expr var fn (Bits 32%Z) :=
  match n with
  | O => acc
  | S n' => bigexpr n' (@expr.Binop var fn (Bits 32%Z) (Bits 32%Z) (Bits 32%Z) (@binop.Add 32%Z) acc (@expr.Const var fn (Bits 32%Z) (Zmod.of_Z 4294967296 1)))
  end.

Definition test_huge_unroll_inner {var : type -> Type} {fn : type -> type -> Type} (u : var type.Unit) : eexpr.eexpr var fn (Bits 32%Z) :=
  @eexpr.Ret var fn (Bits 32%Z) (bigexpr 20 (@expr.Const var fn (Bits 32%Z) (Zmod.zero))).

Definition test_huge_unroll {var fn} := @fns.Ret var fn _ _ "test_huge_unroll_inner" "u" test_huge_unroll_inner.
