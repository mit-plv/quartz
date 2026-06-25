From Stdlib Require Import BinInt BinNat Bits.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Import fn.
From Stdlib Require Import String.
Local Open Scope N_scope.
Local Open Scope string_scope.

Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x => quartz_eexpr:(
  return ( #x + 8 'd 1 ))).
Definition pred {var} {n} : fn var (Bits n) (Bits n) := Fn (fun y => quartz_eexpr:(
  let _u := succ ($(expr.Unop unop.UnsignedResize (expr.Var y)) ) in
  return ( #y + _ 'd (-1) ))).
Definition cycle {var} := Fn (var:=var) (fun z => quartz_eexpr:(
  let r := pred ( succ ( #z ) ) in return #r)).

Lemma interp_cycle : interp cycle = fun z => bv_add (bv_add z (Z_to_bv 8 1)) (Z_to_bv 8 (-1)).
Proof. cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp]. trivial. Qed.

Lemma ok_cycle z : interp cycle z = z.
Proof.
  rewrite interp_cycle.
  apply bv_eq.
  rewrite !bv_add_unsigned.
  rewrite !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 z).
  unfold bv_wrap, bv_modulus in *.
  simpl in *.
  lia.
Qed.

Definition test_global_polyfn_inner := @cycle.
Definition test_global_polyfn {var fn} := fns.package_global_fns'' var fn (@test_global_polyfn_inner).
Require Import Coq.Logic.FunctionalExtensionality.
Lemma interp_reified : fns.interp test_global_polyfn = interp cycle. Proof. reflexivity. Qed.

