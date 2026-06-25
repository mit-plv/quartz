From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Import fn.
From Stdlib Require Import String.
Local Open Scope string_scope.

Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x => quartz_eexpr:(
  return ( #x + 8 'd 1 ))).
Definition pred {var} {n} : fn var (Bits n) (Bits n) := Fn (fun y => quartz_eexpr:(
  let _u := succ ($(expr.Unop unop.UnsignedResize (expr.Var y)) ) in
  return ( #y + _ 'd (-1) ))).
Definition cycle {var} := Fn (var:=var) (fun z => quartz_eexpr:(
  let r := pred ( succ ( #z ) ) in return #r)).

Lemma interp_cycle : interp cycle = fun z => (z + bits.of_Z _ 1 + bits.of_Z _ (-1))%Zmod.
Proof. cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp]. trivial. Qed.

Lemma ok_cycle z : interp cycle z = z.
Proof. rewrite interp_cycle, <-Zmod.add_assoc, (Zmod.of_Z_opp 1), Zmod.add_0_r; trivial. Qed.

Definition test_global_polyfn_inner := @cycle.
Definition test_global_polyfn {var fn} := fns.package_global_fns'' var fn (@test_global_polyfn_inner).
Require Import Coq.Logic.FunctionalExtensionality.
Lemma interp_reified : fns.interp test_global_polyfn = interp cycle. Proof. reflexivity. Qed.

