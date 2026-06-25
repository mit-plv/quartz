From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt BinNat String.
From stdpp Require Import bitvector.definitions.
Require Import quartz.lang.Syntax. Import Syntax.type.
Require Import quartz.lang.domain.
Import (coercions) domain.BV.
Import (notations) type expr eexpr.
Open Scope Z_scope.
Local Open Scope N_scope.

Record MyPixel := { my_red : bits 8 }.
Definition rep_mypixel (v : MyPixel) : type.interp (type.reify'' MyPixel) :=
  (v.(my_red), Datatypes.tt).

Definition test_bitwidth_reproducer_inner {var} := @fn.Fn var type.Unit (type.reify'' MyPixel) (fun _ =>
  quartz_eexpr:(
    let p := const (rep_mypixel (Build_MyPixel (Z_to_bv 8 0))) in
    return #p
  )).

Definition test_bitwidth_reproducer {var fn} := fns.package_global_fns'' var fn (@test_bitwidth_reproducer_inner).
