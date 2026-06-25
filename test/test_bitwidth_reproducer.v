From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import Syntax.type.
Require Import quartz.lang.domain.
Import (coercions) domain.Zmod.
Import (notations) type expr eexpr.
Open Scope Z_scope.

Record MyPixel := { my_red : bits 8 }.
Definition rep_mypixel (v : MyPixel) : type.interp (type.reify'' MyPixel) :=
  (v.(my_red), Datatypes.tt).

Definition test_bitwidth_reproducer_inner {var} := @fn.Fn var type.Unit (type.reify'' MyPixel) (fun _ =>
  quartz_eexpr:(
    let p := const (rep_mypixel (Build_MyPixel Zmod.zero)) in
    return #p
  )).

Definition test_bitwidth_reproducer {var fn} := fns.package_global_fns'' var fn (@test_bitwidth_reproducer_inner).
