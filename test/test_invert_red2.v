From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt String List. Import ListNotations.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Record Pixel := { valid : Bool; red : bits 8; green : bits 8; blue : bits 8 }.
Definition rep_pixel (v : Pixel) : type.interp (type.reify'' Pixel) :=
  (v.(valid), (v.(red), (v.(green), (v.(blue), Datatypes.tt)))).

Definition hole_red := @typeWithHole.Struct "Pixel" [("valid", type.Bool)] "red" typeWithHole.HOLE [("green", type.Bits 8); ("blue", type.Bits 8)] (fun _ => eq_refl).

Definition test_invert_red2_inner {var} := @fn.Fn var type.Unit (type.reify'' Pixel) (fun _ =>
    quartz_eexpr:(
      let p := const (rep_pixel (Build_Pixel (Z_to_bv _ 1%Z) (Z_to_bv _ 255%Z) (bv_0 _) (bv_0 _))) in
      let cur_red := #p .[ hole_red , $expr.tt ] in
      let inv_red : Bits 8 := ~ #cur_red in
      let p_new <- #p .[ hole_red , $expr.tt ] = #inv_red in
      return #p_new)).

Definition test_invert_red2 {var fn} := fns.package_global_fns'' var fn (@test_invert_red2_inner).
