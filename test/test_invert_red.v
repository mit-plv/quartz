From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Record Pixel := { valid : Bool; red : bits 8; green : bits 8; blue : bits 8 }.
Definition rep_pixel (v : Pixel) : type.interp (type.reify'' Pixel) :=
  (v.(valid), (v.(red), (v.(green), (v.(blue), Datatypes.tt)))).

Definition test_invert_red_inner {var} := @fn.Fn var type.Unit (type.reify'' Pixel) (fun _ =>
    quartz_eexpr:(
      let p := const (rep_pixel (Build_Pixel Zmod.one (Zmod.of_Z 256 255) Zmod.zero Zmod.zero)) in
      let cur_red := #p..red in
      let inv_red := ~ #cur_red in
      let p_new <- #p..red = #inv_red in
      return #p_new)).

Definition test_invert_red {var fn} := fns.package_global_fns'' var fn (@test_invert_red_inner).
