From Stdlib Require Import Bits.
From Stdlib Require Import BinInt String.
Require Import quartz.lang.Syntax quartz.lang.transform. Import type.
Import Syntax.type Syntax.expr Syntax.eexpr.

Record Pixel := { valid : Bool; red : bits 8; green : bits 8; blue : bits 8 }.
Definition rep_pixel (v : Pixel) : type.interp (type.reify'' Pixel) :=
  (v.(valid), (v.(red), (v.(green), (v.(blue), Datatypes.tt)))).

Definition test_pack_pixel_inner {var : type -> Type} {fn : type -> type -> Type} (u : var type.Unit) : eexpr.eexpr var fn (Bits 25%Z) :=
  @eexpr.pack var fn (type.reify'' Pixel) (ltac:(repeat (constructor || cbn || discriminate)))
    (expr.Const (rep_pixel (Build_Pixel (bits.of_Z _ 1%Z) (bits.of_Z _ 0xab%Z) Zmod.zero (bits.of_Z _ 42%Z)))).

Definition test_pack_pixel {var fn} := @fns.Ret var fn _ _ "test_pack_pixel_inner" "u" test_pack_pixel_inner.
