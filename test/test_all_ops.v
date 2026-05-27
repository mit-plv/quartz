From Ltac2 Require Import Ltac2.
From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

Record AllOpsRecord := {
  r_opp : bits 32; r_not : bits 32; r_isz : Bool; r_ur : bits 16; r_sr : bits 16;
  r_add : bits 32; r_sub : bits 32; r_and : bits 32; r_or : bits 32; r_slu : bits 32; r_sru : bits 32;
  r_srs : bits 32; r_eq : Bool; r_lt : Bool; r_gt : Bool; r_le : Bool;
  r_ge : Bool; r_lts : Bool; r_gts : Bool; r_les : Bool; r_ges : Bool;
  r_mul_full : bits 64; r_mul_same : Bits 32; r_mul_no_integer_promotion : Bits 32;
  r_mul_big_small : Bits 40; r_mul_small_big : Bits 40; r_mul_trunc : Bits 8
}.

Definition rep_all_ops (v : AllOpsRecord) : type.interp (type.reify'' AllOpsRecord) :=
  ltac2:(let t := struct.rep &v in exact $t ).

Definition test_all_ops_inner {var} := @fn.Fn var type.Unit (type.reify'' AllOpsRecord) (fun _ =>
    quartz_eexpr:(
      let x := $(expr.Const (t:=type.Unit) (type.default _)) in
      let x2 := #x ++ #x in
      let a := 32 'd 0xdeadbeef in
      let b := 32 'd 0xbad1dea5 in
      let rec := $(expr.Const (t:=type.reify'' AllOpsRecord) (type.default _)) in
      let rec <- #rec .. r_opp = (- #a) in
      let rec <- #rec .. r_not = (~ #a) in
      let rec <- #rec .. r_isz = (! #a) in
      let s := $(expr.Unop unop.UnsignedResize (expr.Var a)) in
      let rec <- #rec .. r_ur  = #s in
      let rec <- #rec .. r_sr  = $(expr.Unop unop.SignedResize (expr.Var a)) in
      let rec <- #rec .. r_add = (#a + #b) in
      let rec <- #rec .. r_sub = (#a - #b) in
      let rec <- #rec .. r_and = (#a & #b) in
      let rec <- #rec .. r_or  = (#a | #b) in
      let rec <- #rec .. r_slu = (#a << (#rec .. r_ur)) in
      let rec <- #rec .. r_sru = (#a >> (#rec .. r_ur)) in
      let rec <- #rec .. r_srs = (#a .>> (#rec .. r_ur)) in
      let rec <- #rec .. r_mul_full  = $(expr.Binop (@binop.Mul 32 32 64) (expr.Var a) (expr.Var b)) in
      let rec <- #rec .. r_mul_same  = $(expr.Binop (@binop.Mul 32 32 32) (expr.Var a) (expr.Var b)) in
      let m1 := $(expr.Const (t:=Bits 16) (Z_to_bv _ (-1)%Z)) in
      let rec <- #rec .. r_mul_no_integer_promotion  = $(expr.Binop (@binop.Mul 16 16 32) (expr.Var m1) (expr.Var m1)) in
      let rec <- #rec .. r_mul_small_big  = $(expr.Binop (@binop.Mul 16 32 40) (expr.Var s) (expr.Var b)) in
      let rec <- #rec .. r_mul_big_small  = $(expr.Binop (@binop.Mul 32 16 40) (expr.Var a) (expr.Var s)) in
      let rec <- #rec .. r_mul_trunc  = $(expr.Binop (@binop.Mul 32 16 8) (expr.Var a) (expr.Const (t:=Bits _) (Z_to_bv _ (-7)%Z))) in
      let rec <- #rec .. r_eq  = (#a == #b) in
      let rec <- #rec .. r_lt  = (#a < #b) in
      let rec <- #rec .. r_gt  = (#a > #b) in
      let rec <- #rec .. r_le  = (#a <= #b) in
      let rec <- #rec .. r_ge  = (#a >= #b) in
      let rec <- #rec .. r_lts = (#a .< #b) in
      let rec <- #rec .. r_gts = (#a .> #b) in
      let rec <- #rec .. r_les = (#a .<= #b) in
      let rec <- #rec .. r_ges = (#a .>= #b) in
      return #rec
    )).

Definition test_all_ops {var fn} := fns.package_global_fns'' var fn (@test_all_ops_inner).
