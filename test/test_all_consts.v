From Ltac2 Require Import Ltac2.
From Stdlib Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Record MiniStruct := { mini_a : bits 4 }.
Definition MiniStructType := type.reify'' MiniStruct.

Record AllTypesRecord := {
  l_bits : bits 8;
  l_pair : type.interp (Pair (Bits 4) (Bits 4));
  l_either : type.interp (Either (Bits 4) (Bits 4));
  l_struct : type.interp MiniStructType;
  l_array : type.interp (Array (Bits 4) 2)
}.

Definition test_all_consts_inner {var} := @fn.Fn var type.Unit (type.reify'' AllTypesRecord) (fun _ =>
  quartz_eexpr:(
    let rec := $(expr.Const (t:=type.reify'' AllTypesRecord) (type.default _)) in
    let rec <- #rec .. l_bits = $(expr.Const (t:=Bits 8) (Zmod.of_Z _ 42)) in
    let rec <- #rec .. l_pair = $(expr.Const (t:=Pair (Bits 4) (Bits 4)) (Zmod.of_Z _ 1, Zmod.of_Z _ 2)) in
    let rec <- #rec .. l_either = $(expr.Const (t:=Either (Bits 4) (Bits 4)) (inl (Zmod.of_Z _ 3))) in
    let rec <- #rec .. l_struct = $(expr.Const (t:=MiniStructType) (Zmod.of_Z _ 4, Datatypes.tt)) in
    let rec <- #rec .. l_array = $(expr.Const (t:=Array (Bits 4) 2) (Vector.cons _ (Zmod.of_Z _ 5) 1 (Vector.cons _ (Zmod.of_Z _ 6) 0 (Vector.nil _)))) in
    return #rec
)).

Definition test_all_consts {var fn} := fns.package_global_fns'' var fn (@test_all_consts_inner).
