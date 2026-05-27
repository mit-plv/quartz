(*! sv:reject *)
From stdpp Require Import bitvector.definitions.
From Stdlib Require Import BinInt String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition t := Struct "st" (cons ("b", Bits 1) (cons ("a", Unit) nil)).

Definition test_struct_unit_inner {var} := @fn.Fn var type.Unit t (fun _ =>
  eexpr.Ret (expr.Const (t:=t) (Z_to_bv _ 1%Z, (bv_0 _, Datatypes.tt)))
).

Definition test_struct_unit {var fn} := fns.package_global_fns'' var fn (@test_struct_unit_inner).
