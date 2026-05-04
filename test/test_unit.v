From Stdlib Require Import BinInt Bits.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.

(* NOTE: SystemVerilog and C++ disallow width 0, so the width doesn't match *)
Definition test_unit_inner {var} := @fn.Fn var type.Unit type.Unit (fun _ => quartz_eexpr:(
  return $(expr.Const (t:=Unit) (type.default _)))).

Definition test_unit {var fn} := fns.package_global_fns'' var fn (@test_unit_inner).
