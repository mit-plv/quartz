(*! cpp:reject sv:reject *)
From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Local Open Scope string_scope.

Definition test_bad_binder_inner {var} := @fn.Fn var type.Unit (Bits 8) (fun _ => quartz_eexpr:(
  let x' := 8 'd 42 in
  return #x')).

Definition test_bad_binder {var fn} := fns.package_global_fns'' var fn (@test_bad_binder_inner).
