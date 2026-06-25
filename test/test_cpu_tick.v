From Stdlib Require Import BinInt String.
Require Import quartz.lang.Syntax. Import type fns.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.lang.Processor.
From quartz.lang Require Import test_cpu_tick_fns.
Import (notations) type expr eexpr fn.
Local Open Scope string_scope.

Definition test_cpu_tick_inner {var} := @cpu.tick 2 8 16 8 var.

Definition test_cpu_tick {var : Syntax.type.type -> Type} {fn : Syntax.type.type -> Syntax.type.type -> Type} : fns.fns var fn _ _ :=
  fns.package_global_fns'' var fn (@test_cpu_tick_inner).
