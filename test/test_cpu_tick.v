From Stdlib Require Import BinInt BinNat String.
Import BinNat.
Require Import quartz.lang.Syntax. Import type fns.
Require Import quartz.lang.ident_to_string.
Require Import quartz.lang.domain.
Require Import quartz.examples.Processor.
Import InterfaceExample.
From quartz.test Require Import test_cpu_tick_fns.
From quartz.test Require Import test_cpu_tick_util.
Import (notations) type expr eexpr fn.
Local Open Scope string_scope.

Definition test_cpu_tick_inner {var} := @cpu.tick 2%N 8%N 16%N 8%N (@isMMIOAddr) var.

Definition test_cpu_tick {var : Syntax.type.type -> Type} {fn : Syntax.type.type -> Syntax.type.type -> Type} : fns.fns var fn _ _ :=
  fns.package_global_fns'' var fn (@test_cpu_tick_inner).
