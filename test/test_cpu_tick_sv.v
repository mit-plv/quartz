From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax.
Require Import quartz.lang.Processor.

Definition test_cpu_tick_sv_inner {var} := @cpu.tick 2 8 16 8 var.

Definition test_cpu_tick_sv {var fn} :=
  fns.package_global_fns'' var fn (@test_cpu_tick_sv_inner).
