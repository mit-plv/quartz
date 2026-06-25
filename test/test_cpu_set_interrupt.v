From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax.
Require Import quartz.lang.Processor.

Definition test_cpu_set_interrupt_inner {var} := @cpu.set_interrupt 2 8 16 8 var.

Definition test_cpu_set_interrupt {var fn} :=
  fns.package_global_fns'' var fn (@test_cpu_set_interrupt_inner).
