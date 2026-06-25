From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax.
Require Import quartz.lang.Processor.

Definition test_cpu_can_enq_resp_imem_inner {var} := @cpu.can_enq_resp_imem 2 8 16 8 var.

Definition test_cpu_can_enq_resp_imem {var fn} :=
  fns.package_global_fns'' var fn (@test_cpu_can_enq_resp_imem_inner).
