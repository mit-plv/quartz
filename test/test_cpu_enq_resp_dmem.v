From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax.
Require Import quartz.lang.Processor.

Definition test_cpu_enq_resp_dmem_inner {var} := @cpu.enq_resp_dmem 2 8 16 8 var.

Definition test_cpu_enq_resp_dmem {var fn} :=
  fns.package_global_fns'' var fn (@test_cpu_enq_resp_dmem_inner).
