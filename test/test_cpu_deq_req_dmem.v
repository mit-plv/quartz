From Stdlib Require Import BinInt.
Require Import quartz.lang.Syntax.
Require Import quartz.lang.Processor.

Definition test_cpu_deq_req_dmem_inner {var} := @cpu.deq_req_dmem 2 8 16 8 var.

Definition test_cpu_deq_req_dmem {var fn} :=
  fns.package_global_fns'' var fn (@test_cpu_deq_req_dmem_inner).
