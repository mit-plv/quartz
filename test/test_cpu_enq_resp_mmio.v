From Stdlib Require Import BinInt BinNat.
Require Import quartz.lang.Syntax.
Require Import quartz.examples.Processor.
Import InterfaceExample.
Local Open Scope N_scope.

Definition test_cpu_enq_resp_mmio_inner {var} := @cpu.enq_resp_mmio 2 8 16 8 var.

Definition test_cpu_enq_resp_mmio {var fn} :=
  fns.package_global_fns'' var fn (@test_cpu_enq_resp_mmio_inner).
