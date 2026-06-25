From quartz.lang Require Import Syntax.
From quartz.examples Require Import Processor.
Import InterfaceExample.
From quartz.test Require Import test_cpu_tick_util.
Import BinNat type.
Import Strings.String.
Local Open Scope string_scope.

Section __. Context (mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz : N) {var : type -> Type}.

Definition test_cpu_tick_mono :=
  ltac2:( Control.refine (fun () => rmonomorphize_fast '(@cpu.tick mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz (@isMMIOAddr) var))).

Theorem test_cpu_tick_mono_correct : @test_cpu_tick_mono = @cpu.tick mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz (@isMMIOAddr) var.
Proof.
  exact_no_check (eq_refl (@test_cpu_tick_mono)).
Time Qed.

End __.
