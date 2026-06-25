From quartz.lang Require Import Syntax.
From quartz.lang Require Import Processor.
Import BinInt type.
Import Strings.String.
Local Open Scope string_scope.

Section __. Context (mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz : Z) {var : type -> Type}.

Definition cpu_tick :=
  ltac2:( Control.refine (fun () => rmonomorphize_fast '(@cpu.tick mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz var))).

Theorem cpu_tick_correct : @cpu_tick = @cpu.tick mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz var.
Proof.
  exact_no_check (eq_refl (@cpu_tick)).
Time Qed.

End __.
