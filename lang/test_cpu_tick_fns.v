From Ltac2 Require Import Ltac2 Printf.
From quartz.lang Require Import Syntax Processor test_cpu_tick sv.
Import BinInt type fn.

Section __.
  Context (mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz : Z).
  Context {var : Syntax.type.type -> Type}.
  Context {fn : Syntax.type.type -> Syntax.type.type -> Type}.

  Definition cpu_tick_fns : fns.fns var fn _ _ :=
    fns.package_global_fns'' var fn (@cpu.tick mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz).
End __.

Lemma cpu_tick_equiv (mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz : Z) :
  fns.interp (cpu_tick_fns mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz) =
  fn.interp (@cpu.tick mul_LogNSteps bht_idxSz btb_tagSz btb_idxSz type.interp).
Proof. exact eq_refl. Qed.

Definition cpu_tick_verilog : String.string :=
  sv.pp (cpu_tick_fns 2 8 16 8 (var := sv.var) (fn := sv.fn)).
