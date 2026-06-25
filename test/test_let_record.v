From Ltac2 Require Import Ltac2.
From Stdlib Require Import BinInt BinNat.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr.
Import fn.
Local Open Scope N_scope.

Module SimpleRecord.
  Record SimpleRecord {var} (t : type) := {
    my_fn : fn var t t;
    my_fn2 : fn var t t;
  }.
End SimpleRecord. Notation SimpleRecord := SimpleRecord.SimpleRecord (only parsing).

Module my_mod.
  Section my_sec.
    Context {var : type -> Type}.
    Definition my_let : fn var (Bits 8%N) (Bits 8%N) := Fn (fun x => quartz_eexpr:(return (#x + 8%N 'd 1))).
    Definition my_let2 : fn var (Bits 8%N) (Bits 8%N) := Fn (fun x => quartz_eexpr:(
      let res := $(expr.Call my_let (expr.Var x)) in
      return (#res + 8%N 'd 2)
    )).
    Definition impl : @SimpleRecord var (Bits 8%N) := {|
      SimpleRecord.my_fn := my_let;
      SimpleRecord.my_fn2 := my_let2;
    |}.
  End my_sec.
End my_mod.

Definition get_my_fn {var} := @my_mod.my_let var.
Definition get_my_fn2 {var} := @my_mod.my_let2 var.

Definition test_let_record_inner {var} := @fn.Fn var _ _ (fun x => quartz_eexpr:(
  let res := $(expr.Call (@get_my_fn var) (expr.Var x)) in
  let res2 := $(expr.Call (@get_my_fn2 var) (expr.Var res)) in
  return #res2
)).

Definition test_let_record {var f} : fns.fns var f (Bits 8%N) (Bits 8%N) :=
  fns.package_global_fns'' var f (@test_let_record_inner).
Print test_let_record.
