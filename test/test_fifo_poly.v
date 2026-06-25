From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt Bits String.
Require Import quartz.lang.Syntax. Import Syntax.type.
Require Import quartz.lang.domain.
Import (coercions) domain.Zmod.
Import (notations) type expr eexpr.

Local Open Scope string_scope.
Import fn.
Module Import Fifo.
Record Fifo {var : type -> Type} {fn : type -> type -> Type} {t_state t_data : type} := {
  cap      : fn t_state (type.Bits 32);
  length   : fn t_state (type.Bits 32);
  full     : fn t_state type.Bool;
  empty    : fn t_state type.Bool;
  enq      : fn (type.Pair t_state t_data) t_state;
  deq      : fn t_state (type.Pair t_state t_data)
}.
End Fifo. Notation Fifo := Fifo.Fifo (only parsing).
Arguments Fifo : clear implicits.

Module fifo1. Section fifo1.
  Context (t : type).

  Record state := { valid : Bool; payload : t; }.

  Definition State := type.reify'' state.

  Local Open Scope string_scope.

  Definition cap {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return 32 'd 1)).

  Definition length {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return if #st..valid then 32 'd 1 else 32 'd 0)).

  Definition full {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..valid)).

  Definition empty {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return ! #st..valid)).

  Definition enq {var} := Fn (fun (p : var (type.Pair State t)) => quartz_eexpr:(
      let st := #p .1 in let d  := #p .2 in
    let st <- #st..valid = true in
    let st <- #st..payload = $(expr.Var d) in

    return #st)).

  Definition deq {var} := Fn (fun (st : var State) => quartz_eexpr:(
    let out_d := #st..payload in
    let st_new <- #st..valid = false in
    return (#st_new, #out_d))).

  Definition impl {var} : @Fifo var (fn.fn var) State t := {|
    Fifo.cap    := cap;
    Fifo.length := length;
    Fifo.full   := full;
    Fifo.empty  := empty;
    Fifo.enq    := enq;
    Fifo.deq    := deq
  |}.

  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := struct.rep &v in exact $t).

  Lemma empty_ok (s : state) : fn.interp empty s = Zmod.eqb s.(valid) Zmod.zero.
  Proof. trivial. Qed.

  Lemma not_full_and_empty (st : state) :
    fn.interp empty st <> fn.interp full st.
  Proof.
    cbn -[Zmod.eqb]. (* reduces [#st..valid] in [length] even though [t] is abstract. *)
    (* embed_bool (Zmod.eqb 0 (valid st)) <> valid st *) destruct (Zmod.bool_cases (valid st)); cbv; congruence.
  Qed.
End fifo1. End fifo1.

Definition test_fifo_poly_inner {var : type -> Type} := @fn.Fn var _ _ (fun p => quartz_eexpr:(
  let st1 := #p .1 in
  let st2 := #p .2 in
  let p1 := (#st1, 8 'd 42) in
  let st1_new := $(expr.Call (fifo1.enq (type.Bits 8)) (expr.Var p1)) in
  let p2 := (#st2, true) in
  let st2_new := $(expr.Call (fifo1.enq type.Bool) (expr.Var p2)) in
  return (#st1_new, #st2_new))).

Definition test_fifo_poly {var : type -> Type} {fn : type -> type -> Type} := fns.package_global_fns'' var fn (@test_fifo_poly_inner).
Lemma interp_reified : fns.interp test_fifo_poly = interp test_fifo_poly_inner. exact eq_refl. Qed.
