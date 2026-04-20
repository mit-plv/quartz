#[export] Set Primitive Projections.

From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.

From quartz.lang Require Import Syntax.
From Stdlib Require Import BinInt Bits.
From Stdlib Require Import String List.
From Stdlib Require Vector.
Import ListNotations.

From quartz.lang Require Import ident_to_string let_lift.

Module InterfaceExample.
Import fn.
Import type.
Open Scope Z_scope.

Module Fifo.
Record Fifo {var} (t_state t_data : type) := {
  first    : fn var t_state t_data;
  empty    : fn var t_state type.Bool;
  full     : fn var t_state type.Bool;
  enq      : fn var (type.Pair t_state t_data) t_state;  
  deq      : fn var t_state t_state;  
}.
End Fifo. Notation Fifo := Fifo.Fifo (only parsing).

Module fifo1. Section fifo1.
  Context (t : type).

  Record state := { valid : bool; data : t; }.

  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let full {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..valid)).

  Let empty {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return if #st..valid then false else true)).

  Let first {var} := Fn (fun (st : var State) => quartz_eexpr:(
    let out_d := #st..data in
    return (#out_d))).

  Let enq {var} := Fn (fun (p : var (type.Pair State t)) => quartz_eexpr:(
    let st := #p .1 in let d  := #p .2 in
    let is_full := full ( #st ) (* #st..valid  *)in                        
    let st <- #st..valid = true in
    let st <- #st..data = (if #is_full then #st..data else #d) in
    return #st)).

  Let deq {var} := Fn (fun (st : var State) => quartz_eexpr:(
    let st_new <- #st..valid = false in
    return (#st_new))).

  Definition impl {var} : @Fifo var State t := {|
    Fifo.first := first;
    Fifo.empty := empty;
    Fifo.full   := full;
    Fifo.enq    := enq;
    Fifo.deq    := deq
  |}.

  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := struct.rep &v in exact $t).

  Lemma first_ok (s : state) : fn.interp first s = s.(data).
  Proof. trivial. Qed.
  Lemma full_ok (s : state) : fn.interp full s = s.(valid).
  Proof. trivial. Qed.
  Lemma empty_ok (s : state) : fn.interp empty s = negb s.(valid).
  Proof. trivial. Qed.

  Lemma enq_ok (s : state) x :
    fn.interp full s = false ->
    fn.interp enq (rep s,x) = (rep {| valid := true; data := x |}).
  Proof. cbn. intros * hvalid. rewrite hvalid. trivial. Qed.

  Lemma deq_ok (s : state) :
    fn.interp deq s = (rep {| valid := false; data := s.(data) |}).
  Proof. trivial. Qed.

  Lemma not_full_and_empty (st : state) :
    fn.interp empty st <> fn.interp full st.
  Proof.
    cbn. (* reduces [#st..valid] in [length] even though [t] is abstract. *)
    (* (if valid st then false else true) <> valid st *) destruct (valid st); congruence.
  Qed.
End fifo1. End fifo1.

(* Definition WIDTH : Z := 32. *)

Module Multiplier.

  Record Multiplier {var} {width : Z} {req: Z -> type} (t_state : type) := {
    peek : fn var t_state (type.Bits (width + width));
    full : fn var t_state type.Bool;
    respReady : fn var t_state type.Bool;
    enq : fn var (type.Pair t_state (req width)) t_state; 
    deq : fn var t_state t_state; 
    tick : fn var t_state t_state;
  }.
  
End Multiplier. Notation Multiplier:= Multiplier.Multiplier (only parsing).

Module multiplier. Section multiplier.
  Context (width : Z).
  Context (logNSteps : Z).

  Record req_t := { input_a : Bits width; input_b : Bits width}.
  Definition Req := type.reify'' req_t.

  Record state := { 
    valid : bool; 
    op1 : Bits width;
    op2 : Bits width;
    result : Bits (width + width);
    nstep : Bits logNSteps;
    finished : bool
  }. 

  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let peek {var} := Fn (fun (st : var State) => quartz_eexpr:(
    let out := #st..result in
    return (#out))).

  Let full {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..valid)).

  Let respReady {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..finished)).

  (* TODO: reification of types in other types. *)
  Let enq {var} := Fn (fun (p : var (type.Pair State Req)) => quartz_eexpr:(
    let st := #p .1 in let d  := #p .2 in
    let is_full := full ( #st ) in                        
    if #is_full then
      return #st 
    else 
      let st <- #st..valid = true in
      let st <- #st..op1 = #d..input_a in
      let st <- #st..op2 = #d..input_b in
      let st <- #st..finished = false in
      let st <- #st..nstep = _ 'd 0 in
      return #st)).

  Let deq {var} := Fn (fun (st : var State) => quartz_eexpr:(
    if #st..finished then
      let st <- #st..valid = false in
      let st <- #st..finished = false in 
      return #st 
    else return #st)).

  (* TODO: Boolean and *)
  Let tick {var} := Fn (fun (st: var State) => quartz_eexpr:(
     if #st..valid && ! #st..finished then
       return #st 
     else (* No valid request *)
       return #st)).
  ).

End multiplier. End multiplier.

End InterfaceExample.
