#[export] Set Primitive Projections.

From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.

From quartz.lang Require Import Syntax.
From Stdlib Require Import BinInt Bits.
From Stdlib Require Import String List.
From Stdlib Require NArith Vector.
Import ListNotations.

From quartz.lang Require Import ident_to_string let_lift.

Module InterfaceExample.
Import fn.
Import type.
Open Scope Z_scope.

Module QStdlib.
  Import (notations) eexpr expr. Local Open Scope string_scope.

  Definition ExtractBits {var} (n s l: Z) : fn _ _ (Bits l) := Fn (fun b : var (Bits n) => quartz_eexpr:(
    let shift_amt : Bits n := _ 'd (n - s) in
    let shifted_b := #b >> #shift_amt in    
    return $(expr.Unop unop.UnsignedResize (expr.Var shifted_b)))).
  
End QStdlib.

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

  Record state := { valid : Bool; data : t; }.

  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let full {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..valid)).

  Let empty {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return ! #st..valid )).

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

  Lemma empty_ok (s : state) : fn.interp empty s = embed_bool (Zmod.eqb s.(valid) Zmod.zero).
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
    cbn -[Zmod.eqb]. (* reduces [#st..valid] in [length] even though [t] is abstract. *)
    case (Zmod.bool_cases (valid st)); cbv; congruence.
  Qed.
End fifo1. End fifo1.

(* Definition WIDTH : Z := 32. *)

Module Multiplier.

  Record Multiplier {var} {width : Z} {req: type} (t_state : type) := {
    peek : fn var t_state (type.Bits (width + width));
    full : fn var t_state type.Bool;
    respReady : fn var t_state type.Bool;
    enq : fn var (type.Pair t_state req) t_state; 
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
    valid : Bool; 
    op1 : Bits width;
    op2 : Bits width;
    result : Bits (width + width);
    nstep : Bits logNSteps;
    finished : Bool
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

  Let tick {var} := Fn (fun (st: var State) => quartz_eexpr:(
     if #st..valid & ! #st..finished then
       if !#st..op1 | !#st..op2 then (* zero-skip *)
         let st <- #st..finished = true in 
         let st <- #st..result = _ 'd 0 in 
         return #st
       else if #st..nstep ==  ~ (_ 'd 0) then (* == ones: done *)
         let op1 := #st..op1 in               
         let op2 := #st..op2 in               
         let st <- #st..finished = true in 
         let st <- #st..result = $(expr.Binop binop.Mul (expr.Var op1) (expr.Var op2))  in 
         return #st
       else 
         let st <- #st..nstep = (#st..nstep + _ 'd 1) in
         return #st
    else return #st)).

  Definition impl {var} : @Multiplier var width Req State := {|
    Multiplier.peek := peek;
    Multiplier.full := full;
    Multiplier.respReady := respReady;
    Multiplier.enq    := enq;
    Multiplier.deq := deq;
    Multiplier.tick := tick;
  |}.
  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := struct.rep &v in exact $t).
  Lemma peek_ok (s : state) : fn.interp peek s = s.(result).
  Proof. trivial. Qed.
  Lemma full_ok (s : state) : fn.interp full s = s.(valid).
  Proof. trivial. Qed.

End multiplier. End multiplier.

Module RfScored. Section RfScored.
Context {var: type -> Type}.
Context {log_nregs: Z}.

Notation t_idx := (Bits log_nregs).
  
Record RfScored (t_state t_data : type) := {
  acquireLock : fn var (Pair t_state t_idx) t_state;
  releaseLock : fn var (Pair t_state t_idx) t_state;
  writeAndRelease : fn var (Pair t_state (type.Pair t_idx t_data)) t_state;
  read : fn var (Pair t_state t_idx) t_data;
  isLocked : fn var (Pair t_state t_idx) Bool
}.
End RfScored. End RfScored. Notation RfScored := RfScored.RfScored (only parsing).

Module rfScored. Section rfScored.
  Context {var: type -> Type}.
  Context {log_nregs: Z}.
  Context (t_data : type).

  Notation t_idx := (Bits log_nregs).

  Definition nregs : nat := Z.to_nat (2^log_nregs).
  Notation state := (Vector.t (Bool * t_data) nregs).
  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  (* TODO: let '(_,_) syntax *)
  Let isLocked {var} : fn _ _ Bool := Fn (fun (p : var (Pair State t_idx)) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 in 
    return #st[#idx] .1)).

  Let read {var} : fn _ _ t_data := Fn (fun (p : var (Pair State t_idx)) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 in 
    return #st[#idx] .2)).

  (* TODO: #st[#idx].1 = true syntax *)
  Let acquireLock {var} := Fn (fun (p : var (Pair State t_idx)) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 in 
    let data := #st[#idx] .2 in                        
    let st <- #st[#idx] = (true, #data) in
    return #st)).

  Let releaseLock {var} := Fn (fun (p : var (Pair State t_idx)) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 in 
    let data := #st[#idx] .2 in                        
    let st <- #st[#idx] = (false, #data) in
    return #st)).

  Let writeAndRelease {var} := Fn (fun (p : var (Pair State (type.Pair t_idx t_data))) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 .1 in let data := #p .2 .2 in
    if #st[#idx].1 then (* locked *)
      let st <- #st[#idx] = (false, #data) in
      return #st
    else  (* Do nothing *)
      return #st)).

  Definition impl {var} : @RfScored var log_nregs State t_data := {|
    RfScored.acquireLock := acquireLock;
    RfScored.releaseLock := releaseLock;
    RfScored.writeAndRelease := writeAndRelease;
    RfScored.read := read;
    RfScored.isLocked := isLocked
  |}.

  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := &v in exact $t).

  (* TODO: vector access *)
  Lemma foo (s : state) idx data : 
    fn.interp writeAndRelease (s, (idx, data)) = s.
  Proof. 
    simpl.
  Abort.

End rfScored. End rfScored.

Module Bht. 
  Record Bht {var} {addr_sz} (t_state: type) := {
    update : fn var (Pair t_state (Pair (Bits addr_sz) Bool)) t_state; (* update (pc, taken) *)      
    ppcDp : fn var (Pair t_state (Pair (Bits addr_sz) (Bits addr_sz))) (Bits addr_sz); (* ppcDp (pc, targetPc) *)
  }.
End Bht. Notation Bht := Bht.Bht (only parsing).

Module bht. Section bht.
  Notation histLen := 2%Z.
  Context {idxSz : Z}.
  Notation lenHist := (2%Z).              
  Context {var: type -> Type}.
  Context {addrSz: Z}.

  Definition nEntries : nat := Z.to_nat (2^idxSz).

  Notation state := (Vector.t (Bits histLen) nEntries).
  Definition State := type.reify'' state.
  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let defaultNextPc {var} : fn _ _ (Bits addrSz) := Fn (fun (pc : var (Bits addrSz)) => quartz_eexpr:(
    return #pc + (_ 'd 4))).

  Let getIndex {var} : fn _ _ (Bits idxSz) := Fn (fun (pc : var (Bits addrSz)) => quartz_eexpr:(
    let shift_amt : Bits addrSz := _ 'd 2 in 
    let shifted_pc := #pc >> #shift_amt in
    return $(expr.Unop unop.UnsignedResize (expr.Var shifted_pc)))).

  Let computeTarget {var} : fn _ _ (Bits addrSz) := Fn (fun (args: var (Pair (Pair (Bits addrSz) (Bits addrSz)) Bool)) => quartz_eexpr:( 
    let pc := #args .1 .1 in let targetPc := #args .1 .2 in let taken := #args .2 in
    return if #taken then #targetPc else defaultNextPc (#pc))).

  Let extractDir {var} : fn _ _ Bool := Fn (fun (dp: var (Bits histLen)) => quartz_eexpr:(
    return (#dp == _ 'd 3) | (#dp == _ 'd 2)
  )).

  Let newDP {var} : fn _ _ (Bits histLen) := Fn (fun (p: var (Pair (Bits histLen) Bool)) => quartz_eexpr:(
    let dpBits := #p .1 in let taken := #p .2 in
    if #taken then
      return (if #dpBits == _ 'd 3 then #dpBits else #dpBits + _ 'd 1)
    else 
      return (if ! #dpBits then #dpBits else #dpBits - _ 'd 1)
 )).

  Let ppcDp {var} : fn _ _ (Bits addrSz) := Fn (fun (p: var (Pair State (Pair (Bits addrSz) (Bits addrSz)))) => quartz_eexpr:(
    let st := #p .1 in let pc := #p .2 .1 in let targetPc := #p .2 .2 in
    let index := getIndex ( #pc ) in
    let entry := #st[#index] in
    let direction := extractDir (#entry) in
    return computeTarget ( ((#pc, #targetPc), #direction) )
  )).

  Let update {var} : fn _ _ State := Fn (fun (p: var (Pair State (Pair (Bits addrSz) Bool))) => quartz_eexpr:(
     let st := #p .1 in let pc := #p .2 .1 in let taken := #p .2 .2 in
     let index := getIndex ( #pc ) in
     let entry := #st[#index] in
     let dp' := newDP ( (#entry, #taken) ) in
     let st <- #st[#index] = #dp' in
     return #st
  )).

  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := &v in exact $t).

  Definition impl {var} : @Bht var addrSz State := {|
    Bht.update := update;
    Bht.ppcDp := ppcDp
  |}.

 
End bht. End bht.

Module Btb. 
  Record Btb {var} {addrSz} (t_state: type) := {
    update : fn var (Pair t_state (Pair (Bits addrSz) (Bits addrSz))) t_state; (* update (pc, nextPc *)  
    predPc : fn var (Pair t_state (Bits addrSz)) (Bits addrSz)
  }.
End Btb. Notation Btb := Btb.Btb (only parsing).

Module btb. Section btb.
  Context {addrSz: Z}.              
  Context {tagSz: Z}.              
  Context {idxSz: Z}.

  Definition nEntries : nat := Z.to_nat (2^idxSz).
             
  Record state := { targets: Vector.t (Bits addrSz) nEntries;
                    tags : Vector.t (Bits tagSz) nEntries;
                    valid : Vector.t Bool nEntries }. 

  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let getIndex {var} : fn _ _ (Bits idxSz) := 
      @QStdlib.ExtractBits var addrSz 2 idxSz.  
  Let getTag {var} : fn _ _ (Bits tagSz) := 
      @QStdlib.ExtractBits var addrSz (addrSz - tagSz) tagSz. 

  Let defaultNextPc {var} : fn _ _ (Bits addrSz) := Fn (fun (pc : var (Bits addrSz)) => quartz_eexpr:(
    return #pc + (_ 'd 4))).

  Let predPc {var} : fn _ _ (Bits addrSz) := Fn (fun (p: var (Pair State (Bits addrSz))) => quartz_eexpr:( 
    let st := #p .1 in let pc := #p .2 in 
    let index := getIndex (#pc) in
    let tag := getTag (#pc) in
    let lookup_tag := #st..tags[#index] in
    let lookup_valid := #st..valid[#index] in
    if (#lookup_tag == #tag) & #lookup_valid  then
      let target := #st..targets[#index] in
      return #target
    else
      return defaultNextPc (#pc)
  )).

  Let update {var} : fn _ _ State := Fn (fun (p: var (Pair State (Pair (Bits addrSz) (Bits addrSz)))) => quartz_eexpr:(
    let st := #p .1 in let pc := #p .2 .1 in let nextPc := #p .2 .2 in
    let index := getIndex (#pc) in
    let tag := getTag (#pc) in
    let lookup_tag := #st..tags[#index] in
    if ~ (#nextPc == defaultNextPc (#pc)) then
      (* TODO: updating a submodule array *)
      let valid' <- (#st..valid)[#index] = true in            
      let targets' <- (#st..targets)[#index] = #nextPc in            
      let tags' <- (#st..tags)[#index] = #tag in            
      let st <- #st..valid = #valid' in
      let st <- #st..targets = #targets' in
      let st <- #st..tags = #tags' in
      return #st
    else
      return #st                                            
  )). 

  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := struct.rep &v in exact $t).

  Definition impl {var} : @Btb var addrSz State := {|
    Btb.update := update;
    Btb.predPc := predPc 
  |}.

End btb. End btb.

End InterfaceExample.
