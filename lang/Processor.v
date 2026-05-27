#[export] Set Primitive Projections.
From stdpp Require Import bitvector.definitions (* vector *).

From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.

From quartz.lang Require Import domain Syntax. (* Import (coercions) domain.Zmod. *)
From Stdlib Require Import BinInt.
From Stdlib Require Import String List.
From Stdlib Require NArith Vector.
(* Import ListNotations. *)

From quartz.lang Require Import ident_to_string let_lift.

Module InterfaceExample.
Import fn.
Import type.
(* Open Scope Z_scope. *)

(* TODO: sum types? *)

Import (coercions) BV.
Module QStdlib.
  Import (notations) eexpr expr. Local Open Scope string_scope.

  Definition ExtractBits {var} {n} (s: Z) {l: N} : fn _ _ (Bits l) := Fn (fun b : var (Bits n) => quartz_eexpr:(
    let shift_amt : Bits n := _ 'd s in
    let shifted_b := #b >> #shift_amt in    
    return $(expr.Unop unop.UnsignedResize (expr.Var shifted_b)))).

  (* Concatenate bitvectors, matching [bv_concat sz hi lo] semantics.
     Result width is explicitly [sz] (typically [sz = hi_w + lo_w]).
   *)
  Definition Concat {var} {sz : N} {hi_w lo_w : N}
    : fn _ (type.Pair (Bits hi_w) (Bits lo_w)) (Bits sz) :=
    let lo_w' := Z.of_N lo_w in 
    Fn (fun p : var (type.Pair (Bits hi_w) (Bits lo_w)) => quartz_eexpr:(
      let hi := #p .1 in
      let lo := #p .2 in
      let hi' : Bits sz := $(expr.Unop unop.UnsignedResize (expr.Var hi)) in
      let lo' : Bits sz := $(expr.Unop unop.UnsignedResize (expr.Var lo)) in
      let sh : Bits sz := _ 'd lo_w' in
      return ((#hi' << #sh) | #lo')
    )).

  Declare Custom Entry quartz_struct_init.

  Notation "f ':=' v" :=
   (fun r =>
     quartz_eexpr:(
       let s <- $r..f = $v in
       return #s
     ))
   (in custom quartz_struct_init at level 0,
    f global,
    v custom quartz_expr at level 200).
  Notation "a ';' b" :=
   (fun s =>
     eexpr.Bind "StructInit" (a s) (fun s' => b (expr.Var s')))
   (in custom quartz_struct_init at level 91,
    right associativity,
    a custom quartz_struct_init,
    b custom quartz_struct_init).
  Notation "'init_struct' t '{' fields '}'" :=
   (fields (expr.Const (type.default t)))
   (in custom quartz_eexpr at level 200,
    t constr at level 0,
    fields custom quartz_struct_init at level 92).
  Notation "'init_struct' t '{' '}'" :=
   (quartz_eexpr:(return $(expr.Const (type.default t))))
   (in custom quartz_eexpr at level 200,
    t constr at level 0).

  Notation "'{' f '}' '(' e ')'" := (expr.Call f e)
    (in custom quartz_expr at level 0, left associativity, f constr , e custom quartz_expr at level 200).

  Module StructTest.
  End StructTest.
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

  (* TODO: bool state type? *)
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
    if #is_full then
      return #st
    else
      let st <- #st..valid = true in
      let st <- #st..data = #d in
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

  Lemma empty_ok (s : state) : fn.interp empty s = 
                                 (bv_unsigned s.(valid) =? 0)%Z.
  Proof. 
trivial. Qed.

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
    cbn. 
    case (BV.bool_cases (valid st)); vm_compute bool_decide; 
      cbv[bool_to_bv]; discriminate.
  Qed.
End fifo1. End fifo1.

(* Definition WIDTH : Z := 32. *)

Module Multiplier.

  Record Multiplier {var} {width : N} {req: type} (t_state : type) := {
    peek : fn var t_state (type.Bits (width + width));
    full : fn var t_state type.Bool;
    respReady : fn var t_state type.Bool;
    enq : fn var (type.Pair t_state req) t_state; 
    deq : fn var t_state t_state; 
    tick : fn var t_state t_state;
  }.
  
End Multiplier. Notation Multiplier:= Multiplier.Multiplier (only parsing).

Module multiplier. Section multiplier.
  (* Context {width : Z}. *)
  Notation width := 32%N.
  Context (logNSteps : N).

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

  Definition peek {var} := Fn (fun (st : var State) => quartz_eexpr:(
    let out := #st..result in
    return (#out))).

  Definition full {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..valid)).

  Definition respReady {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..finished)).

  (* TODO: reification of types in other types. *)
  Definition enq {var} := Fn (fun (p : var (type.Pair State Req)) => quartz_eexpr:(
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

  Definition deq {var} := Fn (fun (st : var State) => quartz_eexpr:(
    if #st..finished then
      let st <- #st..valid = false in
      let st <- #st..finished = false in 
      return #st 
    else return #st)).

  Definition tick {var} := Fn (fun (st: var State) => quartz_eexpr:(
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
Context {log_nregs: N}.

Notation t_idx := (Bits log_nregs).
  
Record RfScored {t_state t_data : type} := {
  acquireLock : fn var (Pair t_state t_idx) t_state;
  releaseLock : fn var (Pair t_state t_idx) t_state;
  writeAndRelease : fn var (Pair t_state (type.Pair t_idx t_data)) t_state;
  read : fn var (Pair t_state t_idx) t_data;
  isLocked : fn var (Pair t_state t_idx) Bool
}.
End RfScored. End RfScored. Notation RfScored := RfScored.RfScored (only parsing).
Module rfScored. 
  (* TODO: non-record type *)
  Notation state' t_data nregs := (vector.vec (Bool * t_data) nregs).
  Section rfScored.
  Context {var: type -> Type}.
  Context {log_nregs: N}.
  Context (t_data : type).
  Notation t_idx := (Bits log_nregs).
  Definition nregs : nat := N.to_nat (2^log_nregs).
  Notation state := (state' t_data nregs).
  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  (* TODO: let '(_,_) syntax *)
  Let isLocked {var} : fn _ _ Bool := Fn (fun (p : var (Pair State t_idx)) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 in 
    return #st[#idx] .1)).

  Let read {var} : fn _ _ t_data := Fn (fun (p : var (Pair State t_idx)) => quartz_eexpr:(
    let st := #p .1 in let idx := #p .2 in 
    if !#idx then
      return const (default t_data)
    else
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
  Notation histLen := 2%N.
  Context {idxSz : N}.
  Notation lenHist := (2%N).              
  Context {var: type -> Type}.
  Context {addrSz: N}.

  Definition nEntries : nat := N.to_nat (2^idxSz).

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
  Context {addrSz: N}.              
  Context {tagSz: N}.              
  Context {idxSz: N}.

  Definition nEntries : nat := N.to_nat (2^idxSz).
             
  Record state := { targets: Vector.t (Bits addrSz) nEntries;
                    tags : Vector.t (Bits tagSz) nEntries;
                    valid : Vector.t Bool nEntries }. 

  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let getIndex {var} : fn _ _ (Bits idxSz) := 
      @QStdlib.ExtractBits var addrSz 2 idxSz.  
  Let getTag {var} : fn _ _ (Bits tagSz) := 
      @QStdlib.ExtractBits var addrSz (Z.of_N (addrSz - tagSz)) tagSz. 

  Let defaultNextPc {var} : fn _ _ (Bits addrSz) := Fn (fun (pc : var (Bits addrSz)) => quartz_eexpr:(
    return #pc + (_ 'd 4))).
  Import QStdlib.
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

Module CsrFile.
  Record CsrFile {var} {idxSz} {wordSz} {t_state: type} := {
    readCsr : fn var (Pair t_state (Bits idxSz)) (Bits wordSz);
    writeCsr : fn var (Pair t_state (Pair (Bits idxSz) (Bits wordSz))) t_state
  }.

End CsrFile. Notation CsrFile := CsrFile.CsrFile (only parsing).

Module csrFile. Section csrFile.
  Notation CsrIdx := (Bits 12) (only parsing).
  Notation mword := (Bits 32).
  Definition CSR_mtvec : CsrIdx := Z_to_bv _ 773.
  Definition CSR_mepc : CsrIdx := Z_to_bv _ 833.
  Definition CSR_mcause : CsrIdx := Z_to_bv _ 834.
  Definition CSR_mtval : CsrIdx := Z_to_bv _ 835.
  Definition CSR_mie : CsrIdx := Z_to_bv _ 0x304. 

  Record state := { csr_mtvec : mword;
                    csr_mepc : mword;
                    csr_mcause : mword;
                    csr_mtval : mword;
                    csr_mie : mword 
                  }.
  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let readCsr {var} : fn _ _ mword := Fn (fun (p : var (Pair State CsrIdx)) => quartz_eexpr:(
    let st := #p .1 in let csr := #p .2 in
    if #csr == const CSR_mtvec then return #st..csr_mtvec
    else if #csr == const CSR_mepc then return #st..csr_mepc
    else if #csr == const CSR_mcause then return #st..csr_mcause
    else if #csr == const CSR_mtval then return #st..csr_mtval
    else if #csr == const CSR_mie then return #st..csr_mie
    else return _ 'd 0
  )).

  Let writeCsr {var} : fn _ _ State := Fn (fun (p : var (Pair State (Pair CsrIdx mword))) => quartz_eexpr:(
    let st := #p .1 in let csr := #p .2 .1 in let val := #p .2 .2 in
    if #csr == const CSR_mtvec then
      let st <- #st..csr_mtvec = #val in return #st
    else if #csr == const CSR_mepc  then
      let st <- #st..csr_mepc = #val in return #st
    else if #csr == const CSR_mcause then
      let st <- #st..csr_mcause = #val in return #st
    else if #csr == const CSR_mtval then
      let st <- #st..csr_mtval = #val in return #st
    else if #csr == const CSR_mie then
      let st <- #st..csr_mie = #val in return #st
    else return #st
  )).

  Definition impl {var} : @CsrFile var 12 32 State := {|
    CsrFile.readCsr := readCsr;
    CsrFile.writeCsr := writeCsr
  |}.

End csrFile. End csrFile.

Module Decode. Section Decode.
  Import QStdlib.
  Import (notations) eexpr expr. Local Open Scope string_scope.


  Notation CsrIdx := (Bits 12) (only parsing).
  Notation mword := (Bits 32) (only parsing).
  Notation RegIdx := (Bits 5) (only parsing).

  Notation ImmType := (Bits 3) (only parsing).
  Definition Imm_none : ImmType := Z_to_bv _ 0.
  Definition Imm_I : ImmType    := Z_to_bv _ 1.
  Definition Imm_S : ImmType    := Z_to_bv _ 2.
  Definition Imm_B : ImmType    := Z_to_bv _ 3.
  Definition Imm_U : ImmType    := Z_to_bv _ 4.

  Notation InstType := (Bits 3) (only parsing).
  Definition Inst_Illegal : InstType := Z_to_bv _ 0.
  Definition Inst_Store : InstType   := Z_to_bv _ 1.
  Definition Inst_Load : InstType    := Z_to_bv _ 2.
  Definition Inst_Mul : InstType     := Z_to_bv _ 3.
  Definition Inst_Alu : InstType     := Z_to_bv _ 4.
  Definition Inst_Ctrl : InstType    := Z_to_bv _ 5.
  Definition Inst_System : InstType  := Z_to_bv _ 6.

  Record instrProps :=
  { rs1Valid : Bool;
    rs2Valid : Bool;
    rdValid : Bool;
    itype : InstType; 
    immediateType : ImmType;
  }.
  Definition InstrProps := type.reify'' instrProps.

  Record decodeFields :=
  { D_rs1Idx : RegIdx;
    D_rs2Idx : RegIdx;
    D_rdIdx  : RegIdx;
    D_csrIdx : CsrIdx;
    D_immI   : mword;
    D_immS   : mword;
    D_immB   : mword;
    D_immU   : mword;
    D_csr    : CsrIdx;
    D_opcode : Bits 7;
    D_funct3 : Bits 3;
    D_funct7 : Bits 7;
  }.
  Definition DecodeFields := type.reify'' decodeFields.

  Let Funct7 {var} : fn var (Bits 32) (Bits 7) :=
      ExtractBits 25 .
  Let Funct3 {var} : fn var (Bits 32) (Bits 3) := 
      ExtractBits 12 .  
  Let Opcode {var} : fn var (Bits 32) (Bits 7) := 
      ExtractBits 0 .  
  Let Csr12 {var} : fn var (Bits 32) (Bits 12) :=
      ExtractBits 20 .

  (* Field extractors mirroring [griffin/isaSpec/IsaParams.v:getFields]. *)
  Let Rs1Idx {var} : fn var (Bits 32) (Bits 5) :=
    QStdlib.ExtractBits 15.
  Let Rs2Idx {var} : fn var (Bits 32) (Bits 5) :=
    QStdlib.ExtractBits 20.
  Let RdIdx {var} : fn var (Bits 32) (Bits 5) :=
    QStdlib.ExtractBits 7.


  (* Immediate constructors (all sign-extended to 32 bits). *)
  Let ImmI {var} : fn var (Bits 32) (Bits 32) := Fn (fun (inst: var mword) => quartz_eexpr:(
  let imm12 : Bits 12 := { ExtractBits 20} ( #inst ) in
  return $(expr.Unop unop.SignedResize (expr.Var imm12))
  )).

  Let ImmS {var} : fn var (Bits 32) (Bits 32) := Fn (fun (inst: var mword) => quartz_eexpr:(
  let hi7 : Bits 7 := { ExtractBits 25 } ( #inst ) in
  let lo5 : Bits 5 := { ExtractBits 7 } (#inst ) in
  let imm12 : Bits 12 := Concat ((#hi7, #lo5)) in
  return $(expr.Unop unop.SignedResize (expr.Var imm12))
  )).

  Let ImmB {var} : fn var (Bits 32) (Bits 32) := Fn (fun (inst: var mword) => quartz_eexpr:(
  let imm_bit31 : Bits 1 := { ExtractBits 31 } ( #inst ) in
  let imm_bit7 : Bits 1 := { ExtractBits 7 } ( #inst ) in
  let imm_bits25_6 : Bits 6 := { ExtractBits 25 } ( #inst ) in
  let imm_bits8_4 : Bits 4 := { ExtractBits 8 } ( #inst ) in
  let imm_bits12_11 : Bits 2 := QStdlib.Concat ((#imm_bit31, #imm_bit7)) in
  let imm_bits10_1 : Bits 10 := QStdlib.Concat ((#imm_bits25_6, #imm_bits8_4)) in
  let imm_bits12_1 : Bits 12 := QStdlib.Concat ((#imm_bits12_11, #imm_bits10_1)) in
  let imm_bit0 : Bits 1 := _ 'd 0 in
  let imm13 : Bits 13 := QStdlib.Concat ((#imm_bits12_1, #imm_bit0)) in
  return $(expr.Unop unop.SignedResize (expr.Var imm13))
  )).

  Let ImmU {var} : fn var (Bits 32) (Bits 32) := Fn (fun (inst: var mword) => quartz_eexpr:(
  let u20 : Bits 20 := {ExtractBits 12} ( #inst ) in
  let z12 : Bits 12 := _ 'd 0 in
  let imm32 : Bits 32 := Concat ((#u20, #z12)) in
  return #imm32
  )).

  (* Bundles all raw instruction fields; mirrors [griffin/isaSpec/IsaParams.v:getFields]. *)
  Definition getFields {var} : fn var (Bits 32) DecodeFields := Fn (fun (inst: var mword) => quartz_eexpr:(
    let rs1Idx := Rs1Idx ( #inst ) in
    let rs2Idx := Rs2Idx ( #inst ) in
    let rdIdx  := RdIdx  ( #inst ) in
    let csrIdx := Csr12  ( #inst ) in
    let immI   := ImmI   ( #inst ) in
    let immS   := ImmS   ( #inst ) in
    let immB   := ImmB   ( #inst ) in
    let immU   := ImmU   ( #inst ) in
    let opcode := Opcode ( #inst ) in
    let funct3 := Funct3 ( #inst ) in
    let funct7 := Funct7 ( #inst ) in
    let ret <- init_struct DecodeFields {
      D_rs1Idx := #rs1Idx;
      D_rs2Idx := #rs2Idx;
      D_rdIdx  := #rdIdx;
      D_csrIdx := #csrIdx;
      D_immI   := #immI;
      D_immS   := #immS;
      D_immB   := #immB;
      D_immU   := #immU;
      D_csr    := #csrIdx;
      D_opcode := #opcode;
      D_funct3 := #funct3;
      D_funct7 := #funct7
    } in
    return #ret
  )).

  Definition opcode_LOAD : Bits 7 := Z_to_bv _ 3.
  Definition opcode_OP_IMM : Bits 7 := Z_to_bv _ 19.
  Definition opcode_AUIPC : Bits 7 := Z_to_bv _ 23.
  Definition opcode_STORE : Bits 7 := Z_to_bv _ 35.
  Definition opcode_OP : Bits 7 := Z_to_bv _ 51.
  Definition opcode_BRANCH : Bits 7 := Z_to_bv _ 99.
  Definition opcode_JALR : Bits 7 := Z_to_bv _ 103.
  Definition opcode_SYSTEM : Bits 7 := Z_to_bv _ 115.

  Definition funct3_LW : Bits 3 := Z_to_bv _ 2.
  Definition funct3_ADDI : Bits 3 := Z_to_bv _ 0.
  Definition funct3_SW : Bits 3 := Z_to_bv _ 2.
  Definition funct3_ADD : Bits 3 := Z_to_bv _ 0.
  Definition funct7_ADD : Bits 7 := Z_to_bv _ 0.
  Definition funct3_MUL : Bits 3 := Z_to_bv _ 0.
  Definition funct7_MUL : Bits 7 := Z_to_bv _ 1.
  Definition funct3_BEQ : Bits 3 := Z_to_bv _ 0.
  Definition funct3_JALR : Bits 3 := Z_to_bv _ 0.
  Definition funct3_CSRRW : Bits 3 := Z_to_bv _ 1.

  Definition getInstrProps {var} : fn var _ InstrProps := Fn (fun (inst: var mword) => quartz_eexpr:(
    let opcode := Opcode ( #inst ) in
    let funct3 := Funct3 ( #inst ) in
    let funct7 := Funct7 ( #inst ) in
    let csr12 := Csr12 ( #inst ) in
    let illegal <- init_struct InstrProps { 
                  rs1Valid := false;
                  rs2Valid := false;
                  rdValid := false;
                  itype := const Inst_Illegal;
                  immediateType := const Imm_none } in
    let ret <- init_struct InstrProps { 
                  rs1Valid := false;
                  rs2Valid := false;
                  rdValid := false;
                  itype := const Inst_Illegal;
                  immediateType := const Imm_none } in
    (* LW: load *)
    if (#opcode == const opcode_LOAD) & (#funct3 == const funct3_LW) then
       init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := false;
                    rdValid := true;
                    itype := const Inst_Load;
                    immediateType := const Imm_I } 
    else 
    (* ADDI: alu immediate *)
    if (#opcode == const opcode_OP_IMM) & (#funct3 == const funct3_ADDI) then
      init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := false;
                    rdValid := true;
                    itype := const Inst_Alu;
                    immediateType := const Imm_I }
    else 
    (* AUIPC *)
    if #opcode == const opcode_AUIPC then
       init_struct InstrProps { 
                    rs1Valid := false;
                    rs2Valid := false;
                    rdValid := true;
                    itype := const Inst_Alu;
                    immediateType := const Imm_U } 
    else 
    (* SW: store *)
    if (#opcode == const opcode_STORE) & (#funct3 == const funct3_SW) then
       init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := true;
                    rdValid := false;
                    itype := const Inst_Store;
                    immediateType := const Imm_S }
    else 
    (* ADD: alu register *)
    if (#opcode == const opcode_OP) & (#funct3 == const funct3_ADD) & (#funct7 == const funct7_ADD) then
       init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := true;
                    rdValid := true;
                    itype := const Inst_Alu;
                    immediateType := const Imm_none } 
    else 
    (* BEQ: branch *)
    if (#opcode == const opcode_BRANCH) & (#funct3 == const funct3_BEQ) then
       init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := true;
                    rdValid := false;
                    itype := const Inst_Ctrl;
                    immediateType := const Imm_B }
    else 
    (* JALR: jump and link register *)
    if (#opcode == const opcode_JALR) & (#funct3 == const funct3_JALR) then
       init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := false;
                    rdValid := true;
                    itype := const Inst_Ctrl;
                    immediateType := const Imm_I }
    else 
    (* MUL *)
    if (#opcode == const opcode_OP) & (#funct3 == const funct3_MUL) & (#funct7 == const funct7_MUL) then
      init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := true;
                    rdValid := true;
                    itype := const Inst_Mul;
                    immediateType := const Imm_none }
    else 
    (* CSRRW: system *)
    if (#opcode == const opcode_SYSTEM) & (#funct3 == const funct3_CSRRW) then
      init_struct InstrProps { 
                    rs1Valid := true;
                    rs2Valid := false;
                    rdValid := true;
                    itype := const Inst_System;
                    immediateType := const Imm_none }
    else
      return #illegal
  )).

  Definition getImm {var} : fn var _ mword := Fn (fun (p: var (Pair DecodeFields InstrProps)) => quartz_eexpr:(
    let flds := #p.1 in let props := #p.2 in 
    if (#props..immediateType == const Imm_I) then return #flds..D_immI
    else if (#props..immediateType == const Imm_S) then return #flds..D_immS
    else if (#props..immediateType == const Imm_B) then return #flds..D_immB
    else if (#props..immediateType == const Imm_U) then return #flds..D_immU
    else return _ 'd 0)).

  Record aluInput :=
  { alu_in_flds: DecodeFields;
    alu_in_props : InstrProps;
    alu_in_rs1val : mword;
    alu_in_rs2val: mword;
    alu_in_csrval : mword;
    alu_in_pc : mword
  }.
  Definition AluInput := type.reify'' aluInput.

  Record aluOutput :=
  { alu_out_reg : mword;
    alu_out_csr : mword
  }.
  Definition AluOutput := type.reify'' aluOutput.

  Definition execALU {var} : fn var _ AluOutput := 
    Fn (fun (p: var AluInput) => quartz_eexpr:(
      let imm := getImm ((#p..alu_in_flds, #p..alu_in_props)) in 
      if (#p..alu_in_flds..D_opcode == const opcode_AUIPC) then
        init_struct AluOutput { alu_out_reg := #p..alu_in_pc + #imm;
                                          alu_out_csr := _ 'd 0 } 
      else if (#p..alu_in_flds..D_opcode == const opcode_SYSTEM) then
        init_struct AluOutput { alu_out_reg := #p..alu_in_csrval;
                                          alu_out_csr := #p..alu_in_rs1val }
      else 
        let alu_src1 := #p..alu_in_rs1val in 
        let alu_src2 := if (#p..alu_in_props..immediateType == const Imm_none) then
                          #p..alu_in_rs2val
                        else #imm in
        init_struct AluOutput { alu_out_reg := #alu_src1 + #alu_src2;
                                          alu_out_csr := _ 'd 0}
   )).

  Definition nextPc {var} : fn var _ mword := Fn (fun (p: var mword) => 
                                             quartz_eexpr:(return #p + _ 'd 4)). 
  Let is_word_aligned {var} : fn var _ Bool := Fn (fun (addr: var mword) => quartz_eexpr:(
    return (#addr & (_ 'd 3)) == _ 'd 0)).

  Definition EXN_InstructionAddressMisaligned : mword := Z_to_bv _ 0.
  Definition EXN_IllegalInstruction : mword := Z_to_bv _ 2.
  Definition EXN_LoadAddressMisaligned : mword := Z_to_bv _ 4.
  Definition EXN_StoreAddressMisaligned : mword := Z_to_bv _ 6.

  Record ctrlInput :=
  { ctrl_in_flds: DecodeFields;
    ctrl_in_props : InstrProps;
    ctrl_in_pc : mword;
    ctrl_in_rs1val : mword;
    ctrl_in_rs2val: mword;
  }.
  Definition CtrlInput := type.reify'' ctrlInput.

  Record ctrlOutput :=
  { ctrl_out_taken : Bool;
    ctrl_out_pc : mword;
    ctrl_out_isExn : Bool;
    ctrl_out_exnCode : mword;
    ctrl_out_mtval: mword
  }.
  Definition CtrlOutput := type.reify'' ctrlOutput.

  Definition execControl {var} 
    : fn var _ CtrlOutput := Fn (fun (p: var CtrlInput) => quartz_eexpr:(
      let flds := #p..ctrl_in_flds in 
      let props := #p..ctrl_in_props in
      let pc := #p..ctrl_in_pc in
      let rs1val := #p..ctrl_in_rs1val in
      let rs2val := #p..ctrl_in_rs2val in
      let imm := getImm ((#flds, #props)) in 
        let isJalr := ((#flds..D_opcode == const opcode_JALR) 
                     & (#flds..D_funct3 == const funct3_JALR)) in 
      if (#props..itype == const Inst_Ctrl) then
        if #isJalr then
          let nextPC := (#rs1val + #imm) & (~ (_ 'd 1)) in 
          let isAligned := is_word_aligned (#nextPC) in 
          init_struct CtrlOutput { ctrl_out_taken := true;
                                   ctrl_out_pc := #nextPC;
                                   ctrl_out_isExn := ~#isAligned;
                                   ctrl_out_exnCode := const EXN_InstructionAddressMisaligned;
                                   ctrl_out_mtval := #nextPC }
        else (* BEQ *)
          let taken := (#rs1val == #rs2val) in 
          let nextPC := #pc + #imm in 
          let isAligned := is_word_aligned (#nextPC) in 
          init_struct CtrlOutput { ctrl_out_taken := #taken;
                                   ctrl_out_pc := (if #taken then #nextPC else nextPc (#pc));
                                   ctrl_out_isExn := ~#isAligned;
                                   ctrl_out_exnCode := const EXN_InstructionAddressMisaligned;
                                   ctrl_out_mtval := #nextPC}
      else
          init_struct CtrlOutput { ctrl_out_taken := false;
                                   ctrl_out_pc := nextPc (#pc);
                                   ctrl_out_isExn := false;
                                   ctrl_out_exnCode := _ 'd 0;
                                   ctrl_out_mtval := _ 'd 0}
    )).

  Record memAddrOutput :=
  { memAddrOut_addr : mword;
    memAddrOut_isExn : Bool;
    memAddrOut_exnCode : mword;
    memAddrOut_mtval : mword 
  }.
  Definition MemAddrOutput := type.reify'' memAddrOutput.

  Definition memAddr {var} : fn var _ MemAddrOutput :=
    Fn (fun (p: var (Pair (Pair DecodeFields InstrProps) mword)) => quartz_eexpr:(
      let flds := #p.1.1 in
      let props := #p.1.2 in 
      let rs1val := #p.2 in 
      let imm := getImm ((#flds, #props)) in 
      if ((#props..itype == const Inst_Store) | (#props..itype == const Inst_Load)) then
         let addr  := #rs1val + #imm in 
         let isAligned := is_word_aligned (#addr) in
         let exnCode := if (#props..itype == const Inst_Store) then
                          const EXN_StoreAddressMisaligned
                        else const EXN_LoadAddressMisaligned in 
         init_struct MemAddrOutput { memAddrOut_addr := #addr;
                                     memAddrOut_isExn := ~#isAligned;
                                     memAddrOut_exnCode := #exnCode;
                                     memAddrOut_mtval := #addr }
      else 
         init_struct MemAddrOutput { memAddrOut_addr := _ 'd 0;
                                     memAddrOut_isExn := false;
                                     memAddrOut_exnCode := _ 'd 0;
                                     memAddrOut_mtval := _ 'd 0}
    )).
      
  (* Record decodeOut := { *)
  (*   D_inst : mword; *)
  (*   D_flds : InstrProps; *)
  (* }. *)
  (* Definition DecodeOut := type.reify'' decodeOut. *)

  (* Let decode {var} : fn var (Bits 32) DecodeOut := Fn (fun (inst: var mword) => quartz_eexpr:( *)
  (*   let flds := getInstrProps ( #inst ) in *)
  (*   let ret <- init_struct DecodeOut { *)
  (*     D_inst := #inst; *)
  (*     D_flds := #flds *)
  (*   } in *)
  (*   return #ret *)
  (* )). *)

  (* Class DecodeOutT (T : Type) := { *)
  (*   decodeFields : T -> DecodeOutType *)
  (* }. *)

  (* Class IsaParams {DecodeOut : Type} := { *)
  (*   decode : mword -> DecodeOut *)
  (* }. *)
End Decode. End Decode.


Module CPU.
  Notation mword := (Bits 32).

  Inductive mem_type :=
  | IMEM
  | DMEM
  | MMIO.

  Record Cpu {var} {t_mem_req t_mem_resp: type} (t_state: type) := {
    enqResp : mem_type -> fn var (Pair t_state t_mem_resp) t_state;
    deqReq : mem_type -> fn var t_state t_state;
    setInterrupt : fn var (Pair t_state (Pair Bool mword)) t_state; 
    tick : fn var t_state t_state;
    canEnqResp : mem_type -> fn var t_state Bool;
    canDeqReq : mem_type -> fn var t_state Bool;
    peek : mem_type -> fn var t_state t_mem_req
  }.

End CPU. Notation Cpu := CPU.Cpu (only parsing).

Module cpu. 
  Notation width := 32%N.
  Notation mword := (Bits width).
  Section cpuTypes.
    Record mem_req_t := { mem_req_is_store : Bool; 
                          mem_req_addr : mword;
                          mem_req_data : mword }.
    Definition Mem_req_t := type.reify'' mem_req_t.

    Record mem_resp_t := { mem_resp_addr : mword ; 
                           mem_resp_data : mword }.
    Definition Mem_resp_t := type.reify'' mem_resp_t.

    Record f2d_bookkeeping :=
      { f2d_pc : mword;
        f2d_ppc : mword;
        f2d_epoch : Bool;
        f2d_depoch: Bool;
        f2d_iepoch: Bool;
      }.
    Definition F2d_bookkeeping := type.reify'' f2d_bookkeeping.

    Record d2e_bookkeeping :=
      { d2e_rval1 : mword;
        d2e_rval2 : mword;
        d2e_csr: mword;
        d2e_pc : mword;
        d2e_ppc : mword;
        d2e_epoch : Bool;
        d2e_iepoch : Bool;
        d2e_inst : mword
      }.
    Definition D2e_bookkeeping := type.reify'' d2e_bookkeeping.

    Record e2w_bookkeeping :=
      { e2w_alu : mword;
        e2w_csr : mword;
        e2w_inst : mword;
        e2w_exnInfo : (Bool * mword * mword * mword);
        e2w_isMMIO : Bool;
        e2w_nextPc : mword (* for interrupts *)
      }.
    Definition E2w_bookkeeping := type.reify'' e2w_bookkeeping.

  End cpuTypes.

  Coercion mem_req_rep (v : mem_req_t) : type.reify'' mem_req_t :=
    ltac2:(let t := struct.rep &v in exact $t).
  Coercion mem_resp_rep (v : mem_resp_t) : type.reify'' mem_resp_t :=
    ltac2:(let t := struct.rep &v in exact $t).

  Section cpu.
    Context {mul_LogNSteps: N}.
    Context {bht_idxSz: N}.
    Context {btb_tagSz: N}.
    Context {btb_idxSz: N}.
    Parameter (isMMIOAddr : forall {var}, fn var mword Bool).

    Definition log_nregs : N := 5.
    Definition nregs : nat := N.to_nat (2^log_nregs).
    Record state : Type :=
    { Pc : mword
    ; Epoch : Bool
    ; Depoch: Bool
    ; Iepoch: Bool
    ; Rf: rfScored.state' mword nregs
    ; Csrs : csrFile.State
    ; ToIMem: fifo1.State Mem_req_t (* TODO: reify fifo1.state *)
    ; ToDMem: fifo1.State Mem_req_t
    ; ToMMIO: fifo1.State Mem_req_t
    ; FromIMem: fifo1.State Mem_resp_t
    ; FromDMem: fifo1.State Mem_resp_t
    ; FromMMIO: fifo1.State Mem_resp_t
    ; F2d : fifo1.State F2d_bookkeeping
    ; D2e : fifo1.State D2e_bookkeeping
    ; E2w : fifo1.State E2w_bookkeeping
    ; Mul : @multiplier.State mul_LogNSteps
    ; Mip : Bool
    (* ; Mie : Bool *)
    ; InterruptSrc : mword
    ; Bht : @bht.State bht_idxSz
    ; Btb : @btb.State width btb_tagSz btb_idxSz
    }. 


    Definition State := type.reify'' state.
    Coercion rep (v : state) : type.reify'' state :=
     ltac2:(let t := struct.rep &v in exact $t).

    Import (notations) eexpr expr. Local Open Scope string_scope.
    Import QStdlib.


    Notation fifo1_full := (Fifo.full _ _ (fifo1.impl _)).
    Notation fifo1_empty := (Fifo.empty _ _ (fifo1.impl _)).
    Notation fifo1_enq := (Fifo.enq _ _ (fifo1.impl _)).
    Notation fifo1_first := (Fifo.first _ _ (fifo1.impl _)).
    Notation fifo1_deq := (Fifo.deq _ _ (fifo1.impl _)).
    Notation btb_update := (Btb.update _ (btb.impl)).  
    Notation btb_predPc := (Btb.predPc _ (btb.impl)).  
    Notation rf_isLocked := (RfScored.isLocked (rfScored.impl _ )).
    Notation rf_read := (RfScored.read (rfScored.impl _)).
    Notation rf_acquire := (RfScored.acquireLock (rfScored.impl _)).
    Notation rf_release := (RfScored.releaseLock (rfScored.impl _)).
    Notation csr_read := (CsrFile.readCsr (csrFile.impl)).
    Notation csr_write := (CsrFile.writeCsr (csrFile.impl)).
    Notation bht_update := (Bht.update _ (bht.impl)).  
    Notation bht_ppcDp := (Bht.ppcDp _ (bht.impl)).
    Notation mul_full := (Multiplier.full _ (multiplier.impl mul_LogNSteps)).
    Notation mul_enq := (Multiplier.enq _ (multiplier.impl mul_LogNSteps)).
    Notation mul_tick := (Multiplier.tick _ (multiplier.impl mul_LogNSteps)).
    Notation mul_deq := (Multiplier.deq _ (multiplier.impl mul_LogNSteps)).
    Notation mul_peek := (Multiplier.peek _ (multiplier.impl mul_LogNSteps)).
    Notation mul_ready := (Multiplier.respReady _ (multiplier.impl mul_LogNSteps)).

    Let struct_test {var} := Fn (fun (st : var State) => quartz_eexpr:(
        let pc := #st..Pc in 
        let req <- init_struct Mem_req_t {
          mem_req_is_store := true;
          mem_req_addr := #pc
        } in
        return #req )).


    Lemma struct_test_ok (st : state) :
      fn.interp struct_test st = {| mem_req_is_store := true; 
                                    mem_req_addr := st.(Pc);
                                    mem_req_data := (bv_0 _) |}.
    Proof.
      reflexivity.
    Qed.
                                                                   
    Definition fetch_stage {var} := Fn (fun (st : var State) => quartz_eexpr:(
      if (fifo1_full (#st..ToIMem)) | (fifo1_full (#st..F2d)) then
        return #st 
      else
        let ppc := btb_predPc ((#st..Btb, #st..Pc)) in 
        let imem_req <- init_struct Mem_req_t {
          mem_req_is_store := false;
          mem_req_addr := #st..Pc;
          mem_req_data := _ 'd 0
        } in
        let f2d_req <- init_struct F2d_bookkeeping {
          f2d_pc := #st..Pc;
          f2d_ppc := #ppc;
          f2d_epoch := #st..Epoch;
          f2d_depoch := #st..Depoch; 
          f2d_iepoch := #st..Iepoch
        } in                          
        let st <- #st..Pc = #ppc in 
        let st <- #st..ToIMem = fifo1_enq((#st..ToIMem, #imem_req)) in
        let st <- #st..F2d = fifo1_enq((#st..F2d, #f2d_req)) in
        return #st 
    )).

    (* TODO: enum type *)
    Import Decode.

    Definition decode_stage {var} := Fn (fun (st : var State) => quartz_eexpr:(
      if (fifo1_empty (#st..FromIMem)) | (fifo1_empty (#st..F2d)) then
        return #st
      else
        let imem_resp := fifo1_first (#st..FromIMem) in
        let f2d_book := fifo1_first (#st..F2d) in
        let inst := #imem_resp..mem_resp_data in
        let flds := getFields (#inst) in
        let props := getInstrProps (#inst) in
        if (#f2d_book..f2d_epoch == #st..Epoch) &
           (#f2d_book..f2d_depoch == #st..Depoch) &
           (#f2d_book..f2d_iepoch == #st..Iepoch)
        then
          let rs1_idx := #flds..D_rs1Idx in
          let rs2_idx := #flds..D_rs2Idx in
          let rd_idx := #flds..D_rdIdx in
          let locked1 := rf_isLocked ((#st..Rf, #rs1_idx)) in
          let locked2 := rf_isLocked ((#st..Rf, #rs2_idx)) in
          let locked_rd := rf_isLocked ((#st..Rf, #rd_idx)) in
          let d2e_full := fifo1_full (#st..D2e) in
          let e2w_full := fifo1_full (#st..E2w) in
          let is_sys := (#props..itype == const Inst_System) in
          if #d2e_full | (#locked1 | #locked2 | #locked_rd) | (#is_sys & #e2w_full) then
            return #st (* stall *) 
          else
            let rs1 := rf_read ((#st..Rf, #rs1_idx)) in
            let rs2 := rf_read ((#st..Rf, #rs2_idx)) in
            let csr_val := csr_read ((#st..Csrs, #flds..D_csrIdx)) in
            let imm := getImm ((#flds, #props)) in 
            let ppcDP := if (#props..itype == const Inst_Ctrl) then
                           bht_ppcDp ((#st..Bht, (#f2d_book..f2d_pc, #f2d_book..f2d_pc + #imm)))
                         else #f2d_book..f2d_ppc in
            let dbook <- init_struct D2e_bookkeeping {
              d2e_rval1 := #rs1;
              d2e_rval2 := #rs2;
              d2e_csr := #csr_val;
              d2e_pc := #f2d_book..f2d_pc;
              d2e_ppc := #ppcDP;
              d2e_epoch := #f2d_book..f2d_epoch;
              d2e_iepoch := #f2d_book..f2d_iepoch;
              d2e_inst := #inst
            } in
            let st <- #st..F2d = (fifo1_deq (#st..F2d)) in
            let st <- #st..FromIMem = (fifo1_deq (#st..FromIMem)) in
            let st <- #st..D2e = fifo1_enq((#st..D2e, #dbook)) in
            let st <- if (#ppcDP == #f2d_book..f2d_ppc) then
                       return #st
                     else 
                       let st <- #st..Pc = #ppcDP in 
                       let st <- #st..Depoch = ~#st..Depoch in 
                       return #st in 
            if #props..rdValid then
              let st <- #st..Rf = rf_acquire ((#st..Rf, #rd_idx)) in 
              return #st
            else
              return #st
        else 
          let st <- #st..F2d = (fifo1_deq (#st..F2d)) in
          let st <- #st..FromIMem = (fifo1_deq (#st..FromIMem)) in
          return #st
     )).

    
    Let e2w_exn {var} : fn var _ E2w_bookkeeping := 
          Fn (fun (p: var (Pair mword (Pair mword (Pair mword mword)))) => quartz_eexpr:(
      let inst := #p.1 in
      let exnCode := #p.2.1 in 
      let exnMtval := #p.2.2.1 in
      let mepc := #p.2.2.2 in
      init_struct E2w_bookkeeping { 
                            e2w_alu := _ 'd 0;
                            e2w_csr := _ 'd 0;
                            e2w_exnInfo := (true, #exnCode, #exnMtval, #mepc);
                            e2w_inst := #inst;
                            e2w_isMMIO := false;
                            e2w_nextPc := _ 'd 0 })).

    Definition execute_stage {var} := Fn (fun (st : var State) => quartz_eexpr:(
      let dbook := fifo1_first (#st..D2e) in
      let inst := #dbook..d2e_inst in
      let _pc := #dbook..d2e_pc in 
      let flds := getFields (#inst) in
      let props := getInstrProps (#inst) in
      if fifo1_empty (#st..D2e) then
        return #st (* stall; nothing to do *)
      else if ((#dbook..d2e_epoch == #st..Epoch) &  
               (#dbook..d2e_iepoch == #st..Iepoch)) then
        let rval1 := #dbook..d2e_rval1 in
        let rval2 := #dbook..d2e_rval2 in
        let csr_val := #dbook..d2e_csr in
        let alu_in <- init_struct AluInput { alu_in_flds := #flds;
                                            alu_in_props := #props;
                                            alu_in_rs1val := #rval1;
                                            alu_in_rs2val := #rval2;
                                            alu_in_csrval := #csr_val;
                                            alu_in_pc := #_pc
                                          } in 
        let alu_csr_out := execALU (#alu_in) in 
        let ctrl_in <- init_struct CtrlInput { ctrl_in_flds := #flds;
                                              ctrl_in_props := #props;
                                              ctrl_in_pc := #_pc;
                                              ctrl_in_rs1val := #rval1;
                                              ctrl_in_rs2val := #rval2
                                            } in 
        let ctrl_out := execControl (#ctrl_in) in 
        let nextPC := #ctrl_out..ctrl_out_pc in 
        if fifo1_full (#st..E2w) | 
           ((#props..itype == const Inst_Mul) & mul_full (#st..Mul)) then
          return #st (* stall *)
        else
          let St_ExBook_IsExn <-
            if (#props..itype == const Inst_Illegal) then 
              if ( (#props..itype == const Inst_Store) 
                 | (#props..itype == const Inst_Load)) then (* isMem *)
                let memOut := memAddr (((#flds, #props), #rval1)) in 
                let addr := #memOut..memAddrOut_addr in 
                let req <- init_struct Mem_req_t { 
                              mem_req_is_store := ~(#props..itype == const Inst_Load); 
                              mem_req_addr := #addr ;
                              mem_req_data := if (#props..itype == const Inst_Load) then
                                                _ 'd 0
                                              else #rval2
                          } in 
                let e2w <- init_struct E2w_bookkeeping {
                            e2w_alu := _ 'd 0;
                            e2w_csr := _ 'd 0;
                            e2w_exnInfo := (#memOut..memAddrOut_isExn, 
                                            #memOut..memAddrOut_exnCode,
                                            #memOut..memAddrOut_mtval, 
                                            #_pc);
                            e2w_inst := #inst;
                            e2w_isMMIO := ~#memOut..memAddrOut_isExn & isMMIOAddr(#addr);
                            e2w_nextPc := #nextPC } in
                if #memOut..memAddrOut_isExn then
                  return (#st, (#e2w, true))
                else if isMMIOAddr(#addr) then
                  let st <- #st..ToMMIO = fifo1_enq((#st..ToMMIO, #req)) in 
                  return (#st, (#e2w, false))
                else 
                  let st <- #st..ToDMem = fifo1_enq((#st..ToDMem , #req)) in 
                  return (#st, (#e2w, false))
              else if (#props..itype == const Inst_Mul) then 
                let req <- init_struct multiplier.Req { multiplier.input_a := #rval1;
                                                       multiplier.input_b := #rval2
                                                     } in
                let st <- #st..Mul = mul_enq ((#st..Mul, #req)) in
                let e2w <- init_struct E2w_bookkeeping {
                            e2w_alu := #alu_csr_out..alu_out_reg ;
                            e2w_csr := #alu_csr_out..alu_out_csr;
                            e2w_exnInfo := (false, _ 'd 0, _ 'd 0, _ 'd 0);
                            e2w_inst := #inst;
                            e2w_isMMIO := false;
                            e2w_nextPc := #nextPC } in
                return (#st, (#e2w, false))
              else (* ALU/control/system *)
                let st <- if (#props..itype == const Inst_Ctrl) then
                           #st..Bht = bht_update((#st..Bht, (#_pc, #ctrl_out..ctrl_out_taken)))
                         else return #st in
                let isJalr := ((#flds..D_opcode == const opcode_JALR) 
                     & (#flds..D_funct3 == const funct3_JALR)) in 
                let isCtrlExn := #ctrl_out..ctrl_out_isExn in 
                let ctrlExnCode := #ctrl_out..ctrl_out_exnCode  in 
                let ctrlExnMtval := #ctrl_out..ctrl_out_mtval  in 
                let e2w <- init_struct E2w_bookkeeping {
                            e2w_alu := if #isJalr then
                                         nextPc (#_pc)
                                       else #alu_csr_out..alu_out_reg ;
                            e2w_csr := #alu_csr_out..alu_out_csr;
                            e2w_exnInfo := (#isCtrlExn, #ctrlExnCode, #ctrlExnMtval, #_pc);
                            e2w_inst := #inst;
                            e2w_isMMIO := false;
                            e2w_nextPc := #nextPC } in
                return (#st, (#e2w, #isCtrlExn))
            else (* illegal *)
              return (#st, (e2w_exn ((#inst, (const EXN_IllegalInstruction, (#inst, #_pc)))), true))
          in
          let st := #St_ExBook_IsExn.1 in 
          let ex_book := #St_ExBook_IsExn.2.1 in
          let isExn := #St_ExBook_IsExn.2.2 in
          let st <- #st..D2e = fifo1_deq (#st..D2e) in 
          let st <- #st..E2w = fifo1_enq ((#st..E2w , #ex_book)) in 
          let st <- if (#nextPC == #dbook..d2e_ppc) then
                     return #st
                   else
                     let st <- #st..Epoch = ~#st..Epoch in
                     let st <- #st..Pc = #nextPC in 
                     let st <- #st..Btb = btb_update ((#st..Btb, (#_pc, #nextPC))) in 
                     return #st in 
          if #isExn then
            let trapHandlerAddr := csr_read ((#st..Csrs, const csrFile.CSR_mtvec)) in
            let st <- #st..Pc = #trapHandlerAddr in
            let st <- #st..Epoch = ~#st..Epoch in 
            let st <- #st..Btb = btb_update ((#st..Btb, (#_pc, #trapHandlerAddr))) in 
            return #st
          else return #st
      else (* mispredicted *)
        let st <- #st..D2e = (fifo1_deq (#st..D2e)) in 
        if #props..rdValid then (* release any write lock *)
          let st <- #st..Rf = rf_release((#st..Rf, #flds..D_rdIdx)) in
          return #st
        else
          return #st
    )).
    Let handle_interrupt {var} : fn var (Pair State mword) State :=
          Fn (fun (p: var (Pair State mword)) => quartz_eexpr:(
      let st := #p.1 in 
      let nextPc := #p.2 in
      let mie := csr_read ((#st..Csrs, const csrFile.CSR_mie)) in 
      if #st..Mip & ~(#mie == _ 'd 0) then
        let trapHandlerAddr := csr_read ((#st..Csrs, const csrFile.CSR_mtvec)) in 
        let st <- #st..Iepoch = ~(#st..Iepoch) in 
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mepc, #nextPc))) in
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mie, _ 'd 0))) in
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mtval, #st..InterruptSrc))) in
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mcause, _ 'd 0 ))) in
        let st <- #st..Pc = #trapHandlerAddr in 
        return #st
      else return #st
    )).

    Definition writeback_stage {var} := Fn (fun (st : var State) => quartz_eexpr:(
      let e2w_book := fifo1_first (#st..E2w) in
      let inst := #e2w_book..e2w_inst in 
      let flds := getFields (#inst) in
      let props := getInstrProps (#inst) in
      let e2w_isExn := #e2w_book..e2w_exnInfo.1.1.1 in 
      let exnCode := #e2w_book..e2w_exnInfo.1.1.2 in 
      let exnMtval := #e2w_book..e2w_exnInfo.1.2 in 
      let exnMepc := #e2w_book..e2w_exnInfo.2 in 
      let isMem := (#props..itype == const Inst_Store) | (#props..itype == const Inst_Load)  in
      let isMul := (#props..itype == const Inst_Mul) in 
      if fifo1_empty (#st..E2w) | 
         (~#e2w_isExn & 
           ((#e2w_book..e2w_isMMIO & fifo1_empty (#st..FromMMIO)) |
            (#isMem & ~#e2w_book..e2w_isMMIO & fifo1_empty (#st..FromDMem)) | 
            (#isMul & ~mul_ready(#st..Mul)))) then
        return #st
      else if #e2w_isExn then
        let st <- #st..E2w = fifo1_deq(#st..E2w) in 
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mie, _ 'd 0))) in
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mtval, #exnMtval))) in
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mcause, #exnCode))) in
        let st <- #st..Csrs = csr_write((#st..Csrs, (const csrFile.CSR_mepc, #exnMepc))) in
        if #props..rdValid then
          let st <- #st..Rf = rf_release ((#st..Rf, #flds..D_rdIdx)) in
          return #st
        else
          return #st
      else
        let St_reg_csr <-
          if #e2w_book..e2w_isMMIO then
            let resp := fifo1_first (#st..FromMMIO) in
            let st <- #st..FromMMIO = fifo1_deq (#st..FromMMIO) in 
            return (#st, (#resp..mem_resp_data, 32 'd 0))  
          else if #isMem then
            let resp := fifo1_first (#st..FromDMem) in
            let st <- #st..FromDMem = fifo1_deq (#st..FromDMem) in 
            return (#st, (#resp..mem_resp_data, 32 'd 0))  
          else if #isMul then
            let resp := mul_peek (#st..Mul) in 
            let st <- #st..Mul = mul_deq (#st..Mul) in 
            return (#st, ($(expr.Unop unop.UnsignedResize (expr.Var resp)), _ 'd 0))  
          else
            return (#st, (#e2w_book..e2w_alu, #e2w_book..e2w_csr)) in
        let st := #St_reg_csr.1 in
        let reg_data := #St_reg_csr.2.1 in
        let csr_data := #St_reg_csr.2.2 in
        let st <- #st..E2w = fifo1_deq(#st..E2w) in 
        let st <- if #props..rdValid then
                   #st..Rf = rf_release ((#st..Rf, #flds..D_rdIdx)) 
                 else return #st in  
        let st <- if (#props..itype == const Inst_System) then
                   #st..Csrs = csr_write((#st..Csrs, (#flds..D_csrIdx, #csr_data))) 
                 else return #st in
        return handle_interrupt ((#st, #e2w_book..e2w_nextPc))
    )).
    Definition tick_mul {var} := Fn (fun (st : var State) => quartz_eexpr:(
      let st <- #st..Mul = mul_tick(#st..Mul) in 
      return #st)).

    Definition tick {var} := Fn (fun (st : var State) => quartz_eexpr:(
      let st := writeback_stage (#st) in
      let st := execute_stage (#st) in
      let st := decode_stage (#st) in
      let st := fetch_stage (#st) in
      let st := tick_mul (#st) in 
      return #st)).

    Notation foo := FromIMem.

    (* TODO *)
    (* Inductive MemType := *)
    (* | Imem *)
    (* | Dmem *)
    (* | Mmio. *)
    
    (* Definition fromMem (mem: MemType) := *)
    (*   match mem with *)
    (*   | Imem => FromIMem *)
    (*   | Dmem => FromDMem *)
    (*   | Mmio => FromMMIO *)
    (*   end.  *)
    
    (* Definition can_enq_resp (mem: MemType) {var} :=  *)
    (*   let mem := fromMem mem in  *)
    (*   Fn (fun (st : var State) => quartz_eexpr:( *)
    (*   return ! fifo1_full (#st..foo))).                                                                               *)

    Definition can_enq_resp_imem {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return ! fifo1_full (#st..FromIMem))).
    Definition can_enq_resp_dmem {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return ! fifo1_full (#st..FromDMem))).
    Definition can_enq_resp_mmio {var} :=
      Fn (fun (st : var State) => quartz_eexpr:( 
      let e2w_empty := fifo1_empty (#st..E2w) in
      let reqEmpty := fifo1_empty (#st..ToMMIO) in
      let e2w_book := fifo1_first (#st..E2w) in
      let full := fifo1_full (#st..FromMMIO) in
      return (! #full) & (! #e2w_empty & #e2w_book..e2w_isMMIO) & #reqEmpty
    )).

    Definition can_deq_req_imem {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return ! fifo1_empty (#st..ToIMem))).
    Definition can_deq_req_dmem {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return ! fifo1_empty (#st..ToDMem))).
    Definition can_deq_req_mmio {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return ! fifo1_empty (#st..ToMMIO ))).

    Definition peek_imem {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return fifo1_first (#st..ToIMem))).
    Definition peek_dmem {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return fifo1_first (#st..ToDMem))).
    Definition peek_mmio {var} :=
      Fn (fun (st : var State) => quartz_eexpr:(
      return fifo1_first (#st..ToMMIO ))).

    Definition set_pc {var} := Fn (fun (arg: var (Pair State mword) ) => quartz_eexpr:(
      let st := #arg.1 in 
      let pc := #arg.2 in 
      let st <- #st..Pc = #pc in
      return #st )).


    Definition set_interrupt {var} := Fn (fun (arg: var (Pair State (Pair Bool mword)) ) => quartz_eexpr:(
      let st := #arg.1 in 
      let mip := #arg.2.1 in 
      let interruptSrc := #arg.2.2 in 
      let st <- #st..Mip = #mip in
      let st <- #st..InterruptSrc = #interruptSrc in
      return #st)).

     Definition enq_resp_imem {var} := Fn (fun (arg: var (Pair State Mem_resp_t) ) => quartz_eexpr:(
       let st := #arg.1 in let resp := #arg.2 in
       let st <- #st..FromIMem = fifo1_enq ((#st..FromIMem,#resp)) in
       return #st
     )).
     Definition enq_resp_dmem {var} := Fn (fun (arg: var (Pair State Mem_resp_t) ) => quartz_eexpr:(
       let st := #arg.1 in let resp := #arg.2 in
       let st <- #st..FromDMem = fifo1_enq ((#st..FromDMem,#resp)) in
       return #st
     )).
     Definition enq_resp_mmio {var} := Fn (fun (arg: var (Pair State Mem_resp_t) ) => quartz_eexpr:(
       let st := #arg.1 in let resp := #arg.2 in
       let st <- #st..FromMMIO = fifo1_enq ((#st..FromMMIO ,#resp)) in
       return #st
     )).
     Definition deq_req_imem {var} := Fn (fun (st: var State) => quartz_eexpr:(
       let st <- #st..ToIMem = fifo1_deq ((#st..ToIMem )) in
       return #st
     )).
     Definition deq_req_dmem {var} := Fn (fun (st: var State) => quartz_eexpr:(
       let st <- #st..ToDMem = fifo1_deq ((#st..ToDMem )) in
       return #st
     )).

     Definition deq_req_mmio {var} := Fn (fun (st: var State) => quartz_eexpr:(
       let st <- #st..ToMMIO = fifo1_deq ((#st..ToMMIO)) in
       return #st
     )).

    Definition impl {var} : @Cpu var Mem_req_t Mem_resp_t State := {|
      CPU.enqResp mem := match mem with
                         | CPU.IMEM => enq_resp_imem
                         | CPU.DMEM => enq_resp_dmem
                         | CPU.MMIO => enq_resp_mmio
                         end;
      CPU.deqReq mem := match mem with
                         | CPU.IMEM => deq_req_imem
                         | CPU.DMEM => deq_req_dmem
                         | CPU.MMIO => deq_req_mmio
                         end;
      CPU.setInterrupt := set_interrupt;
      CPU.tick := tick;
      CPU.canEnqResp mem := match mem with
                            | CPU.IMEM => can_enq_resp_imem
                            | CPU.DMEM => can_enq_resp_dmem
                            | CPU.MMIO => can_enq_resp_mmio
                            end;
      CPU.canDeqReq mem := match mem with
                           | CPU.IMEM => can_deq_req_imem
                           | CPU.DMEM => can_deq_req_dmem
                           | CPU.MMIO => can_deq_req_mmio
                           end;
      CPU.peek mem := match mem with
                      | CPU.IMEM => peek_imem
                      | CPU.DMEM => peek_dmem
                      | CPU.MMIO => peek_mmio
                      end;
     |}.

  End cpu.
End cpu.

End InterfaceExample.
