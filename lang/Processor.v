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
    let shift_amt : Bits n := _ 'd s in
    let shifted_b := #b >> #shift_amt in    
    return $(expr.Unop unop.UnsignedResize (expr.Var shifted_b)))).

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

Module rfScored. 
  (* TODO: non-record type *)
  Notation state' t_data nregs := (Vector.t (Bool * t_data) nregs).
  Section rfScored.
  Context {var: type -> Type}.
  Context {log_nregs: Z}.
  Context (t_data : type).

  Notation t_idx := (Bits log_nregs).
  Definition nregs : nat := Z.to_nat (2^log_nregs).
  Notation state := (state' t_data nregs).
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

Module CsrFile.
  Record CsrFile {var} {idxSz} {wordSz} (t_state: type) := {
    readCsr : fn var (Pair t_state (Bits idxSz)) (Bits wordSz);
    writeCsr : fn var (Pair t_state (Pair (Bits idxSz) (Bits wordSz))) t_state
  }.

End CsrFile. Notation CsrFile := CsrFile.CsrFile (only parsing).

Module csrFile. Section csrFile.
  Notation CsrIdx := (Bits 12) (only parsing).
  Notation mword := (Bits 32).
  Definition CSR_mtvec : CsrIdx := Zmod.of_Z _ 773.
  Definition CSR_mepc : CsrIdx := Zmod.of_Z _ 833.
  Definition CSR_mcause : CsrIdx := Zmod.of_Z _ 834.
  Definition CSR_mtval : CsrIdx := Zmod.of_Z _ 835.
  Definition CSR_mie : CsrIdx := Zmod.of_Z _ 0x304. 

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

Module Decode.
  Notation CsrIdx := (Bits 12) (only parsing).
  Notation mword := (Bits 32) (only parsing).

  Record DecodeOutType := {
    D_rs1Idx : Bits 5;
    D_rs2Idx : Bits 5;
    D_rdIdx : Bits 5;
    D_csrIdx : CsrIdx;
    D_imm : mword;
    D_rdValid : Bool;
    D_isSys : Bool;
    D_isCtrl : Bool
  }.

  (* Class DecodeOutT (T : Type) := { *)
  (*   decodeFields : T -> DecodeOutType *)
  (* }. *)

  (* Class IsaParams {DecodeOut : Type} := { *)
  (*   decode : mword -> DecodeOut *)
  (* }. *)
End Decode.


Module CPU.
  Notation mword := (Bits 32).

  Inductive mem_type :=
  | IMEM
  | DMEM
  | MMIO.

  Record Cpu {var} (t_mem_req t_mem_resp: type) (t_state: type) := {
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
  Notation width := 32.
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

  Section cpu.
    Context {mul_LogNSteps: Z}.
    Context {bht_idxSz: Z}.
    Context {btb_tagSz: Z}.
    Context {btb_idxSz: Z}.

    Definition log_nregs : Z := 5.
    Definition nregs : nat := Z.to_nat (2^log_nregs).
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
    ; Mul : multiplier.State width mul_LogNSteps
    ; Mip : Bool
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
    Notation btb_update := (Btb.update _ (btb.impl)).  
    Notation btb_predPc := (Btb.predPc _ (btb.impl)).  

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
                                    mem_req_data := Zmod.zero |}.
    Proof.
      reflexivity.
    Qed.
                                                                   
    Let fetch {var} := Fn (fun (st : var State) => quartz_eexpr:(
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

    Let decode_stage {var} := Fn (fun (st : var State) => quartz_eexpr:(
      if (fifo1_empty (#st..FromIMem)) | (fifo1_empty (#st..F2d)) then          
        return #st (* Nothing to do *)
      else 
        let imem_resp := fifo1_first (#st..FromIMem) in
        let f2d_book := fifo1_first (#st..F2d) in 
        if (#f2d_book..f2d_epoch == #st..Epoch) &
           (#f2d_book..f2d_depoch == #st..Depoch) &
           (#f2d_book..f2d_iepoch == #st..Iepoch)
        then 
          return #st
        else
          return #st
    )).

      (* let fromIMem_empty := fifo1_empty (#st..FromIMem) in *)
      (* let f2d_empty := fifo1_empty (#st..F2d) in *)
      (* let d2e_full := fifo1_full (#st..D2e) in *)
      (* let e2w_full := fifo1_full (#st..E2w) in *)
      (* let f2d_book := fifo1_first (#st..F2d) in *)
      (* let epoch := #st..Epoch in  *)
      (* let depoch := #st..Depoch in  *)
      (* let iepoch := #st..Iepoch in  *)
      (* let inst := #imem_resp..mem_resp_data in *)
      (* let D := decode params #inst in *)
      (* let D_flds := decodeFields D in *)
      (* if #fromIMem_empty | #f2d_empty then *)
      (*   return false *)
      (* else if bool_decide (#f2d_book..f2d_epoch = #epoch) && *)
      (*         bool_decide (#f2d_book..f2d_depoch = #depoch) && *)
      (*         bool_decide (#f2d_book..f2d_iepoch = #iepoch) then *)
      (*   let rs1_idx := D_rs1Idx D_flds in *)
      (*   let rs2_idx := D_rs2Idx D_flds in *)
      (*   let rd_idx := D_rdIdx D_flds in *)
      (*   let csr_idx := D_csrIdx D_flds in *)
      (*   locked1 ← rf (RfScored.IsLocked rs1_idx); *)
      (*   locked2 ← rf (RfScored.IsLocked rs2_idx); *)
      (*   locked_rd ← rf (RfScored.IsLocked rd_idx); *)
      (*   if d2e_full || (locked1 || locked2 || locked_rd) || (D_isSys D_flds && e2w_full) then *)
      (*     return false *)
      (*   else *)
      (*     rs1 ← rf (RfScored.Read rs1_idx); *)
      (*     rs2 ← rf (RfScored.Read rs2_idx); *)
      (*     csr_val ← getCSR csr_idx; *)
      (*     let imm := D_imm D_flds in  *)
      (*     bht_ppcDP ← bht (BhtAPI.PpcDP (#f2d_book..f2d_pc) (bv_add (#f2d_book..f2d_pc) (bv_zero_extend _ imm))); *)
      (*     let ppcDP := if D_isCtrl D_flds then bht_ppcDP else #f2d_book..f2d_ppc in *)
      (*     let dbook := {| d2e_rval1 := rs1; *)
      (*                     d2e_rval2 := rs2; *)
      (*                     d2e_csr := csr_val; *)
      (*                     d2e_pc := #f2d_book..f2d_pc; *)
      (*                     d2e_ppc := ppcDP; *)
      (*                     d2e_epoch := #f2d_book..f2d_epoch; *)
      (*                     d2e_iepoch := #f2d_book..f2d_iepoch; *)
      (*                     d2e_inst := #inst; *)
      (*                  |} in *)
      (*     f2d_ fifo1_deq;; *)
      (*     fromIMem_ fifo1_deq;; *)
      (*     d2e_ (fifo1_enq (#st..D2e, dbook));; *)
      (*     let/prog _ := (if (bool_decide (ppcDP = #f2d_book..f2d_ppc)) then *)
      (*                      pass *)
      (*                    else *)
      (*                      setPc ppcDP;; *)
      (*                      setDepoch (negb #depoch);; *)
      (*                      pass) in *)
      (*     if D_rdValid D_flds then *)
      (*       rf_ (RfScored.AcquireLock rd_idx);; *)
      (*       return true *)
      (*     else *)
      (*       return true *)
      (* else *)
      (*   f2d_ fifo1_deq;; *)
      (*   fromIMem_ fifo1_deq;; *)
      (*   return false *)


  End cpu.
End cpu.

End InterfaceExample.
