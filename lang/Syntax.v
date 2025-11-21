From stdpp Require Import base bitvector vector.
From Stdlib Require Import 
  List 
  NArith 
  Program.Equality 
  String.
Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope Z_scope.

Module type.
  Inductive type :=
  | Bool
  | Bits (sz: N)
  | Pair (t1 t2: type)
  | Array (t: type) (sz: nat).
  
  Fixpoint type_denote tau : Type :=
    match tau with
    | Bool => bool
    | Bits sz => bv sz
    | Pair t1 t2 => (type_denote t1) * (type_denote t2)
    | Array ty n => vec (type_denote ty) n 
    end.
End type.
Import type.
Coercion type_denote: type >-> Sortclass.
Notation Unit := (Bits 0).
Notation unit_value := (bv_0 0).

(* TODO: structs & array ops *)
Module unop.
  Inductive unop : type -> type -> Type :=
  | Not {n} : unop (Bits n) (Bits n)
  | Fst {a b: type} : unop (Pair a b) a
  | Snd {a b: type} : unop (Pair a b) b.

  Definition interp {a b} (op: unop a b) : type_denote a -> type_denote b :=
    match op with
    | Not _ => bv_not 
    | Fst _ _ => fst 
    | Snd _ _ => snd
    end. 

End unop.

Module binop.

  Inductive bits_comparison :=
  | cLt | cGt | cLe | cGe.

  Inductive binop : type -> type -> type -> Type := 
  | Plus {n} : binop (Bits n) (Bits n) (Bits n)
  | And {n} : binop (Bits n) (Bits n) (Bits n)
  | Or {n} : binop (Bits n) (Bits n) (Bits n)
  | Lsl {n} : binop (Bits n) (Bits n) (Bits n)
  | Lsr {n} : binop (Bits n) (Bits n) (Bits n)
  | Asr {n} : binop (Bits n) (Bits n) (Bits n)
  | EqBits {n} : binop (Bits n) (Bits n) Bool
  | Compare (signed: bool) (c: bits_comparison) {n} : binop (Bits n) (Bits n) Bool
  | MkPair {a b: type} : binop a b (Pair a b).

  Definition interp {a b c} (op: binop a b c) 
    : type_denote a -> type_denote b -> type_denote c :=
    match op with
    | Plus _ => bv_add
    | And _ => bv_and
    | Or _ => bv_or
    | Lsl _ => bv_shiftl
    | Lsr _ => bv_shiftr
    | Asr _ => bv_ashiftr
    | EqBits _ => fun b1 b2 => bool_decide (b1 = b2)
    | Compare signed c _ => fun b1 b2 => 
        match signed, c with
        | true, cLt =>  bool_decide (bv_signed b1 < bv_signed b2)
        | false, cLt => bool_decide (bv_unsigned b1 < bv_unsigned b2)
        | true, cGt =>  bool_decide (bv_signed b1 > bv_signed b2)
        | false, cGt => bool_decide (bv_unsigned b1 > bv_unsigned b2)
        | true, cLe =>  bool_decide (bv_signed b1 <= bv_signed b2)
        | false, cLe => bool_decide (bv_unsigned b1 <= bv_unsigned b2)
        | true, cGe =>  bool_decide (bv_signed b1 >= bv_signed b2)
        | false, cGe => bool_decide (bv_unsigned b1 >= bv_unsigned b2)
        end
    | MkPair _ _ => Datatypes.pair
    end. 
End binop.

Module typeWithHole.
  Inductive typeWithHole :=
  | HOLE
  | PairL (t1 : typeWithHole) (t2: type)
  | PairR (t1 : type) (t2: typeWithHole)
  | Array (sz: nat) (idx: fin sz) (t: typeWithHole).

  Fixpoint plug (C : typeWithHole) (t : type) : type :=
    match C with
    | HOLE => t
    | PairL t1 t2 => type.Pair (plug t1 t) t2
    | PairR t1 t2 => type.Pair t1 (plug t2 t)
    | Array sz _ t' => type.Array (plug t' t) sz
    end.

  Fixpoint fieldUpdate {C: typeWithHole.typeWithHole} {t: type} 
    (r : type_denote (typeWithHole.plug C t)) (v : type_denote t) 
    : (type_denote (typeWithHole.plug C t)) :=
    match C return type_denote (typeWithHole.plug C t) -> (type_denote (typeWithHole.plug C t)) with
    | typeWithHole.HOLE => fun r => v
    | typeWithHole.PairL t1 t2 => fun r => (fieldUpdate r.1 v, r.2)
    | typeWithHole.PairR t1 t2 => fun r => (r.1, fieldUpdate r.2 v)
    | typeWithHole.Array sz idx t => fun r =>
         Vector.replace r idx (fieldUpdate (r !!! idx) v)
    end r.

  Fixpoint getField {C: typeWithHole.typeWithHole} {t: type} 
    (r : type_denote (typeWithHole.plug C t)) 
    : type_denote t :=
    match C return type_denote (typeWithHole.plug C t) -> (type_denote t) with
    | typeWithHole.HOLE => fun r => r
    | typeWithHole.PairL t1 _ => fun r => @getField t1 t r.1 
    | typeWithHole.PairR _ t2 => fun r => @getField t2 t r.2
    | typeWithHole.Array sz idx t' => fun r =>
        @getField t' t (r!!! idx)                                      
    end r.

End typeWithHole.

Module expr.
  Section WithSubstitutionType.
    Context {var: type -> Type}.

    Import unop.
    Import binop.

    (* TODO: value method call; let bindings *)
    Inductive expr : type -> Type := 
    | Var {tx: type} (x: var tx) : expr tx
    | Const {tc: type} (c: type_denote tc) : expr tc
    | Unop {t1 tR: type} (op: unop t1 tR) (e1: expr t1) : expr tR
    | Binop {t1 t2 tR: type} (op: binop t1 t2 tR) (e1: expr t1) (e2: expr t2) : expr tR
    | ITE {k: type} (cond: expr Bool) (tbranch fbranch: expr k) : expr k
    | LetIn (name_hint: string) {tx: type} (ex: expr tx) {tC: type} (eC: var tx -> expr tC) : expr tC
    | LetUpdate {C} {te} (e: expr (typeWithHole.plug C te)) (v: expr te): expr (typeWithHole.plug C te)
    | GetField {C} {t} (e: expr (typeWithHole.plug C t)) : expr t.

  End WithSubstitutionType.

  Arguments expr : clear implicits.

  Fixpoint interp {t} (e: expr type_denote t) : type_denote t :=
    match e in expr _ t return type_denote t with
    | Var _ x => x 
    | Const _ c => c
    | Unop _ _ op e1 => unop.interp op (interp e1)
    | Binop _ _ _ op e1 e2 => binop.interp op (interp e1) (interp e2)
    | ITE _ cond tbranch fbranch => 
        if interp cond then interp tbranch else interp fbranch
    | LetIn _ _ ex _ eC => let x := interp ex in interp (eC x)
    | LetUpdate _ _ e v => 
        typeWithHole.fieldUpdate (interp e) (interp v)
    | GetField _ _ e =>
        typeWithHole.getField (interp e)  
    end.

End expr.

Notation expr := expr.expr.

Module action.
  Section WithSubstitutionType.
    Context {var: type -> Type}.

    Import expr.
    (* StateUpdate -> similar to LetUpdate except does not take input expr *)
    (* StateUpdate' -> GetSt, LetUpdate, PutSt *)
    Inductive action : type -> type -> Type :=
    | GetSt {env_t} : action env_t env_t
    | PutSt {env_t} (st: expr var env_t) : action env_t Unit
    (* | LetNonDet (name_hint: string) {tx: type} {tC: type} (eC: var tx -> action tC) : action tC *)
    | LetInput {env_t} (name_hint: string) {tx: type} {tC: type} (eC: var tx -> action env_t tC) : action env_t tC
    | LetAction {env_t} (name_hint: string) {tx: type} (x: action env_t tx) {tC: type} (eC: var tx -> action env_t tC) : action env_t tC
    | StateUpdate {C} {te} (v: expr var te) : action (typeWithHole.plug C te) Unit
    | Output {env_t} {te: type} (e: expr var te) : action env_t Unit
    | MethodCall {C} {te} {tret} {targ} (arg: expr var targ) (fn: var targ -> @action te tret) : action (typeWithHole.plug C te) tret
    | Return {env_t} {t: type} (e: expr var t) : action env_t t
    .
  End WithSubstitutionType.

  Arguments action : clear implicits.

  Section WithState.
    Let R := Prop.
    Inductive io_t : Type := 
    | IOInput (_: {t & type_denote t})
    | IOOutput (_: {t & type_denote t})
    .
   
    Definition io_trace_t := list io_t.


    Fixpoint interp {env_t: type} {t} (e: action type_denote env_t t) (env: type_denote env_t) (ios: io_trace_t)
      : (type_denote t * type_denote env_t * io_trace_t -> R) -> R :=
      match e in action _ env_t' t' 
              return type_denote env_t' -> (type_denote t' * type_denote env_t' * io_trace_t -> R) -> R with
      | GetSt _ => fun env post => post (env, env, ios)
      | PutSt _ st => fun env post => post (unit_value, expr.interp st, ios)
      (* (* | LetNonDet _ tx tC eC => *) *)
      (* (*     fun post => forall x, interp (eC x) env ios post *) *)
      | LetAction _ _ tx x tC eC =>
          fun env post =>
          interp x env ios (fun '(rX, env', ios') => interp (eC rX) env' ios' post)
      | LetInput _ _ tx tC eC =>
          fun env post => forall x,
          let io : io_t := IOInput (existT _ x) in
          interp (eC x) env (io::ios) post
      | Output _ t te => fun env post =>
          let out_val := expr.interp te in
          let io : io_t := IOOutput (existT _ out_val) in
          post (unit_value, env, io::ios)
      | StateUpdate C te v => fun env post =>
          post(unit_value, typeWithHole.fieldUpdate env (expr.interp v), ios)
      | MethodCall C te tret targ arg fn => fun env post =>
          interp (fn (expr.interp arg)) (typeWithHole.getField env) ios (fun '(r, env', ios') => 
            post(r, typeWithHole.fieldUpdate env env', ios'))                                        
      | Return _ _ e => fun env post => post (expr.interp e, env, ios)
      end env.
  End WithState.
End action.

Module example.
  Section WithSubstitutionType.
    Context {var : type -> Type}.

    Local Coercion var : type >-> Sortclass.
    Let exprVar {t} := expr.Var (var := var) (tx := t).

    Definition add n (x y : Bits n) : expr var (Bits n) :=
      expr.Binop binop.Plus (expr.Const x) (expr.Const y). 

  End WithSubstitutionType.

  Lemma add_ok n (x y: Bits n) :
    expr.interp (add x y) = (x + y)%bv.
  Proof.
    reflexivity.
  Qed.

  (* TODO: struct example *)
End example.

Module notations.

End notations.

(* Module primUnop. *)
(*   Inductive unop : N -> N -> Type := *)
(*   | Not {n} : unop n n *)
(*   | Slice (sz: N) (offset: N) (width: N) *)

(* End primUnop. *)

(* Module primBinop. *)
(* End primBinop. *)

(* Circuit:
   - Cinput/Cregister 
   - var input -> Expr   
   - COutput
   - CBundle 
   
 *)

Module circuitSyntax.
  Section WithSubstitutionType.
    Context {var: type -> Type}.

    Fixpoint compile {env_t: type} {ret: type} (a: action.action var env_t ret) 
                     : var env_t -> expr var (Pair env_t ret).
    Proof.
      destruct a; intro env.
      - (* GetSt *)
        exact (expr.Binop binop.MkPair (expr.Var env) (expr.Var env)).
      - exact (expr.Binop binop.MkPair st (@expr.Const _ (Bits 0) unit_value)).
      - (* LetInput *)
        admit.
      - (* LetAction *)
         pose proof (compile _ _ a env) as X.
         refine (expr.LetIn name_hint _ _).
         + exact (expr.Unop unop.Snd X).
         + intro ret. 
           refine (expr.LetIn "TODO_FOO" (expr.Unop unop.Fst X) _).
           intro env'.
           exact (compile _ _ (eC ret) env').
      - (* StateUpdate *)
         refine (expr.Binop binop.MkPair _ (@expr.Const _ (Bits 0) unit_value)).
         exact (expr.LetUpdate (expr.Var env) v).
      - (* Output *)
        (* refine (expr.Binop binop.MkPair _ (@expr.Const _ (Bits 0) unit_value)). *)
        admit.
      - (* MethodCall *)
        refine (expr.LetIn "TODO" arg _).
        intro arg_interp.
        refine (expr.LetIn "TODO" (expr.GetField (expr.Var env)) _).
        intro sub_env.
        pose proof (compile _ _ (fn arg_interp) sub_env).
        refine (expr.Binop binop.MkPair _ (expr.Unop unop.Snd X)).
        refine (expr.LetUpdate (expr.Var env) (expr.Var sub_env)).
      - (* Return *)
        exact (expr.Binop binop.MkPair (expr.Var env) e).

  (* Local Definition CReg := (string * nat)%type. *)
  (* Section CReg. *)
  (*   Variable x: CReg. *)
  (*   Local Definition cRegName: string := fst x. *)
  (*   Local Definition cRegPos: nat := snd x. *)
  (* End CReg. *)

  (* Local Definition CTmp := (string * nat)%type. *)
  (* Section CTmp. *)
  (*   Variable x: CTmp. *)
  (*   Local Definition cTmpName: string := fst x. *)
  (*   Local Definition cTmpIdx: nat := snd x. *)
  (* End CTmp. *)

  Section WithContext.
    Inductive circuit: N -> Type := .
    (* | CReadReg (x: CReg) (t: type) *)

    (* | CMux {sz} (select: circuit 1) (c1 c2: circuit sz) : circuit sz *)
    (* | CConst {sz} (cst: bv sz) : circuit sz *)
    (* | CReadRegister (reg: reg_t) : circuit (CR reg). *)
  End WithContext.

End circuitSyntax.

Module compiler.
  Import circuitSyntax.
End compiler.

(* Global Instance type_eq_dec : EqDecision type. *)
(* Proof. solve_decision. Defined. *)

(* Global Instance EqDecision_type_denote {tau: type} : EqDecision (type_denote tau). *)
(* Proof. *)
(*   unfold EqDecision. revert tau. *)
(*   fix eq_dec_td 1. *)
(*   destruct tau; cbn; try solve_decision. *)
(*   eapply @vec_dec. *)
(*   solve_decision. *)
(* Defined. *)
