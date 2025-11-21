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
    | LetUpdate {C} {te} (e: expr (typeWithHole.plug C te)) (v: expr te): expr (typeWithHole.plug C te).

  End WithSubstitutionType.

  Arguments expr : clear implicits.
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
        let interp_e := interp e in 
        let interp_v := interp v in 
        fieldUpdate interp_e interp_v 
    end.

End expr.

Notation expr := expr.expr.

Module action.
  Section WithSubstitutionType.
    Context {var: type -> Type}.

    Import expr.

    Inductive action : type -> Type :=
    (* | ReadState   *)
    (* | Bind (name_hint: string) {tx: type} (ex: expr var tx) {tC: type} (eC: var tx -> action tC) : action tC *)
    | LetAction (name_hint: string) {tx: type} (x: action tx) {tC: type} (eC: var tx -> action tC) : action tC

    (* | If  *)
    (* | IfElse (s: string) (p: Expr Bool) k' (t f: Action k') (cont: ty k' -> Action k) *)

    | Return {t: type} (e: expr var t) : action t
    .
  End WithSubstitutionType.

  Arguments action : clear implicits.

  Definition env_t : Type.
  Admitted.

  (* Fixpoint interp {t} (e: action type_denote t) : type_denote t := *)
  (*   match e with *)
  (*   | Return _ e => e *)
  (*   end. *)

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

Module circuitSyntax.
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
