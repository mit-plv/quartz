From Stdlib Require Import BinInt Bits Vector.
From Stdlib Require Import String List.
Import ListNotations.
Local Coercion Zmod.unsigned : Zmod >-> Z.

Open Scope Z_scope.

Module type.
  Local Set Boolean Equality Schemes.
  Inductive type :=
  | Bool
  | Bits (sz: Z)
  | Pair (_ _ : type)
  | Struct (_ : list (string * type))
  | Array (t: type) (sz: nat).

  Fixpoint interp t : Type :=
    match t with
    | Bool => bool
    | Bits sz => bits sz
    | Pair a b => interp a * interp b
    | Struct nts => fold_right (fun nt T => interp (snd nt) * T)%type unit nts
    | Array t n => Vector.t (interp t) n
    end.

  Definition struct := list (string * type).
  Definition Struct_ : struct -> type := Struct.
  Coercion Struct_ : struct >-> type.

  Coercion type.interp: type >-> Sortclass.

  Section WithInhabited.
  Context (inhabited : forall t : type, t).
  Fixpoint inhabited_struct (s : struct) : s :=
    match s with
    | nil => tt
    | cons (_, t) s => (inhabited t, inhabited_struct s)
    end.
  Context (t : type).
  Fixpoint inhabited_array (n : nat) :=
    match n return Vector.t t n with
    | O => Vector.nil _
    | S n => Vector.cons (type.interp t) (inhabited t) n (inhabited_array n)
    end.
  End WithInhabited.
  Fixpoint inhabited (t : type) : t. refine
    match t return t with
    | Bool => false
    | Bits sz => Zmod.zero
    | Pair a b => (inhabited a, inhabited b)
    | Struct s => inhabited_struct inhabited s
    | Array t n => inhabited_array inhabited t n
    end.
  Qed.

  Global Opaque inhabited inhabited_array inhabited_struct.

  Fixpoint eq_dec (a b : type) : { a = b } + { a <> b }. refine
    match a, b with
    | Bool, Bool => left eq_refl
    | Bits a, Bits b =>
        match Z.eq_dec a b with left _ => left _ | right _ => right _ end
    | Struct a, Struct b =>
        match list_eq_dec (fun '(sa, a) '(sb, b) =>
          match string_dec sa sb, eq_dec a b with left _, left _ => left _ | _, _ => right _ end
        ) a b with | left _ => left _ | right _ => right _ end
    | Pair a1 a2, Pair b1 b2 =>
        match eq_dec a1 b1, eq_dec a2 b2 with | left _, left _ => left _ | _, _ => right _ end
    | Array a n, Array b m =>
        match eq_dec a b, PeanoNat.Nat.eq_dec n m with | left _, left _ => left _ | _, _ => right _ end
    | _, _ => right _
    end.
  all : abstract congruence.
  Defined.
End type.

Import type.
Notation Unit := (Bits 0) (only parsing).
Notation unit_value := (bits.of_Z _ 0) (only parsing).

Module struct.
  Notation struct := type.struct (only parsing).
  Search NoDup bool.

  Definition has (s : struct) (n : string) (t : type) : bool :=
    existsb (fun nt => String.eqb (fst nt) n && type_beq (snd nt) t)%bool s.
  Definition Has s n t := Bool.Is_true (has s n t).

  Fixpoint get {s : struct} (n : string) (t : type) : s -> t :=
    match s with | nil => fun _ => inhabited t | cons (nf, tf) s' =>
    match String.eqb nf n with | false => fun s => @get _ n t (snd s) | true =>
    match type.eq_dec tf t with | right _ => fun s => @get _ n t (snd s) | left pf =>
    fun s => eq_rect tf type.interp (fst s) _ pf
    end end end.

  Fixpoint upd {s : struct} (n : string) (t : type) : s -> (t -> t) -> s :=
    match s with | nil => fun s _ => s | cons (nf, tf) s' =>
    match String.eqb nf n with | false => fun s v => (fst s, @upd s' n t (snd s) v) | true =>
    match type.eq_dec t tf with | right _ => fun s v => (fst s, @upd s' n t (snd s) v) | left pf =>
    fun s v => (eq_rect t (fun t => type.interp t -> type.interp t) v _ pf (fst s) , snd s)
    end end end.

  Definition put {s : struct} (n : string) (t : type) (sv : s) (v : t) :=
    @upd s n t sv (fun _ => v).

  Local Open Scope string_scope.
  Example get_ab_b : @get [("a", Bits 7); ("b", Bool)] "b" Bool = fun r => fst (snd r).
  Proof. cbv [get eq_dec eq_rect String.eqb Ascii.eqb Bool.eqb]. trivial. Qed.
  Example get_ab_c : @get [("a", Bits 7); ("b", Bool)] "c" Bool = fun r => inhabited Bool.
  Proof. cbv [get eq_dec eq_rect String.eqb Ascii.eqb Bool.eqb]. trivial. Qed.
End struct.

Module unop.
  Inductive unop : type -> type -> Type :=
  | Not {n} : unop (Bits n) (Bits n)
  .

  Definition interp {a b} (op: unop a b) : type.interp a -> type.interp b :=
    match op in unop a b return a -> b with
    | Not => Zmod.not
    end.
End unop.
Notation unop := unop.unop (only parsing).

Module binop.
  Inductive compare := cLt | cGt | cLe | cGe.

  Inductive binop : type -> type -> type -> Type :=
  | Plus {n} : binop (Bits n) (Bits n) (Bits n)
  | And {n} : binop (Bits n) (Bits n) (Bits n)
  | Or {n} : binop (Bits n) (Bits n) (Bits n)
  | Lsl {n} : binop (Bits n) (Bits n) (Bits n)
  | Lsr {n} : binop (Bits n) (Bits n) (Bits n)
  | Asr {n} : binop (Bits n) (Bits n) (Bits n)
  | EqBits {n} : binop (Bits n) (Bits n) Bool
  | Compare (signed: bool) (c: compare) {n} : binop (Bits n) (Bits n) Bool
  | MkPair {a b: type} : binop a b (Pair a b).

  Definition interp {a b c} (op: binop a b c) : a -> b -> c :=
    match op in binop a b c return a -> b -> c with
    | Plus => Zmod.add
    | And => Zmod.and
    | Or => Zmod.or
    | Lsl => fun a b => Zmod.slu a b
    | Lsr => fun a b => Zmod.sru a b
    | Asr => fun a b => Zmod.srs a b
    | EqBits => Zmod.eqb
    | Compare signed c => fun a b =>
        match c with cLt => Z.ltb | cGt => Z.gtb | cLe => Z.leb | cGe => Z.geb end
        (if signed then Zmod.signed a else Zmod.unsigned a)
        (if signed then Zmod.signed b else Zmod.unsigned b)
    | MkPair => Datatypes.pair
    end.
End binop.
Notation binop := binop.binop (only parsing).

Module typeWithHole.
  Inductive typeWithHole :=
  | HOLE
  | PairL (t1 : typeWithHole) (t2: type)
  | PairR (t1 : type) (t2: typeWithHole)
  | Struct (l : struct) (n : string) (t : typeWithHole) (r : struct)
  | Array (sz: nat) (t: typeWithHole).

  Fixpoint plug (C : typeWithHole) (t : type) : type :=
    match C with
    | HOLE => t
    | PairL t1 t2 => type.Pair (plug t1 t) t2
    | PairR t1 t2 => type.Pair t1 (plug t2 t)
    | Struct l n C r => type.Struct (l ++ cons (n, plug C t) r)
    | Array sz t' => type.Array (plug t' t) sz
    end.

  Fixpoint indices (t : typeWithHole) : type :=
    match t with
    | HOLE => Unit
    | PairL t _ | PairR _ t | Struct _ _ t _ => indices t
    | Array sz t => Pair (Bits (Z.log2_up (Z.of_nat sz))) (indices t)
    end.

  Axiom Vector__get : forall {T n}, Vector.t T n -> bits (Z.log2_up (Z.of_nat n)) -> T.
  Axiom Vector__mod : forall {T n}, Vector.t T n -> bits (Z.log2_up (Z.of_nat n)) -> (T -> T) -> Vector.t T n.

  Fixpoint getField C : forall t, plug C t -> indices C -> t :=
    match C with
    | HOLE => fun t r i => r
    | PairL a b => fun _ r i => getField a _ (fst r) i
    | PairR a b => fun _ r i => getField b _ (snd r) i
    | Struct _ n t _ => fun _ r i => getField t _ (struct.get n _ r) i
    | Array sz t => fun _ r i => getField t _ (Vector__get r (fst i)) (snd i)
    end.
  Arguments getField {_ _}.

  Fixpoint updField C : forall t, plug C t -> indices C -> (t -> t) -> plug C t :=
    match C with
    | HOLE => fun t r i f => f r
    | PairL a b => fun _ r i v => (updField a _ (fst r) i v, snd r)
    | PairR a b => fun _ r i v => (fst r, updField b _ (snd r) i v)
    | Struct _ n t _ => fun _ r i v => struct.upd n _ r v
    | Array sz t => fun _ r i v => Vector__mod r (fst i) (fun r => updField _ _ r (snd i) v)
    end.
  Arguments updField {_ _}.
End typeWithHole.
Notation typeWithHole :=typeWithHole.typeWithHole (only parsing).

Coercion typeWithHole.plug : typeWithHole >-> Funclass.
Coercion typeWithHole.indices : typeWithHole >-> type.

Module expr.
  Section WithSubstitutionType.
    Context {var: type -> Type}.
    Definition this t := var t.

    Inductive expr : type -> Type :=
    | Var {tx: type} (x: var tx) : expr tx
    | Const {tc: type} (c: type.interp tc) : expr tc
    | Unop {t1 tR: type} (op: unop t1 tR) (e1: expr t1) : expr tR
    | Binop {t1 t2 tR: type} (op: binop t1 t2 tR) (e1: expr t1) (e2: expr t2) : expr tR
    | Cond {t} (_ : expr Bool) (a b : expr t) : expr t
    | Let (name_hint: string) {tx: type} (ex: expr tx) {tC: type} (eC: var tx -> expr tC) : expr tC
    | Get {C : typeWithHole} {t} (r : expr (C t)) (i : expr C) : expr t
    | Upd {C : typeWithHole} {t} (r : expr (C t)) (i : expr C)
       (v : var t -> expr t) : expr (typeWithHole.plug C t).

    Definition tt := @Const Unit unit_value.
    Definition true := @Const Bool true.
    Definition false := @Const Bool false.
    Definition zero {n} := @Const (Bits n) Zmod.zero.
  End WithSubstitutionType.
  Arguments expr : clear implicits.

  Fixpoint interp {t} (e: expr type.interp t) : type.interp t :=
    match e in expr _ t return type.interp t with
    | Var x => x
    | Const c => c
    | Unop op e1 => unop.interp op (interp e1)
    | Binop op e1 e2 => binop.interp op (interp e1) (interp e2)
    | Cond e a b => if interp e then interp a else interp b
    | Let _ ex eC => let x := interp ex in interp (eC x)
    | Get r i => typeWithHole.getField (interp r) (interp i)
    | Upd r i fv => typeWithHole.updField (interp r) (interp i) (fun v => interp (fv v))
    end.

  Declare Custom Entry quartz_expr.
  Notation "quartz_expr:( e )" := e (e custom quartz_expr, format "'quartz_expr:(' e ')'").
  Notation "$ v" := v (in custom quartz_expr at level 0, v constr at level 0, format "'$' v").
  Notation "x" := (x) (in custom quartz_expr, x global, only parsing).
  Notation "f x" := (f x) (in custom quartz_expr at level 10).
  Notation "'let' x := e1 'in' e2"        := (Let "$let" e1 (fun x => e2))
   (in custom quartz_expr at level 100, x constr at level 0, e1 custom quartz_expr, e2 custom quartz_expr).
  Notation "this!" := (ltac:(match goal with x : this _ |- _ => exact x end))
    (in custom quartz_expr, only parsing).
End expr.
Notation expr := expr.expr.

Module action.
  Import expr.
  Section WithSubstitutionType.
    Context {var: type -> Type}.
    Local Notation this := (@expr.this var).
    Local Notation expr := (@expr.expr var).

    Inductive action : type -> type -> Type :=
    | Ret {s t} (e : this s -> expr t) : action s t
    | Put {s} (e : this s -> expr s) : action s Unit
    | Bind {s} (name_hint : string) {tx} (a : action s tx) {t}
      (aC : var tx -> action s t) : action s t
    | Cond {s t} (_ : this s -> expr Bool) (a b : action s t) : action s t
    | Upd {C : typeWithHole} {t r} (s := C t) (i : this s -> expr C) (fv : this s -> action t r) : action s r
    .

    Definition UpdPut {C : typeWithHole} {t} (i : expr C) (v : expr t) :=
      Upd (C:=C) (t:=t) (fun _ => i) (fun _ => Put (fun _ => v)).

    Definition Seq {s a b} (a : action s a) (b : action s b) :=
      Bind "$Seq" a (fun _ => b).
  End WithSubstitutionType.
  Arguments action : clear implicits.

  Section WithState.
    Fixpoint interp {s t} (e: action type.interp s t) : s -> s * t :=
      match e in action _ s t return s -> s * t with
      | Ret e => fun s => (s, expr.interp (e s))
      | Put e => fun s => let v := expr.interp (e s) in (v, unit_value)
      | Bind _ a aC => fun s =>
          let '(s, v) := interp a s in
          interp (aC v) s
      | Cond e a b => fun s => if expr.interp (e s) then interp a s else interp b s
      | Upd i fv => fun s =>
          let i := expr.interp (i s) in
          let ms := typeWithHole.getField s i in
          let (ms, v) := interp (fv s) ms in
          (typeWithHole.updField s i (fun _ => ms), v)
      end.
  End WithState.

  Declare Custom Entry quartz_action.
  Notation "quartz_action:( a )" := a (a custom quartz_action, format "'quartz_action:(' a ')'").
  Notation "$ v" := v (in custom quartz_action at level 0, v constr at level 0, format "'$' v").
  Notation "x" := (x) (in custom quartz_action, x global, only parsing).
  Notation "a1 ; a2" := (Seq a1 a2)
    (in custom quartz_action at level 1, right associativity, format "'[v' a1 ; '/' a2 ']'").
  Notation "this!" := (ltac:(match goal with x : this _ |- _ => exact x end))
    (in custom quartz_action, only parsing).
  Notation "'return' e" := (Ret (fun _ => e))
    (in custom quartz_action at level 1, e custom quartz_expr).
End action.
Notation action := action.action (only parsing).

Module example.
  Section WithSubstitutionType.
    Context {var : type -> Type}.

    Local Coercion var : type >-> Sortclass.
    Let exprVar {t} := expr.Var (var := var) (tx := t).

    Definition add {n} (x y : Bits n) : expr var (Bits n) :=
      expr.Binop binop.Plus (expr.Const x) (expr.Const y).

  End WithSubstitutionType.

  Lemma add_ok n (x y: Bits n) :
    expr.interp (add x y) = Zmod.add x y.
  Proof. trivial. Qed.

End example.


Module flat.
  Section WithSubstitutionType.
  Context {var: type -> Type}.
  (* cases of [expr.expr] without binders *)
  Inductive expr : type -> Type :=
  | Var {tx: type} (x: var tx) : expr tx
  | Const {tc: type} (c: type.interp tc) : expr tc
  | Unop {t1 tR: type} (op: unop t1 tR) (e1: expr t1) : expr tR
  | Binop {t1 t2 tR: type} (op: binop t1 t2 tR) (e1: expr t1) (e2: expr t2) : expr tR
  | Cond {t} (_ : expr Bool) (a b : expr t) : expr t
  | Get {C : typeWithHole} {t} (r : expr (C t)) (i : expr C) : expr t.

  (* cases of [expr.expr] with binders, returning T instead of expr t *)
  Inductive flat {T : Type} :=
  | Let (name_hint: string) {tx: type} (ex: expr tx) (eC: var tx -> flat)
  | Upd {C : typeWithHole} {t} (x: expr (C t)) (i : expr C) (v: expr t) (eC : var (C t) -> flat)
  | Ret (_ : T).

  Definition let_ {T} (name_hint: string) {tx: type} (ex: expr tx) : forall (eC: var tx -> flat), @flat T :=
    match ex with
    | Var v => fun eC => eC v
    | ex => fun eC => Let name_hint ex eC
    end.
  End WithSubstitutionType.

  #[global] Arguments expr : clear implicits.
  #[global] Arguments flat : clear implicits.

  Section WithSubstitutionType.
  Context {var: type -> Type}.
  Fixpoint bind {A B} (a : flat var A) (b : A -> flat var B) : flat var B :=
    match a with
    | Let x e C => Let x e (fun v => bind (C v) b)
    | Upd e i v C => Upd e i v (fun v => bind (C v) b)
    | Ret a => b a
    end.
  End WithSubstitutionType.
End flat.
Notation flat := flat.flat (only parsing).

Module flatten.
  Section WithSubstitutionType.
  Context {var: type -> Type}.
  Fixpoint expr {t} (e : expr var t) : flat var (flat.expr var t) :=
    match e in expr _ t return flat var (flat.expr var t) with
    | expr.Var x => flat.Ret (flat.Var x)
    | expr.Const c => flat.Ret (flat.Const c)
    | expr.Unop u e => flat.bind (expr e) (fun v => flat.Ret (flat.Unop u v))
    | expr.Binop u e1 e2 =>
      flat.bind (expr e1) (fun v1 =>
      flat.bind (expr e2) (fun v2 =>
      flat.Ret (flat.Binop u v1 v2)))
    | expr.Cond e1 e2 e3 =>
      flat.bind (expr e1) (fun v1 =>
      flat.bind (expr e2) (fun v2 =>
      flat.bind (expr e3) (fun v3 =>
      flat.Ret (flat.Cond v1 v2 v3))))
    | expr.Get e1 e2 =>
      flat.bind (expr e1) (fun v1 =>
      flat.bind (expr e2) (fun v2 =>
      flat.Ret (flat.Get v1 v2)))
    | expr.Let x e C =>
      flat.bind (expr e) (fun e =>
      flat.let_ x e (fun v => expr (C v)))
    | expr.Upd es ei e3 =>
      flat.bind (expr es) (fun es =>
      flat.bind (expr ei) (fun ei =>
      flat.let_ "$eupd" (flat.Get es ei) (fun ef =>
      flat.bind (expr (e3 ef)) (fun ef =>
      flat.Upd es ei ef (fun es => flat.Ret (flat.Var es))))))
    end.

    Fixpoint action {s t} (a : action var s t) : (var s -> flat var (flat.expr var s * flat.expr var t)) :=
      match a in action _ s t return (var s -> flat var (flat.expr var s * flat.expr var t)) with
      | action.Ret e => fun s =>
        flat.bind (expr (e s)) (fun e => flat.Ret (flat.Var s, e))
      | action.Put e => fun s =>
        flat.bind (expr (e s)) (fun e =>
        flat.Ret (e, @flat.Const _ Unit unit_value ))
      | action.Bind x a aC => fun s =>
        flat.bind (action a s) (fun '(es, ev) =>
        flat.let_ (x++"$s") es (fun s =>
        flat.let_ x ev (fun v =>
        action (aC v) s)))
      | action.Upd ei fv => fun s =>
        flat.bind (expr (ei s)) (fun ei =>
        flat.let_ "$aupd" (flat.Get (flat.Var s) ei) (fun fs =>
        flat.bind (action (fv s) fs) (fun '(rs, rv) =>
        flat.Upd (flat.Var s) ei rs (fun s =>
        flat.Ret (flat.Var s, rv)))))
      | action.Cond c a1 a2 => fun s =>
        flat.bind (action a1 s) (fun '(s1, e1) =>
        flat.bind (action a2 s) (fun '(s2, e2) =>
        flat.bind (expr (c s)) (fun c =>
        flat.Let "$acs" (flat.Cond c (s1) (s2)) (fun s =>
        flat.Let "$ace" (flat.Cond c e1 e2) (fun e =>
        flat.Ret (flat.Var s, flat.Var e))))))
      end.
  End WithSubstitutionType.

  (*
  Theorem correct:
    forall env_t ret (a: action.action type.interp env_t ret) (env: env_t),
      expr.interp (compile a env) = action.interp a env.
  Proof.
    (* TODO: Fix proof. *)
    induction a; intros; cbn; auto.
    - intros. rewrite IHa. rewrite H. case_match; auto.
    - intros. case_match. rewrite H. rewrite H0. auto.
  Qed.
     *)
End flatten.

From quartz Require VerilogSyntax.

Require Import AdmitAxiom.

Module verilog.
  Import (notations)ListNotations.
  Import -(notations,options)VerilogSyntax.
  Import flat.
  Local Unset Asymmetric Patterns.
  Section WithVerilogIdentifier.
    Context {VId : Set} (field_name : string -> VId).
    Context {gensym_state : Type} (gensym : gensym_state -> string -> VId * gensym_state).
    Let var (_ : type) := VId.

    Fixpoint const {t : type} : t -> @VExpr VId :=
      match t return t -> @VExpr VId with
      | Bool => fun v => VExprPriLiteral (VIntegralBinary (Some 1) (Z.b2z v))
      | Bits n => fun v =>
          VExprPriLiteral (
          (if Z.ltb n 8 return _->_->VIntegralNumber
            then VDecimalNumberB else VIntegralHex)
          (Some n) (Zmod.unsigned v))
      | _ => fun _ => ltac:(admit)
      end.

    Fixpoint lvalue (c : typeWithHole) (e : @VExpr VId) : @VExpr VId :=
      match c with
      | typeWithHole.HOLE => e
      | typeWithHole.Struct _ n c _ =>
        lvalue c (VExprHier e (VExprId (field_name n)))
      | _ => ltac:(admit)
      end.

    Definition unop {a b} (u : unop a b) : VUniOp :=
      match u with
      | unop.Not => VUniNot
      end.

    Fixpoint expr {t} (e : expr var t) : @VExpr VId :=
      match e with
      | Var x => VExprId x
      | Const c => const c
      | Cond c t f => VExprCond (@expr _ c) (@expr _ t) (@expr _ f)
      | Unop u e => VExprUniOp (unop u) (@expr _ e)
      | Binop _ _ _ => ltac:(admit)
      | @Get _ c _ e TODO_i => lvalue c (expr e)
      end.

    Fixpoint stmts {a b} (s : flat var (flat.expr var a * flat.expr var b)) (g : gensym_state) (fs ft : VId) : list (@VStatementItem VId) :=
      match s with
      | Let x ex eC =>
          let '(x, g) := gensym g x in
          VStatementItemBlockingAssignNormal (VExprId x) (expr ex) ::
          @stmts _ _ (eC x) g fs ft
      | @Upd _ _ c _ e TODO_i v eC =>
          let '(x, g) := gensym g EmptyString in
          VStatementItemBlockingAssignNormal (VExprId x) (expr e) ::
          VStatementItemBlockingAssignNormal (lvalue c (VExprId x)) (expr v) ::
          @stmts _ _ (eC x) g fs ft
      | Ret (a, b) =>
          VStatementItemBlockingAssignNormal (VExprId fs) (expr a) ::
          VStatementItemBlockingAssignNormal (VExprId ft) (expr b) ::
          nil
      end.
  End WithVerilogIdentifier.
End verilog.

Local Open Scope string_scope.
Import typeWithHole VerilogSyntax.
Compute verilog.lvalue id HOLE (VExprId "x").
Compute verilog.lvalue id (Struct [("aa", Bool)] "bb" (Struct [("a", Bool)] "b" HOLE []) []) (VExprId "x").

Module fifo1.
  Import typeWithHole expr action.
  Definition T := Bits 42.
  Definition state := type.Struct [("len", Bool); ("data", T)].
  Definition enq {var} (d : var T) : action var state Unit := quartz_action:(
    $(UpdPut (C:=typeWithHole.Struct [] "len" HOLE [("data", T)]) tt true);
    $(UpdPut (C:=typeWithHole.Struct [("len", Bool)] "data" HOLE []) tt (Var d))).
  Definition len {var} (s : var state) : expr var Bool :=
    Get (C:=typeWithHole.Struct [] "len" HOLE [("data", T)]) (Var s) tt.
  Definition peek {var} (s : var state) : expr var T :=
    Get (C:=typeWithHole.Struct [("len", Bool)] "data" HOLE []) (Var s) tt.
  Definition deq {var} : action var state T := quartz_action:(
    $(UpdPut (C:=typeWithHole.Struct [] "len" HOLE [("data", T)]) tt false);
    $(Ret peek)).
End fifo1.

Require Import DecimalString.
Definition gensym_st : Type := list string * Z.
Definition gensym (st : gensym_st) (s : string) : string * gensym_st :=
  let (st, n) := st in
  if orb (String.eqb "" s) (List.existsb (String.eqb s) st)
  then let s := s ++ "$" ++ NilEmpty.string_of_int (Z.to_int n) in (s, (cons s st, n+1))
  else (s, (cons s st, n)).
Import expr action fifo1.
Local Notation "verilog_stmt:( t ')'" := t (t custom verilog_stmt).
Local Notation "$ x" := (x) (x constr at level 0, in custom verilog_expr at level 1).
Compute let d:="d" in let s:="s" in
  verilog.stmts id gensym (flatten.action (quartz_action:(
  $(enq d);(* void action method call *)
  deq; (* non-void action method call *)
  return
    let v := len this! in (* value method call *)
    $(expr.Var v)
  )) s) (nil, 0) "FINAL_STATE" "FINAL_VALUE".

(* ...which in slightly less verbose concrete syntax gives:
$aupd = s.len
$0 = s
$0.len = 1'b1
_unit = 0'd0
$aupd$1 = $0.data
$2 = $0
$2.data = d
_ret1 = 0'd0
$aupd$3 = $2.len
$4 = $2
$4.len = 1'b0
_unit$5 = 0'd0
_ret2 = $4.data
_let = $4.len
FINAL_STATE = $4
FINAL_VALUE = _let
 *)

(* NEXT STEPS:
   - Verilog
     - Expr -> always_comb verilog blocks
     - Reference: https://github.com/Cherified/Guru/blob/main/PrettyPrinter/CodePrinter.hs
   - Notations :) --> customEntry fun
     - Reference: https://github.com/mit-plv/bedrock2/blob/master/bedrock2/src/bedrock2/NotationsCustomEntry.v#L9
     - Reference: https://github.com/mit-plv/fiat2/blob/main/fiat2/src/fiat2/Notations.v#L158
     - Reference: VerilogSyntax.v
   - Pretty Gallina reflection/verification stuffs
     - Reification of lvalues/holes
       - Ltac2 silliness
*)

