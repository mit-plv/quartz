From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
From Stdlib Require Import BinInt Bits.
From Stdlib Require Import String List.
From Stdlib Require Vector.
Import ListNotations.

Require Import ident_to_string.

Open Scope Z_scope.

Module type.
  Local Set Boolean Equality Schemes.
  Inductive type :=
  | Bool
  | Bits (sz: Z)
  | Pair (_ _ : type)
  | Struct (_ : list (string * type))
  | Array (t: type) (sz: nat).
  Notation Unit := (Bits 0) (only parsing).

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

  Section WithDefault. (* default values for out-of-bounds array access *)
  Context (default : forall t : type, t).
  Fixpoint default_struct (s : struct) : s :=
    match s with
    | nil => tt
    | cons (_, t) s => (default t, default_struct s)
    end.
  Context (t : type).
  Fixpoint default_array (n : nat) :=
    match n return Vector.t t n with
    | O => Vector.nil _
    | S n => Vector.cons (type.interp t) (default t) n (default_array n)
    end.
  End WithDefault.
  Fixpoint default (t : type) : t :=
    match t return t with
    | Bool => false
    | Bits sz => Zmod.zero
    | Pair a b => (default a, default b)
    | Struct s => default_struct default s
    | Array t n => default_array default t n
    end.

  Ltac2 Type exn ::= [ ReifyUnknown (constr) | InductiveNotAPrimitiveRecord (constr) ].
  Ltac2 rec reify t :=
    lazy_match! t with
    | type.interp ?t => t
    | bool => 'type.Bool
    | bits ?n => constr:(type.Bits $n)
    | prod ?t1 ?t2 =>
        let rt1 := reify t1 in
        let rt2 := reify t2 in
        constr:(type.Pair $rt1 $rt2)
    | Vector.t ?t ?n =>
        let rt := reify t in
        constr:(type.Array $rt $n)
    | _ => match UConstr.kind t with UConstr.Ind ind inst =>
      let pp := match Ind.get_projections (Ind.data ind) with Some pp => pp | _ => Control.throw (InductiveNotAPrimitiveRecord t) end in
      let r := Array.fold_right (fun pp acc =>
          let c := Option.get (Proj.to_constant pp) in
          let n := constr_string_of_string (Ident.to_string (List.last (Env.path (Std.ConstRef c)))) in
          let e := UConstr.make (UConstr.Constant c inst) in
          let t := match UConstr.kind (Constr.type e) with UConstr.Prod _ t => t | _ => 'Empty_set end in
          let rt := reify t in
          constr:(cons ($n, $rt) $acc)
        ) pp constr:(@nil (String.string * type)) in
      constr:(type.Struct $r)
    | _ => Control.throw (ReifyUnknown t)
  end end.

  Notation reify'' state := (ltac2:(let r := type.reify (pretype state) in exact $r)) (only parsing).
  Definition tt : Unit := Zmod.zero.
End type.
Import type.

Module struct.
  Notation struct := type.struct (only parsing).

  Fixpoint fieldType (s : struct) (n : string) : type :=
    match s with
    | nil => Unit
    | cons nt s =>
      if String.eqb (fst nt) n
      then snd nt
      else fieldType s n
    end.

  Fixpoint get {s : struct} n : s -> fieldType s n :=
    match s with
    | nil => fun _ => tt
    | cons nt s =>
        let b := String.eqb (fst nt) n in
        if b return Struct (nt::s) -> if b then snd nt else fieldType s n
        then fst
        else fun v => get n (snd v)
    end.

  Fixpoint upd {s : struct} n : s -> (fieldType s n -> fieldType s n) -> s :=
    match s with
    | nil => fun s _ => s
    | cons nt s =>
        let b := String.eqb (fst nt) n in
        if b return
          Struct (nt::s) ->
          ((if b then snd nt else fieldType s n) -> if b then snd nt else fieldType s n)
          -> Struct (nt::s)
        then fun v f => (f (fst v), snd v)
        else fun v f => (fst v, @upd _ n (snd v) f)
    end.

  Definition put {s : struct} (n : string) (t : type) (sv : s) (v : fieldType s n) :=
    @upd s n sv (fun _ => v).

  Local Open Scope string_scope.
  Example get_ab_a : @get [("a", Bits 7); ("b", Bool)] "a" = fun r => fst r.
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.
  Example get_ab_b : @get [("a", Bits 7); ("b", Bool)] "b" = fun r => fst (snd r).
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.
  Example get_ab_c : @get [("a", Bits 7); ("b", Bool)] "c" = fun r => tt.
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.

  Ltac2 rep v :=
    match UConstr.kind (Constr.type v) with
    | UConstr.Ind ind inst =>
      let arrproj := Option.get (Ind.get_projections (Ind.data ind)) in
      Array.fold_right (fun p acc =>
        let c := Option.get (Proj.to_constant p) in
        let e := UConstr.make (UConstr.Constant c inst) in
        let e := constr:($e $v) in
        constr:(pair $e $acc)
        ) arrproj 'Datatypes.tt
    | _ => Control.throw (type.ReifyUnknown (Constr.type v))
    end.
End struct.

Module Vector.
  Section WithT.
  Context {T : Type}.
  Fixpoint upd {n} (xs : Vector.t T n) (i : nat) (f : T -> T) : Vector.t T n :=
    match xs in Vector.t _ n return Vector.t T n with
    | Vector.nil _ => Vector.nil _
    | Vector.cons _ x _ xs =>
      match i with
      | O => Vector.cons _ (f x) _ xs
      | S i => Vector.cons _ x _ (upd xs  i f)
      end
    end.
  End WithT.
End Vector.

Module unop.
  Inductive unop : type -> type -> Type :=
  | IsZero {n} : unop (Bits n) Bool
  | Not {n} : unop (Bits n) (Bits n) (* bitwise completement *)
  | Opp {n} : unop (Bits n) (Bits n) (* arithmetic negation *)
  | UnsignedResize {n m} : unop (Bits n) (Bits m) (* zero-extend or truncate *)
  | SignedResize {n m} : unop (Bits n) (Bits m) (* sign-extend or truncate *)
  .

  Definition interp {a b} (op: unop a b) : type.interp a -> type.interp b :=
    match op in unop a b return a -> b with
    | IsZero => Zmod.eqb Zmod.zero
    | Not => Zmod.not
    | Opp => Zmod.opp
    | UnsignedResize => fun v => bits.of_Z _ (Zmod.unsigned v)
    | SignedResize => fun v => bits.of_Z _ (Zmod.signed v)
    end.
End unop.
Notation unop := unop.unop (only parsing).

Module binop.
  Inductive compare := cLt | cGt | cLe | cGe.

  Inductive binop : type -> type -> type -> Type :=
  | Add {n} : binop (Bits n) (Bits n) (Bits n)
  | And {n} : binop (Bits n) (Bits n) (Bits n)
  | Or {n} : binop (Bits n) (Bits n) (Bits n)
  | Slu {n m} : binop (Bits n) (Bits m) (Bits n)
  | Sru {n m} : binop (Bits n) (Bits m) (Bits n)
  | Srs {n m} : binop (Bits n) (Bits m) (Bits n)
  | EqBits {n} : binop (Bits n) (Bits n) Bool
  | Compare (signed: bool) (c: compare) {n} : binop (Bits n) (Bits n) Bool
  | MkPair {a b: type} : binop a b (Pair a b).

  Definition interp {a b c} (op: binop a b c) : a -> b -> c :=
    match op in binop a b c return a -> b -> c with
    | Add => Zmod.add
    | And => Zmod.and
    | Or => Zmod.or
    | Slu => fun a b => Zmod.slu a (Zmod.unsigned b)
    | Sru => fun a b => Zmod.sru a (Zmod.unsigned b)
    | Srs => fun a b => Zmod.srs a (Zmod.unsigned b)
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
     {NoDup_by_fun_eq_refl : forall t, struct.fieldType (l ++ (n, t) :: r) n = t}
  | Array (sz : nat) (t : typeWithHole) (index_width : Z).

  Fixpoint plug (C : typeWithHole) (t : type) : type :=
    match C with
    | HOLE => t
    | PairL t1 t2 => type.Pair (plug t1 t) t2
    | PairR t1 t2 => type.Pair t1 (plug t2 t)
    | Struct l n C r => type.Struct (l ++ cons (n, plug C t) r)
    | Array sz t' _ => type.Array (plug t' t) sz
    end.

  Fixpoint indices (t : typeWithHole) : type :=
    match t with
    | HOLE => Unit
    | PairL t _ | PairR _ t | Struct _ _ t _ => indices t
    | Array sz t n => Pair (Bits n) (indices t)
    end.

  Fixpoint get C : forall t, plug C t -> indices C -> t :=
    match C return forall t, plug C t -> indices C -> t with
    | HOLE => fun t r i => r
    | PairL a b => fun _ r i => get a _ (fst r) i
    | PairR a b => fun _ r i => get b _ (snd r) i
    | @Struct _ n t _ pf => fun _ r i => get t _ (eq_rect _ _ (struct.get n r) _ (pf _)) i
    | Array sz t _ => fun _ r i => get t _
        (List.nth_default (default _) (Vector.to_list r) (Z.to_nat (Zmod.unsigned (fst i)))) (snd i)
    end.
  Arguments get {_ _}.

  Fixpoint upd C : forall t, plug C t -> indices C -> (t -> t) -> plug C t :=
    match C return forall t, plug C t -> indices C -> (t -> t) -> plug C t with
    | HOLE => fun t r i f => f r
    | PairL a b => fun _ r i f => (upd a _ (fst r) i f, snd r)
    | PairR a b => fun _ r i f => (fst r, upd b _ (snd r) i f)
    | @Struct _ n t _ pf => fun _ r i f =>
        struct.upd n r (eq_rect (plug t _) (fun u => u -> u) (fun v => upd t _ v i f) _ (eq_sym (pf _)))
    | Array sz t _ => fun _ r i f =>
        Vector.upd r (Z.to_nat (Zmod.unsigned (fst i))) (fun r => upd _ _ r (snd i) f)
    end.
  Arguments upd {_ _}.

  Ltac2 reify_field p0c :=
    match UConstr.kind p0c with
    | UConstr.Constant c0 inst =>
      match Proj.of_constant c0 with
      | Some p0 =>
        lazy_match! type.reify (UConstr.make (UConstr.Ind (Proj.ind p0) inst)) with
        | type.Struct ?rs =>
    let rec firstn n l := if Int.le n 0
      then lazy_match! l with nil => l | @cons ?t _ _ => constr:(@nil $t) end
      else lazy_match! l with @cons ?t ?x ?l => let l := firstn (Int.sub n 1) l in constr:(@cons $t $x $l) end in
    let rec skipn n l := if Int.le n 0 then l else lazy_match! l with cons _ ?l => skipn (Int.sub n 1) l end in
    let hd l := lazy_match! l with @nil _ => l | @cons _ ?x _ => x end in
          let l := firstn (Proj.index p0) rs in
          let (n, t) := lazy_match! hd (skipn (Proj.index p0) rs) with (?n, ?t) => (n, t) end in
          let r := skipn (Int.add 1 (Proj.index p0)) rs in
          (constr:(@Struct $l $n HOLE $r (fun _ => eq_refl)), t)
        | _ => Control.throw (type.ReifyUnknown p0c)
        end
      | _ => Control.throw (type.ReifyUnknown p0c)
      end
    | _ => Control.throw (type.ReifyUnknown p0c)
    end.
End typeWithHole.
Notation typeWithHole :=typeWithHole.typeWithHole (only parsing).

Coercion typeWithHole.plug : typeWithHole >-> Funclass.
Coercion typeWithHole.indices : typeWithHole >-> type.

Module expr.
  Section WithSubstitutionType.
    Context {var: type -> Type}.

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

    Definition tt := @Const Unit Zmod.zero.
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
    | Get r i => typeWithHole.get (interp r) (interp i)
    | Upd r i fv => typeWithHole.upd (interp r) (interp i) (fun v => interp (fv v))
    end.

  Declare Custom Entry quartz_expr.
  Notation "quartz_expr:( e )" := e (e custom quartz_expr, only parsing).
  Notation "# v" := (expr.Var v) (in custom quartz_expr at level 0, v constr at level 0, format "'#' v").
  Notation "$ v" := v (in custom quartz_expr at level 0, v constr at level 0, format "'$' v").
  Notation "x" := (x) (in custom quartz_expr, x global, only parsing).
  Notation "f x" := (f x) (in custom quartz_expr at level 10).
  Notation "x == y" := (Binop (binop.EqBits) x y) (in custom quartz_expr at level 70).
  Notation "'let' x := e1 'in' e2"        := (Let "$let" e1 (fun x => e2))
    (in custom quartz_expr at level 200, x constr at level 0, e1 custom quartz_expr, e2 custom quartz_expr).

  Definition this (var : type -> Type) t := var t.
  Notation "this!" := (ltac:(match goal with x : @this _ _ |- ?g => exact (Var x) || exact x end))
    (in custom quartz_expr, only parsing).
  Notation "v 'at' f" := (ltac2:(let (c, t) := typeWithHole.reify_field (pretype f) in let v := pretype v in eexact (Get (C:=$c) (t:=$t) $v tt)))
    (in custom quartz_expr at level 10, f global, v custom quartz_expr, only parsing).
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
      | Put e => fun s => let v := expr.interp (e s) in (v, Zmod.zero)
      | Bind _ a aC => fun s =>
          let '(s, v) := interp a s in
          interp (aC v) s
      | Cond e a b => fun s => if expr.interp (e s) then interp a s else interp b s
      | Upd i fv => fun s =>
          let i := expr.interp (i s) in
          let ms := typeWithHole.get s i in
          let (ms, v) := interp (fv s) ms in
          (typeWithHole.upd s i (fun _ => ms), v)
      end.
  End WithState.

  Declare Custom Entry quartz_action.
  Notation "quartz_action:( a )" := a (a custom quartz_action, only parsing).
  Notation "$ v" := v (in custom quartz_action at level 0, v constr at level 0, format "'$' v").
  Notation "x" := (x) (in custom quartz_action, x global, only parsing).
  Notation "f e" := (f e) (e custom quartz_expr, in custom quartz_action at level 10).
  Notation "f = v" := (UpdPut (C:=ltac2:(let (r, _) := typeWithHole.reify_field (pretype f) in exact $r)) tt v)
    (in custom quartz_action, f global, v custom quartz_expr, only parsing).
  Notation "'let' x '<-' a1 'in' a2"        := (Bind "$bind" a1 (fun x => a2))
    (in custom quartz_action at level 200, x constr at level 0, a1 custom quartz_action, a2 custom quartz_action).
  Notation "a1 ; a2" := (Seq a1 a2)
    (in custom quartz_action at level 1, right associativity, format "'[v' a1 ; '/' a2 ']'").
  Notation "this!" := (ltac:(match goal with x : @this _ _ |- _ => exact (Var x) || exact x end))
    (in custom quartz_action, only parsing).
  Notation "'return' e" := (Ret (fun _ => e))
    (in custom quartz_action at level 1, e custom quartz_expr).
End action.
Notation action := action.action (only parsing).

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
        flat.Ret (e, @flat.Const _ Unit Zmod.zero ))
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
    Local Notation VExpr := (VExpr (VId:=VId)).
    Context {gensym_state : Type} (gensym : gensym_state -> string -> VId * gensym_state).
    Let var (_ : type) := VId.

    Fixpoint const {t : type} : t -> VExpr :=
      match t return t -> VExpr with
      | Bool => fun v => VExprPriLiteral (VIntegralBinary (Some 1) (Z.b2z v))
      | Bits n => fun v =>
          VExprPriLiteral (
          (if Z.ltb n 8 return _->_->VIntegralNumber
            then VDecimalNumberB else VIntegralHex)
          (Some n) (Zmod.unsigned v))
      | _ => fun _ => ltac:(admit)
      end.

    Fixpoint lvalue (c : typeWithHole) (e : VExpr) : VExpr :=
      match c with
      | typeWithHole.HOLE => e
      | typeWithHole.Struct _ n c _ =>
        lvalue c (VExprHier e (VExprId (field_name n)))
      | _ => ltac:(admit)
      end.

    Definition unop {a b} (o : unop a b) : VExpr -> VExpr :=
      match o with
      | unop.IsZero => VExprUniOp VUniNot
      | unop.Not => VExprUniOp VUniNeg
      | unop.Opp => VExprUniOp VUniMinus
      | @unop.UnsignedResize n m => VExprCast (VExprPriLiteral (VDecimalNumberNB m))
      | @unop.SignedResize n m => fun e =>
        let e := VExprSystemTfCall VSystemTfSigned [e] in
        let e := VExprCast (VExprPriLiteral (VDecimalNumberNB m)) e in
        let e := VExprSystemTfCall VSystemTfUnsigned [e] in e
      end.

    Definition binop {a b c} (o : binop a b c) : VBinOp :=
      match o with
      | binop.EqBits => VBinEq
      | _ => ltac:(admit)
      end.

    Fixpoint expr {t} (e : expr var t) : VExpr :=
      match e with
      | Var x => VExprId x
      | Const c => const c
      | Cond c t f => VExprCond (@expr _ c) (@expr _ t) (@expr _ f)
      | Unop o e => unop o (@expr _ e)
      | Binop o a b => VExprBinOp (binop o) (@expr _ a) (@expr _ b)
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
Module fifo1. (* Example module *)
  Section WithElementType.
  Import typeWithHole expr action.
  Context {t : type}. (* Compile-time module parameter *)

  #[projections(primitive)]
  Record state := { len : bool; data : t }.

  (* Value method -- does not modiy, state can be used inside [expr] *)
  Definition peek {var} (s : this var (type.reify'' state)) : expr var t := quartz_expr:(
    this! at data).

  (* Action method -- modifies state, return Unit *)
  Definition enq {var} (d : var t) : action var (type.reify'' state) Unit := quartz_action:(
    len = true;
    data = #d).

  (* ActionValue method -- modifies state, returns a value *)
  Definition deq {var} : action var (type.reify'' state) t := quartz_action:(
    len = false;
    return this! at data).

  (* For specifications, compute the representation of native-record [state] *)
  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := struct.rep &v in exact $t).

  Import Datatypes type.

  (* Example specifications and proofs. Code can be symbolically evaluated by
   * reduction even if [t] is abstract. See [typeWithHole.Struct] and [get]. *)

  Lemma peek_ok (s : state) : expr.interp (peek (rep s)) = s.(data).
  Proof. trivial. Qed.

  Lemma enq_ok (s : state) x :
    action.interp (enq x) s = (rep {| len := true; data := x |}, tt ).
  Proof. trivial. Qed.

  Lemma deq_ok (s : state) :
    action.interp deq s = (rep {| len := false; data := s.(data) |}, s.(data) ).
  Proof. trivial. Qed.
  End WithElementType.
End fifo1.

Module Private_CompilationExample.
Require Import DecimalString.
Definition gensym_st : Type := list string * Z.
Definition gensym (st : gensym_st) (s : string) : string * gensym_st :=
  let (st, n) := st in
  if orb (String.eqb "" s) (List.existsb (String.eqb s) st)
  then let s := s ++ "$" ++ NilEmpty.string_of_int (Z.to_int n) in (s, (cons s st, n+1))
  else (s, (cons s st, n)).
Import VerilogSyntax expr action fifo1.
Local Notation "verilog_stmt:( t ')'" := t (t custom verilog_stmt).
Local Notation "$ x" := (x) (x constr at level 0, in custom verilog_expr at level 1).
Local Notation V := VExprId.
Compute let INPUT:="INPUT" in
  verilog.stmts id gensym (flatten.action (quartz_action:(
    enq INPUT;
    let x <- deq in
    return
      let v := peek this! in (* value method call *)
      #v == #x
  )) "STATE") (nil, 0) "STATE" "OUTPUT".
End Private_CompilationExample.

(* ...which in slightly less verbose concrete syntax gives:
tr -dc "[:alnum:]_ \n=$'."|sed s/verilog_stmt//g|sed s/VExprId//g|sed -e 's/\s\s*/ /g'|sed 's/\$ //g'|sed 's/V //g'
$aupd = STATE.len
$0 = STATE
$0.len = 1'b1
$Seq = 0'd0
$aupd$1 = $0.data
$2 = $0
$2.data = INPUT
$Seq$3 = 0'd0
$aupd$4 = $2.len
$5 = $2
$5.len = 1'b0
$Seq$6 = 0'd0
$bind = $5.data
$let = $5.data
STATE = $5
OUTPUT = $let == $bind
 *)

(* NEXT STEPS:
   - Flesh out nested-field and array-index access
   - Test (and likely finish up) method calls with nontrivial wrapper modules
   - Fill in remaining cases of translation to verilog
   - Print verilog abstract syntax as concrete syntax
     - Reference: https://github.com/Cherified/Guru/blob/main/PrettyPrinter/CodePrinter.hs
   - More notations (Binops, action let, ...)
     - Reference: https://github.com/mit-plv/bedrock2/blob/master/bedrock2/src/bedrock2/NotationsCustomEntry.v#L9
     - Reference: https://github.com/mit-plv/fiat2/blob/main/fiat2/src/fiat2/Notations.v#L158
     - Reference: VerilogSyntax.v
   - Investigate whether it's worth trying to generate fewer intermediate assignments
   - Prove compiler correctness
*)


Module Export more. Module type.
  Import type.
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
    all : subst; trivial; abstract congruence.
  Defined.

  Lemma eq_dec_refl t : eq_dec t t = left eq_refl.
  Proof.
    destruct eq_dec; [|contradiction].
    apply f_equal, Eqdep_dec.UIP_dec, type.eq_dec.
  Qed.
End type. End more.
