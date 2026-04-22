#[export] Set Primitive Projections.
From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
From Stdlib Require Import BinInt Bits.
From Stdlib Require Import String List.
From Stdlib Require Vector.
Import ListNotations.

From quartz.lang Require Import ident_to_string let_lift.

Open Scope Z_scope.

Module type.
  Local Set Boolean Equality Schemes.
  Inductive type :=
  | Bits (sz: Z)
  | Pair (_ _ : type)
  | Either (_ _ : type)
  | Struct (name : string) (_ : list (string * type))
  | Array (t: type) (sz: nat).
  Notation Unit := (Bits 0) (only parsing).
  Notation Bool := (Bits 1) (only parsing).

  Fixpoint interp t : Type :=
    match t with
    | Bits sz => bits sz
    | Pair a b => interp a * interp b
    | Either a b => interp a + interp b
    | Struct _ nts => fold_right (fun nt T => interp (snd nt) * T)%type unit nts
    | Array t n => Vector.t (interp t) n
    end.
  Definition interpfn a b := interp a -> interp b.

  Definition struct := list (string * type).
  Definition Struct_ : struct -> type := Struct "".
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
    | Bits sz => Zmod.zero
    | Pair a b => (default a, default b)
    | Either a b => inl (default a) (* TODO: confirm this *)
    | Struct _ s => default_struct default s
    | Array t n => default_array default t n
    end.

  Ltac2 Type exn ::= [ ReifyUnknown (constr) | InductiveNotAPrimitiveRecord (constr) ].
  Ltac2 rec reify t :=
    lazy_match! t with
    | type.interp ?t => t
    | bits ?n => constr:(type.Bits $n)
    | prod ?t1 ?t2 =>
        let rt1 := reify t1 in
        let rt2 := reify t2 in
        constr:(type.Pair $rt1 $rt2)
    | sum ?t1 ?t2 =>
        let rt1 := reify t1 in
        let rt2 := reify t2 in
        constr:(type.Either $rt1 $rt2)
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
      let basename := constr_string_of_ident (List.last (Env.path (Std.IndRef ind))) in
      constr:(type.Struct $basename $r)
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
        if b return Struct _ (nt::s) -> type.interp (if b then _ else _)
        then fst
        else fun v => get n (snd v)
    end.

  Fixpoint upd {s : struct} n : s -> (fieldType s n -> fieldType s n) -> s :=
    match s with
    | nil => fun s _ => s
    | cons nt s =>
        let b := String.eqb (fst nt) n in
        if b return let t := type.interp (if b then _ else _) in
                    Struct _ (nt::s) -> (t -> t) -> Struct _ (nt::s)
        then fun v f => (f (fst v), snd v)
        else fun v f => (fst v, @upd _ n (snd v) f)
    end.

  Definition put {s : struct} (n : string) (t : type) (sv : s) (v : fieldType s n) :=
    @upd s n sv (fun _ => v).

  Local Open Scope string_scope.
  Local Example get_ab_a : @get [("a", Bits 7); ("b", Bool)] "a" = fun r => fst r.
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.
  Local Example get_ab_b : @get [("a", Bits 7); ("b", Bool)] "b" = fun r => fst (snd r).
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.
  Local Example get_ab_c : @get [("a", Bits 7); ("b", Bool)] "c" = fun r => tt.
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.

  Ltac2 Type exn ::= [ RepUnknown (constr) ].
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
    | _ => Control.throw (RepUnknown (Constr.type v))
    end.
End struct.

Module Import Zmod.
  Coercion embed_bool (b : bool) : Zmod 2 := Zmod.of_Z _ (Z.b2z b).
  Coercion nonzero {m} (x : Zmod m) : bool := negb (Zmod.eqb x Zmod.zero).
  Lemma nonzero_bool (b : bool) : nonzero b = b :> bool. Proof. case b; trivial. Qed.
  Inductive Cases2 : Zmod 2 -> Prop :=
  | Cases2_0 : Cases2 (Zmod.mk 2 0 I) | Cases2_1 : Cases2 (Zmod.mk 2 1 I).
  Lemma cases2 (x : Zmod 2) : Cases2 x.
  Proof. destruct (Zmod.in_elements x ltac:(inversion 1)); intuition subst; constructor. Qed.
  Inductive BoolCases : Zmod 2 -> Prop :=
  | BoolTrue : BoolCases true | BoolFalse : BoolCases false.
  Lemma bool_cases (b : Zmod 2) : BoolCases b.
  Proof. destruct (Zmod.in_elements b ltac:(inversion 1)); intuition subst; constructor. Qed.
End Zmod.

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
  | Left {l r} : unop l (Either l r)
  | Right {l r} : unop r (Either l r)
  .

  Definition interp {a b} (op: unop a b) : type.interp a -> type.interp b :=
    match op in unop a b return a -> b with
    | IsZero => Zmod.eqb Zmod.zero
    | Not => Zmod.not
    | Opp => Zmod.opp
    | UnsignedResize => fun v => bits.of_Z _ (Zmod.unsigned v)
    | SignedResize => fun v => bits.of_Z _ (Zmod.signed v)
    | Left => inl
    | Right => inr
    end.
End unop.
Notation unop := unop.unop (only parsing).

Module binop.
  Inductive compare := cLt | cGt | cLe | cGe.

  Inductive binop : type -> type -> type -> Type :=
  | Add {n} : binop (Bits n) (Bits n) (Bits n)
  | Sub {n} : binop (Bits n) (Bits n) (Bits n)
  | And {n} : binop (Bits n) (Bits n) (Bits n)
  | Or {n} : binop (Bits n) (Bits n) (Bits n)
  | Slu {n m} : binop (Bits n) (Bits m) (Bits n)
  | Sru {n m} : binop (Bits n) (Bits m) (Bits n)
  | Srs {n m} : binop (Bits n) (Bits m) (Bits n)
  | Mul {n m z} : binop (Bits n) (Bits m) (Bits z) 
  | EqBits {n} : binop (Bits n) (Bits n) Bool
  | Compare (signed: bool) (c: compare) {n} : binop (Bits n) (Bits n) Bool
  | MkPair {a b: type} : binop a b (Pair a b).

  Definition interp {a b c} (op: binop a b c) : a -> b -> c :=
    match op in binop a b c return a -> b -> c with
    | Add => Zmod.add
    | Sub => Zmod.sub
    | And => Zmod.and
    | Or => Zmod.or
    | Slu => fun a b => Zmod.slu a (Zmod.unsigned b)
    | Sru => fun a b => Zmod.sru a (Zmod.unsigned b)
    | Srs => fun a b => Zmod.srs a (Zmod.unsigned b)
    | @Mul _ _ z => fun a b => Zmod.of_Z (2^z) (Zmod.unsigned a * Zmod.unsigned b)
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
  | Struct (sn : string) (l : struct) (n : string) (t : typeWithHole) (r : struct)
     {NoDup_by_fun_eq_refl : forall t, struct.fieldType (l ++ (n, t) :: r) n = t}
  | Array (sz : nat) (t : typeWithHole) (index_width : Z).

  Fixpoint plug (C : typeWithHole) (t : type) : type :=
    match C with
    | HOLE => t
    | PairL t1 t2 => type.Pair (plug t1 t) t2
    | PairR t1 t2 => type.Pair t1 (plug t2 t)
    | Struct sn l n C r => type.Struct sn (l ++ cons (n, plug C t) r)
    | Array sz t' _ => type.Array (plug t' t) sz
    end.

  Fixpoint indices (t : typeWithHole) : type :=
    match t with
    | HOLE => Unit
    | PairL t _ | PairR _ t | Struct _ _ _ t _ => indices t
    | Array sz t n => Pair (Bits n) (indices t)
    end.

  Fixpoint get C : forall t, plug C t -> indices C -> t :=
    match C return forall t, plug C t -> indices C -> t with
    | HOLE => fun t r i => r
    | PairL a b => fun _ r i => get a _ (fst r) i
    | PairR a b => fun _ r i => get b _ (snd r) i
    | @Struct _ _ n t _ pf => fun _ r i => get t _ (eq_rect _ _ (struct.get n r) _ (pf _)) i
    | Array sz t _ => fun _ r i => get t _
        (List.nth_default (default _) (Vector.to_list r) (Z.to_nat (Zmod.unsigned (fst i)))) (snd i)
    end.
  Arguments get {_ _}.

  Fixpoint upd C : forall t, plug C t -> indices C -> (t -> t) -> plug C t :=
    match C return forall t, plug C t -> indices C -> (t -> t) -> plug C t with
    | HOLE => fun t r i f => f r
    | PairL a b => fun _ r i f => (upd a _ (fst r) i f, snd r)
    | PairR a b => fun _ r i f => (fst r, upd b _ (snd r) i f)
    | @Struct _ _ n t _ pf => fun _ r i f =>
        struct.upd n r (eq_rect (plug t _) (fun u => u -> u) (fun v => upd t _ v i f) _ (eq_sym (pf _)))
    | Array sz t _ => fun _ r i f =>
        Vector.upd r (Z.to_nat (Zmod.unsigned (fst i))) (fun r => upd _ _ r (snd i) f)
    end.
  Arguments upd {_ _}.

  Ltac2 Type exn ::= [ ReifyFieldUnknown (constr) ].
  Ltac2 reify_field p0c :=
    match UConstr.kind p0c with
    | UConstr.Constant c0 inst =>
      match Proj.of_constant c0 with
      | Some p0 =>
        lazy_match! type.reify (UConstr.make (UConstr.Ind (Proj.ind p0) inst)) with
        | type.Struct ?sn ?rs =>
    let rec firstn n l := if Int.le n 0
      then lazy_match! l with nil => l | @cons ?t _ _ => constr:(@nil $t) end
      else lazy_match! l with @cons ?t ?x ?l => let l := firstn (Int.sub n 1) l in constr:(@cons $t $x $l) end in
    let rec skipn n l := if Int.le n 0 then l else lazy_match! l with cons _ ?l => skipn (Int.sub n 1) l end in
    let hd l := lazy_match! l with @nil _ => l | @cons _ ?x _ => x end in
          let l := firstn (Proj.index p0) rs in
          let (n, t) := lazy_match! hd (skipn (Proj.index p0) rs) with (?n, ?t) => (n, t) end in
          let r := skipn (Int.add 1 (Proj.index p0)) rs in
          (constr:(@Struct $sn $l $n HOLE $r (fun _ => eq_refl)), t)
        | _ => Control.throw (ReifyFieldUnknown p0c)
        end
      | _ => Control.throw (ReifyFieldUnknown p0c)
      end
    | _ => Control.throw (ReifyFieldUnknown p0c)
    end.
End typeWithHole.
Notation typeWithHole :=typeWithHole.typeWithHole (only parsing).

Coercion typeWithHole.plug : typeWithHole >-> Funclass.
Coercion typeWithHole.indices : typeWithHole >-> type.

Module expr.
  Section WithSubstitutionType.
    Context {var : type -> Type}.
    Context {fn : type -> type -> Type}.

    Inductive expr {t : type} : Type :=
    | Const (c : type.interp t)
    | Var (x : var t)
    | Get (C : typeWithHole) (r : @expr (C t)) (i : @expr C)
    | Unop {t1 : type} (op : unop t1 t) (e1 : @expr t1)
    | Binop {t1 t2 : type} (op : binop t1 t2 t) (e1 : @expr t1) (e2 : @expr t2)
    | If (_ : @expr Bool) (a b : @expr t)
    | Call {a} (_ : fn a t) (_ : @expr a).

    Definition tt := @Const Unit Zmod.zero.
    Definition true := @Const Bool true.
    Definition false := @Const Bool false.
    Definition zero {n} := @Const (Bits n) Zmod.zero.
  End WithSubstitutionType.
  Arguments expr : clear implicits.

  Fixpoint interp {t} (e : expr type.interp type.interpfn t) : type.interp t :=
    match e return type.interp t with
    | Const c => c
    | Var x => x
    | Get _ r i => typeWithHole.get (interp r) (interp i)
    | Unop op e1 => unop.interp op (interp e1)
    | Binop op e1 e2 => binop.interp op (interp e1) (interp e2)
    | If e a b => if interp e : bool then interp a else interp b
    | Call f e => f (interp e)
    end.

  Declare Custom Entry quartz_expr.
  Notation "quartz_expr:( e )" := e (e custom quartz_expr, only parsing).

  Notation "( e )" := e (in custom quartz_expr, e custom quartz_expr at level 200).
  Notation "# v" := (expr.Var v) (in custom quartz_expr at level 0, v constr at level 0, format "'#' v").
  Notation "$ v" := v (in custom quartz_expr at level 0, v constr at level 0, format "'$' v").
  (* Notation "x" := (x) (in custom quartz_expr at level 0, x global). *)
  Notation "sz ''d' val" := (expr.Const (t:=Bits sz) (Zmod.of_Z _ val))
    (in custom quartz_expr at level 0, sz constr at level 0, val constr at level 0, format "sz ''d' val").
  Notation "'const' c" := (expr.Const c) (in custom quartz_expr at level 0, c constr at level 0).
  Notation "f '(' e ')'" := (expr.Call f e)
    (in custom quartz_expr at level 0, left associativity, f global, e custom quartz_expr at level 200).
  Notation "r '..' f" := (expr.Get (ltac2:(let (c, _) := typeWithHole.reify_field (pretype f) in exact $c)) r expr.tt)
    (in custom quartz_expr at level 1, left associativity, f global, r custom quartz_expr, only parsing).
  Notation "r '[' i ']'" :=
    (expr.Get (typeWithHole.Array _ typeWithHole.HOLE _) r (expr.Binop binop.MkPair i expr.tt))
    (in custom quartz_expr at level 1, left associativity, i custom quartz_expr at level 200).
  Notation "p '.1'" := (expr.Get (typeWithHole.PairL typeWithHole.HOLE _) p expr.tt)
    (in custom quartz_expr at level 1, left associativity).
  Notation "p '.2'" := (expr.Get (typeWithHole.PairR _ typeWithHole.HOLE) p expr.tt)
    (in custom quartz_expr at level 1, left associativity).
  Notation "r .[ C , i ]" := (expr.Get C r i)
    (in custom quartz_expr at level 1, left associativity, C constr at level 0, i custom quartz_expr at level 200, format "r .[ C ,  i ]").

  Notation "'tt'" := (expr.tt) (in custom quartz_expr at level 0).
  Notation "'false'" := (expr.false) (in custom quartz_expr at level 0).
  Notation "'true'" := (expr.true) (in custom quartz_expr at level 0).
  Notation "- e" := (expr.Unop unop.Opp e) (in custom quartz_expr at level 35, right associativity).
  Notation "! e" := (expr.Unop unop.IsZero e) (in custom quartz_expr at level 35, right associativity).
  Notation "~ e" := (expr.Unop unop.Not e) (in custom quartz_expr at level 35, right associativity).
  Notation "'left' e" := (expr.Unop unop.Left e) (in custom quartz_expr at level 10, right associativity).
  Notation "'right' e" := (expr.Unop unop.Right e) (in custom quartz_expr at level 10, right associativity).

  Notation "'(' x ',' y ',' .. ',' z ')'" :=
    (expr.Binop (@binop.MkPair _ _) .. (expr.Binop (@binop.MkPair _ _) x y) .. z)
    (in custom quartz_expr at level 0, x custom quartz_expr at level 200,
     y custom quartz_expr at level 200, z custom quartz_expr at level 200,
     format "( '[' x , '/' y , '/' .. , '/' z ']' )").
  Notation "e1 * e2" := (expr.Binop binop.And e1 e2) (in custom quartz_expr at level 39, left associativity).
  Notation "e1 & e2" := (expr.Binop binop.And e1 e2) (in custom quartz_expr at level 40, left associativity).
  Notation "e1 + e2" := (expr.Binop binop.Add e1 e2) (in custom quartz_expr at level 50, left associativity).
  Notation "e1 - e2" := (expr.Binop binop.Add e1 e2) (in custom quartz_expr at level 50, left associativity).
  Notation "e1 | e2" := (expr.Binop binop.Or e1 e2) (in custom quartz_expr at level 50, left associativity).
  Notation "e1 << e2" := (expr.Binop binop.Slu e1 e2) (in custom quartz_expr at level 60, left associativity).
  Notation "e1 >> e2" := (expr.Binop binop.Sru e1 e2) (in custom quartz_expr at level 60, left associativity).
  Notation "e1 .>> e2" := (expr.Binop binop.Srs e1 e2) (in custom quartz_expr at level 60, left associativity).

  Notation "e1 == e2" := (expr.Binop binop.EqBits e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 < e2" := (expr.Binop (binop.Compare Datatypes.false binop.cLt) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 <= e2" := (expr.Binop (binop.Compare Datatypes.false binop.cLe) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 > e2" := (expr.Binop (binop.Compare Datatypes.false binop.cGt) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 >= e2" := (expr.Binop (binop.Compare Datatypes.false binop.cGe) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 .< e2" := (expr.Binop (binop.Compare Datatypes.true binop.cLt) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 .<= e2" := (expr.Binop (binop.Compare Datatypes.true binop.cLe) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 .> e2" := (expr.Binop (binop.Compare Datatypes.true binop.cGt) e1 e2) (in custom quartz_expr at level 70, no associativity).
  Notation "e1 .>= e2" := (expr.Binop (binop.Compare Datatypes.true binop.cGe) e1 e2) (in custom quartz_expr at level 70, no associativity).

  Notation "'if' cond 'then' a 'else' b" := (expr.If cond a b)
    (in custom quartz_expr at level 200, cond custom quartz_expr at level 200, a custom quartz_expr at level 200, b custom quartz_expr at level 200).
End expr.
Notation expr := expr.expr.

Module eexpr. (* extended expressions = purely functional "function" bodies *)
  Import expr.
  Section WithSubstitutionType.
    Context {var : type -> Type}.
    Context {fn : type -> type -> Type}.
    Local Notation expr := (@expr.expr var fn).

    Inductive eexpr : type -> Type :=
    | Ret {t} (e : expr t) : eexpr t
    | Let (name_hint : string) {tx} (a : expr tx) {t} (aC : var tx -> eexpr t) : eexpr t
    | Bind (name_hint : string) {tx} (a : eexpr tx) {t} (aC : var tx -> eexpr t) : eexpr t
    | If {t} (_ : expr Bool) (a b : eexpr t) : eexpr t
    | Case {l r} (_ : expr (Either l r)) {t} (l : var l -> eexpr t) (r : var r -> eexpr t) : eexpr t
    | Upd {C : typeWithHole} (i : expr C) {t} (s := C t) (es : expr s) (v : expr t) : eexpr s.
  End WithSubstitutionType.
  Coercion Ret : expr >-> eexpr.
  Arguments eexpr : clear implicits.

  Fixpoint interp {t} (e: eexpr type.interp type.interpfn t) : t :=
    match e in eexpr _ _ t return t with
    | Ret e => expr.interp e
    | Let _ a b => let x := expr.interp a in interp (b x)
    | Bind _ a b => let x := interp a in interp (b x)
    | If e a b => if expr.interp e : bool then interp a else interp b
    | Case e l r => match expr.interp e with inl v => interp (l v) | inr v => interp (r v) end
    | Upd i s v => typeWithHole.upd (expr.interp s) (expr.interp i) (fun _ => expr.interp v)
    end.

  Declare Custom Entry quartz_eexpr.
  Notation "quartz_eexpr:( e )" := e (e custom quartz_eexpr, only parsing).

  Notation "( e )" := e (in custom quartz_eexpr, e custom quartz_eexpr at level 200).
  Notation "$ v" := v (in custom quartz_eexpr at level 0, v constr at level 0, format "'$' v").
  Notation "x" := (x) (in custom quartz_eexpr at level 0, x global).
  Notation "'return' e" := (eexpr.Ret e)
    (in custom quartz_eexpr at level 200, e custom quartz_expr at level 200).
  Notation "'let' x ':=' a 'in' b" := (eexpr.Let "Let" a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, a custom quartz_expr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'let' x : t ':=' a 'in' b" := (eexpr.Let (tx:=t) "Let" a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, t constr at level 200, a custom quartz_expr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'let' x '<-' a 'in' b" := (eexpr.Bind "Bind" a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, a custom quartz_eexpr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'let' x : t '<-' a 'in' b" := (eexpr.Bind (tx := t) "Bind" a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, t constr at level 200, a custom quartz_eexpr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'if' cond 'then' a 'else' b" := (eexpr.If cond a b)
    (in custom quartz_eexpr at level 200, cond custom quartz_expr at level 200, a custom quartz_eexpr at level 200, b custom quartz_eexpr at level 200).
  Notation "'match' cond 'with' | 'left' l '=>' a | 'right' r '=>' b 'end'" := (eexpr.Case cond (fun l => a) (fun r => b))
    (in custom quartz_eexpr at level 200, cond custom quartz_expr at level 200, l name, a custom quartz_eexpr at level 200, r name, b custom quartz_eexpr at level 200).
  Notation "s '..' f '=' v" := (eexpr.Upd (C:=ltac2:(let (c, _) := typeWithHole.reify_field (pretype f) in exact $c)) expr.tt s v)
    (in custom quartz_eexpr at level 200, f global, s custom quartz_expr at level 0, v custom quartz_expr at level 200).
  Notation "s '[' i ']' '=' v" :=
    (eexpr.Upd (C:=typeWithHole.Array _ typeWithHole.HOLE _) (expr.Binop binop.MkPair i expr.tt) s v)
    (in custom quartz_eexpr at level 200, s custom quartz_expr at level 0, i custom quartz_expr at level 200, v custom quartz_expr at level 200).
  Notation "s .[ C , i ] '=' v" := (eexpr.Upd (C:=C) i s v)
    (in custom quartz_eexpr at level 200, s custom quartz_expr at level 0, C constr at level 0, i custom quartz_expr at level 200, v custom quartz_expr at level 200).
End eexpr.
Notation eexpr := eexpr.eexpr (only parsing).

Module fn.
  Import expr eexpr.
  Section WithSubstitutionType.
    Context {var : type -> Type}.
    Inductive fn {a b} := Fn { body : var a -> eexpr var (@fn) b }.
  End WithSubstitutionType.
  Arguments Fn {_ _ _}.
  #[global] Add Printing Constructor fn.
  Arguments fn : clear implicits.

  Section WithF.
  Context {var : type -> Type} {fn1 fn2} (f : forall a b : type, fn1 a b -> fn2 a b).
  Fixpoint expr_map_fn {t} (e : expr var fn1 t) : expr var fn2 t :=
    match e with
    | Const c => Const c
    | Var x => Var x
    | Get C r i => Get C (@expr_map_fn _ r) (@expr_map_fn _ i)
    | Unop op e => Unop op (@expr_map_fn _ e)
    | Binop op e1 e2 => Binop op (@expr_map_fn _ e1) (@expr_map_fn _ e2)
    | expr.If e a b => expr.If (@expr_map_fn _ e) (@expr_map_fn _ a) (@expr_map_fn _ b)
    | Call fn a => Call (f _ _ fn) (@expr_map_fn _ a)
    end.
  Fixpoint eexpr_map_fn {t} (e : eexpr var fn1 t) { struct e} : eexpr var fn2 t :=
    match e with
    | eexpr.Ret e => eexpr.Ret (expr_map_fn e)
    | eexpr.Let x e C => eexpr.Let x (expr_map_fn e) (fun v => @eexpr_map_fn _ (C v))
    | eexpr.Bind x e C => eexpr.Bind x (@eexpr_map_fn _ e) (fun v => @eexpr_map_fn _ (C v))
    | If e a b => If (expr_map_fn e) (@eexpr_map_fn _ a) (@eexpr_map_fn _ b)
    | Case e a b => Case (expr_map_fn e) (fun l => @eexpr_map_fn _ (a l)) (fun r => @eexpr_map_fn _ (b r))
    | Upd i s v => Upd (@expr_map_fn _ i) (@expr_map_fn _ s) (@expr_map_fn _ v)
    end.
  End WithF.

  Fixpoint interp {a b} (f : fn type.interp a b) {struct f} : type.interp a -> type.interp b :=
     fun v => eexpr.interp (eexpr_map_fn (@interp) (f.(body) v)).

  Ltac2 let_lift_fns e := let_lift_constants (fun c i =>
    lazy_match! Constr.type (UConstr.make (UConstr.Constant c i)) with
    | context[@fn.fn] => true
    | _ => false
    end) e.

  Module Private_example_global_fn.
    Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x => quartz_eexpr:(
      return ( #x + 8 'd 1 ))).
    Definition pred {var} : fn var (Bits 8) (Bits 8) := Fn (fun y => quartz_eexpr:(
      let _u := succ ($(expr.Unop unop.UnsignedResize (expr.Var y)) ) in
      return ( #y + 8 'd (-1) ))).
    Definition cycle {var} := Fn (var:=var) (fun z => quartz_eexpr:(
      let r := pred ( succ ( #z ) ) in return #r)).
    Lemma interp_cycle : interp cycle = fun z => (z + bits.of_Z _ 1 + bits.of_Z _ (-1))%Zmod.
    Proof.
      cbn [cycle            interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp].
      (* = (fun v : Bits 8 => interp pred (interp succ v)) *)
      cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp].
      (* = RHS *)
      trivial.
    Qed.
    Lemma ok_cycle z : interp cycle z = z.
    Proof. rewrite interp_cycle, <-Zmod.add_assoc, (Zmod.of_Z_opp 1), Zmod.add_0_r; trivial. Qed.
  End Private_example_global_fn.

  Module Private_example_global_polyfn. (* polymorphic functions can't be packaged yet *)
    Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x => quartz_eexpr:(
      return ( #x + 8 'd 1 ))).
    Definition pred {var} {n} : fn var (Bits n) (Bits n) := Fn (fun y => quartz_eexpr:(
      let _u := succ ($(expr.Unop unop.UnsignedResize (expr.Var y)) ) in
      return ( #y + _ 'd (-1) ))).
    Definition cycle {var} := Fn (var:=var) (fun z => quartz_eexpr:(
      let r := pred ( succ ( #z ) ) in return #r)).
    Lemma interp_cycle : interp cycle = fun z => (z + bits.of_Z _ 1 + bits.of_Z _ (-1))%Zmod.
    Proof. cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp]. trivial. Qed.
    Lemma ok_cycle z : interp cycle z = z.
    Proof. rewrite interp_cycle, <-Zmod.add_assoc, (Zmod.of_Z_opp 1), Zmod.add_0_r; trivial. Qed.
  End Private_example_global_polyfn.
End fn.

Module fns. (* deeply embedded environments of functions *)
  Import expr eexpr.
  Section WithSubstitutionType.
    Context {var : type -> Type}.
    Context {fn : type -> type -> Type}.
    Inductive fns {a b} :=
    | Let {a b} (func_name_hint arg_name_hint : string) (f : var a -> eexpr var fn b) (_ : fn a b -> fns)
    | Ret (func_name_hint arg_name_hint : string) (_ : var a -> eexpr var fn b).
  End WithSubstitutionType.
  Arguments fns : clear implicits.

  Fixpoint interp {a b} (fs : fns type.interp type.interpfn a b) : a -> b :=
    match fs with
    | Let _ _ f C => let f := fun a => eexpr.interp (f a) in interp (C f)
    | Ret _ _ f => fun a => eexpr.interp (f a)
    end.

    Import Printf.

  Local Ltac2 rec rdelta (x : constr) : constr :=
    let oref := match Unsafe.kind x with
                | Unsafe.Constant cst _ => Some (Std.ConstRef cst)
                | Unsafe.Var id => Some (Std.VarRef id)
                | _ => None
                end in
    match oref with | None => x | Some ref =>
    let x' := eval cbv delta [$ref] in $x in
    if Constr.equal x x' then x
    else rdelta x' end.

  Ltac2 package_global_fns var fn e :=
    let tga := lazy_match! Constr.type e with forall var, fn.fn var ?a ?b => a end in
    let tgb := lazy_match! Constr.type e with forall var, fn.fn var ?a ?b => b end in
    let e := rdelta e in
    let e := eval cbv beta iota in ($e $var) in
    let oldfn := constr:(fn.fn $var) in
    let fnLet := constr:(@Let $var $fn $tga $tgb) in
    let fnRet := constr:(@Ret $var $fn $tga $tgb) in
    let rec app_lets (e : constr) (a : constr) : constr :=
      match UConstr.kind e with
      | UConstr.LetIn bf e c =>
        match UConstr.kind e with
        | UConstr.Lambda bv e =>
          let e := UConstr.substnl [a] 0 e in
          let lm := UConstr.make (UConstr.Lambda bv (UConstr.make (UConstr.Rel 2))) in
          let c := UConstr.substnl [lm] 0 (UConstr.liftn 1 2 c) in
          UConstr.make (UConstr.LetIn bf e (app_lets c a))
        | _ =>
          UConstr.make (UConstr.LetIn bf e (app_lets c a))
        end
      | _ => printf "UNRECOGNIZED %t" e; e
    end in
    let e := fn.let_lift_fns e in
    let e := app_lets e var in
    let rec replace_fn (e : constr) :=
      if Constr.equal e oldfn
      then fn else
      UConstr.map replace_fn e in
    let binder_name (b : binder) := match Binder.name b with
      | Some id => constr_string_of_ident id | None => constr:(""%string) end in
    let lambda_name (body_constr : constr) := match UConstr.kind body_constr with
      | UConstr.Lambda lb _ => binder_name lb | _ => constr:(""%string) end in
    let rec shallow_reify (e : constr) :=
      match UConstr.kind e with
      | UConstr.LetIn b body c =>
        match Constr.decompose_app_list body with
        | (f, [var'; ta; t; body]) =>
          if Bool.neg (Constr.equal f constr:(@fn.Fn)) then e else
          if Bool.neg (Constr.equal var' var) then e else
          let bt := UConstr.make (UConstr.App fn [|ta;t|]) in
          let b := Constr.Binder.unsafe_make (Binder.name b) (Binder.relevance b) bt in
          let c := UConstr.make (UConstr.Lambda b (shallow_reify c)) in
          UConstr.make (UConstr.App fnLet [|ta; t; binder_name b; lambda_name body; replace_fn body; c|])
        | _ => e
        end
      | _ =>
        match Constr.decompose_app_list e with
        | (f, [var'; ta; t; body]) =>
           if Bool.neg (Constr.equal f constr:(@fn.Fn)) then e else
           if Bool.neg (Constr.equal var' var) then e else
           let cycle := constr:("cycle"%string) in (* TODO *)
           UConstr.make (UConstr.App fnRet [|cycle; lambda_name body; replace_fn body|])
        | _ => printf "UNRECOGNIZED %t" e; e
        end
    end in
    shallow_reify e.

  Module Private_example_wholeprogramdef.
    Local Open Scope string_scope.
    Definition packaged_cycle {var fn} : fns _ _ _ _ := ltac2:(
      let e := package_global_fns &var &fn constr:(@fn.Private_example_global_fn.cycle) in exact $e).
    Lemma packaged_ok : interp packaged_cycle = fn.interp fn.Private_example_global_fn.cycle.
    Proof. cbn beta iota delta [interp packaged_cycle]. trivial. Qed.
  End Private_example_wholeprogramdef.
End fns.
Local Notation fns := fns.fns (only parsing).

From Stdlib Require Import DecimalString List.

Module sv.
  Local Open Scope bool_scope. Local Open Scope string_scope.
  Definition var (t : type) := string.
  Definition fn (a b : type) := string.

  Definition pp_Z (n : Z) : string := NilZero.string_of_int (Z.to_int n).
  Definition pp_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).
  Definition LF := "
".

  Fixpoint pp_type (t : type) : string :=
    match t with
    | type.Unit => "unit"
    | type.Bits sz => "bit["++pp_Z (sz - 1)++":0]"
    | type.Pair a b => "Pair#("++pp_type a++", "++pp_type b++")::t"
    | type.Either a b => "Either#("++pp_type a++", "++pp_type b++")::t"
    | type.Struct name _ => name
    | type.Array t sz => pp_type t++"["++pp_nat sz++"-1:0]"
    end.

  Definition pp_struct nts :=
    "struct packed { "++ fold_right (fun '(n, t') acc => pp_type t'++" "++n++"; "++acc) "" nts++ "}".

  Definition pp_typedef name nts := "typedef "++pp_struct nts++" "++name++";"++LF.

  Fixpoint pp_typedefs (ts : list type) : string :=
    match ts with
    | nil => ""
    | type.Struct n nts :: ts => pp_typedef n nts ++ pp_typedefs ts
    | _ :: ts => pp_typedefs ts
    end.

  Fixpoint pp_const {t : type} : type.interp t -> string :=
    match t return type.interp t -> string with
    | type.Unit => fun b => "tt"
    | type.Bits sz => fun v => pp_Z sz++"'d"++pp_Z (Zmod.unsigned v)
    | type.Pair a b => fun p =>
        "Pair#("++pp_type a++", "++pp_type b++")::mk("++
        @pp_const a (fst p)++", "++@pp_const b (snd p)++")"
    | type.Either a b => fun e =>
        match e with
        | inl v => "Either#("++pp_type a++", "++pp_type b++")::left("++@pp_const a v++")"
        | inr v => "Either#("++pp_type a++", "++pp_type b++")::right("++@pp_const b v++")"
        end
    | type.Struct _ nts =>
        let fix pp_struct_val (fs : list (string * type))
          : fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs -> string :=
          match fs return fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs -> string with
          | nil => fun _ => ""
          | cons (n, t') rest => fun v =>
              let val_str := @pp_const t' (fst v) in
              let rest_str := pp_struct_val rest (snd v) in
              "."++n++"("++val_str++")" ++
              (if match rest with nil => true | _ => false end then "" else ", ") ++
              rest_str
          end
        in fun s => "'{ "++pp_struct_val nts s++" }"
    | type.Array t' sz =>
        let fix pp_vec {n} (v : Vector.t (type.interp t') n) : string :=
          match v in Vector.t _ n return string with
          | Vector.nil _ => ""
          | Vector.cons _ hd 0 tl => @pp_const t' hd
          | Vector.cons _ hd (S n') tl => @pp_const t' hd++", "++pp_vec tl
          end
        in fun v => "'{"++pp_vec v++"}"
    end.

  Fixpoint pp_hole_upd (C : typeWithHole) (base : string) (idx : string) : string :=
    match C with
    | typeWithHole.HOLE => base
    | typeWithHole.PairL t1 _ => pp_hole_upd t1 (base ++ ".fst") idx
    | typeWithHole.PairR _ t2 => pp_hole_upd t2 (base ++ ".snd") idx
    | typeWithHole.Struct _ _ n t _ => pp_hole_upd t (base ++ "." ++ n) idx
    | typeWithHole.Array _ t _ => pp_hole_upd t (base ++ "[" ++ idx ++ ".fst]") (idx ++ ".snd")
    end.

  Fixpoint pp_hole_get (t_hole : type) (C : typeWithHole) (base : string) (idx : string) : string :=
    match C with
    | typeWithHole.HOLE => base
    | typeWithHole.PairL t1 t2 =>
        let T1 := typeWithHole.plug t1 t_hole in
        pp_hole_get t_hole t1 ("Pair#(" ++ pp_type T1 ++ ", " ++ pp_type t2 ++ ")::fst(" ++ base ++ ")") idx
    | typeWithHole.PairR t1 t2 =>
        let T2 := typeWithHole.plug t2 t_hole in
        pp_hole_get t_hole t2 ("Pair#(" ++ pp_type t1 ++ ", " ++ pp_type T2 ++ ")::snd(" ++ base ++ ")") idx
    | typeWithHole.Struct _ _ n t _ =>
        pp_hole_get t_hole t (base ++ "." ++ n) idx
    | typeWithHole.Array _ t _ =>
        pp_hole_get t_hole t (base ++ "[" ++ idx ++ ".fst]") (idx ++ ".snd")
    end.

  Definition pp_unop {t1 t2} (op : unop t1 t2) (e1_str : string) : string :=
    match op with
    | @unop.IsZero n => "("++e1_str++" == 0)"
    | @unop.Not n => "(~"++e1_str++")"
    | @unop.Opp n => "(-"++e1_str++")"
    | @unop.UnsignedResize n m => pp_Z m ++ "'($unsigned("++e1_str++"))"
    | @unop.SignedResize n m => "$unsigned(" ++ pp_Z m ++ "'($signed("++e1_str++")))"
    | @unop.Left l r => "Either#("++pp_type l++", "++pp_type r++")::left("++e1_str++")"
    | @unop.Right l r => "Either#("++pp_type l++", "++pp_type r++")::right("++e1_str++")"
    end.

  Definition pp_binop {t1 t2 t3} (op : binop t1 t2 t3) (e1_str e2_str : string) : string :=
    match op with
    | @binop.Add n => "("++e1_str++" + "++e2_str++")"
    | @binop.Sub n => "("++e1_str++" - "++e2_str++")"
    | @binop.And n => "("++e1_str++" & "++e2_str++")"
    | @binop.Or n => "("++e1_str++" | "++e2_str++")"
    | @binop.Slu n m => "("++e1_str++" << "++e2_str++")"
    | @binop.Sru n m => "("++e1_str++" >> "++e2_str++")"
    | @binop.Srs n m => "$unsigned(($signed("++e1_str++") >>> "++e2_str++"))"
    | @binop.EqBits n => "("++e1_str++" == "++e2_str++")"
    | @binop.Mul n m z => pp_Z m ++ "'($unsigned(" ++e1_str++" * "++e2_str++"))" (* TODO: is truncation needed? *)
    | @binop.Compare signed c n =>
        let op_str := match c with
          | binop.cLt => "<" | binop.cGt => ">"
          | binop.cLe => "<=" | binop.cGe => ">="
        end in
        let e1_s := if signed then "$signed("++e1_str++")" else e1_str in
        let e2_s := if signed then "$signed("++e2_str++")" else e2_str in
        "("++e1_s++" "++op_str++" "++e2_s++")"
    | @binop.MkPair a b => "Pair#("++pp_type a++", "++pp_type b++")::mk("++e1_str++", "++e2_str++")"
    end.

  Fixpoint pp_expr {t} (e : expr.expr var fn t) : string :=
    match e with
    | expr.Const c => pp_const c
    | expr.Var x => x
    | @expr.Get _ _ _ C r i => pp_hole_get t C (pp_expr r) (pp_expr i)
    | expr.Unop op e1 => pp_unop op (pp_expr e1)
    | expr.Binop op e1 e2 => pp_binop op (pp_expr e1) (pp_expr e2)
    | expr.If cond a b => "("++pp_expr cond++" ? "++pp_expr a++" : "++pp_expr b++")"
    | expr.Call f e1 => f++"("++pp_expr e1++")"
    end.

    Fixpoint pp_eexpr {t} (ind : string) (e : eexpr.eexpr var fn t) (out_var : string) (id : nat) : string * nat :=
    match e with
    | @eexpr.Ret _ _ _ exp => (ind ++ out_var ++ " = " ++ pp_expr exp ++ ";", id)
    | @eexpr.Let _ _ name_hint tx a _ aC =>
        let vname := name_hint ++ "_" ++ pp_nat id in
        let stmt1 := ind ++ pp_type tx ++ " " ++ vname ++ " = " ++ pp_expr a ++ ";" in
        let '(stmt2, id') := pp_eexpr ind (aC vname) out_var (S id) in
        (stmt1 ++ ""++LF ++ stmt2, id')
    | @eexpr.Bind _ _ name_hint tx a _ aC =>
        let vname := name_hint ++ "_" ++ pp_nat id in
        let stmt_decl := ind ++ "begin " ++ pp_type tx ++ " " ++ vname ++ ";" in
        let '(stmt1, id1) := pp_eexpr ind a vname (S id) in
        let '(stmt2, id2) := pp_eexpr ind (aC vname) out_var id1 in
        (stmt_decl ++ ""++LF ++ stmt1 ++ ""++LF ++ stmt2 ++ " end", id2)
    | @eexpr.If _ _ _ cond a b =>
        let ind_nested := ind ++ "  " in
        let '(stmt_a, id1) := pp_eexpr ind_nested a out_var id in
        let '(stmt_b, id2) := pp_eexpr ind_nested b out_var id1 in
        (ind ++ "if (" ++ pp_expr cond ++ ") begin"++LF ++
         stmt_a ++ ""++LF ++
         ind ++ "end else begin"++LF ++
         stmt_b ++ ""++LF ++
         ind ++ "end", id2)
    | @eexpr.Case _ _ l_t r_t cond _ l_branch r_branch =>
        let l_var := "left_" ++ pp_nat id in
        let r_var := "right_" ++ pp_nat id in
        let ind_case := ind ++ "  " in
        let ind_nested := ind_case ++ "  " in
        let '(stmt_l, id1) := pp_eexpr ind_nested (l_branch l_var) out_var (S id) in
        let '(stmt_r, id2) := pp_eexpr ind_nested (r_branch r_var) out_var id1 in
        (ind ++ "case (" ++ pp_expr cond ++ ") matches"++LF ++
         ind_case ++ "tagged left ." ++ l_var ++ " : begin"++LF ++
         stmt_l ++ ""++LF ++
         ind_case ++ "end"++LF ++
         ind_case ++ "tagged right ." ++ r_var ++ " : begin"++LF ++
         stmt_r ++ ""++LF ++
         ind_case ++ "end"++LF ++
         ind ++ "endcase", id2)
    | @eexpr.Upd _ _ C i _ es v =>
        (ind ++ out_var ++ " = " ++ pp_expr es ++ ";"++LF ++ ind ++
         pp_hole_upd C out_var (pp_expr i) ++ " = " ++ pp_expr v ++ ";", id)
    end.

  Definition pp_fn {a b} (fname argname : string) (fn_body : var a -> eexpr.eexpr var fn b) : string :=
    "function automatic " ++ pp_type b ++ " " ++ fname ++ " ("++LF++
    "  input " ++ pp_type a ++ " " ++ argname ++ ");"++LF ++
      fst (pp_eexpr "  " (fn_body argname) fname 0)++LF++
    "endfunction"++LF.

  Fixpoint pp_fns {a b} (fs : fns.fns var fn a b) : string :=
    match fs with
    | fns.Let fname argname fn_body C =>
        pp_fn fname argname fn_body ++ ""++LF ++ pp_fns (C fname)
    | fns.Ret fname argname fn_body => pp_fn fname argname fn_body
    end.

  Require Import List.

  Definition type_set_add (t : type) (acc : list type) : list type :=
    if existsb (type.type_beq t) acc then acc else t :: acc.

  Fixpoint typeannots_type (t : type) (acc : list type) : list type :=
    let acc' := type_set_add t acc in
    match t with
    | type.Pair a b | type.Either a b => typeannots_type b (typeannots_type a acc')
    | type.Array t' _ => typeannots_type t' acc'
    | type.Struct _ nts => fold_right (fun nt a => typeannots_type (snd nt) a) acc' nts
    | _ => acc'
    end.

  Fixpoint typeannots_expr {t} (e : expr.expr var fn t) (acc : list type) : list type :=
    match e with
    | @expr.Const _ _ _ c => typeannots_type t acc
    | expr.Var x => acc
    | @expr.Get _ _ _ C r i => typeannots_type (typeWithHole.plug C t) (typeannots_expr i (typeannots_expr r acc))
    | @expr.Unop _ _ _ _ op e1 =>
        let acc := match op with
                   | @unop.Left l r | @unop.Right l r => typeannots_type r (typeannots_type l acc)
                   | _ => acc
                   end in
        typeannots_expr e1 acc
    | @expr.Binop _ _ _ _ _ op e1 e2 =>
        let acc := match op with
                   | @binop.MkPair a b => typeannots_type b (typeannots_type a acc)
                   | _ => acc
                   end in
        typeannots_expr e2 (typeannots_expr e1 acc)
    | expr.If cond a b => typeannots_expr b (typeannots_expr a (typeannots_expr cond acc))
    | @expr.Call _ _ _ _ _ e1 => typeannots_expr e1 acc
    end.

  Fixpoint typeannots_eexpr {t} (e : eexpr.eexpr var fn t) (acc : list type) : list type :=
    match e with
    | @eexpr.Ret _ _ _ exp => typeannots_expr exp acc
    | @eexpr.Let _ _ _ tx a _ aC =>
        typeannots_eexpr (aC "") (typeannots_expr a (typeannots_type tx acc))
    | @eexpr.Bind _ _ _ tx a _ aC =>
        typeannots_eexpr (aC "") (typeannots_eexpr a (typeannots_type tx acc))
    | @eexpr.If _ _ _ cond a b =>
        typeannots_eexpr b (typeannots_eexpr a (typeannots_expr cond acc))
    | @eexpr.Case _ _ _ _ cond _ l r =>
        typeannots_eexpr (r "") (typeannots_eexpr (l "") (typeannots_expr cond acc))
    | @eexpr.Upd _ _ _ i _ es v =>
        typeannots_expr v (typeannots_expr es (typeannots_expr i acc))
    end.

  Fixpoint typeannots_fns {a b} (fs : fns.fns var fn a b) (acc : list type) : list type :=
    let acc := typeannots_type b (typeannots_type a acc) in
    match fs with
    | @fns.Let _ _ _ _ a' b' _ _ fn_body C =>
        let acc := typeannots_type b' (typeannots_type a' acc) in
        typeannots_fns (C "") (typeannots_eexpr (fn_body "") acc)
    | fns.Ret _ _ fn_body =>
        typeannots_eexpr (fn_body "") acc
    end.

  Fixpoint is_subterm (s t : type) : bool :=
    type.type_beq s t ||
    match t with
    | type.Pair a b | type.Either a b => is_subterm s a || is_subterm s b
    | type.Struct _ nts => fold_right (fun nt b => b || is_subterm s (snd nt)) false nts
    | type.Array t _ => is_subterm s t
    | _ => false
    end.

  Fixpoint insert_type (t : type) (l : list type) : list type :=
    match l with
    | nil => t :: nil
    | h :: tail =>
        if is_subterm t h
        then t :: h :: tail
        else h :: insert_type t tail
    end.

  Definition topsort := fold_right insert_type [].

  Local Open Scope string_scope.

  Definition pp {a b} fns :="// Generated from Rocq by Quartz (experimental prototype version)
typedef enum { tt } unit;

class Pair #(parameter type A, parameter type B);
  typedef struct packed { A fst; B snd; } t;
  static function A fst (t p); return p.fst; endfunction
  static function B snd (t p); return p.snd; endfunction
  static function t mk (A a, B b); return t'{a, b}; endfunction
endclass

class Either #(parameter type A, parameter type B);
  typedef union tagged packed { A left; B right; } t;
  static function t left(A a); return tagged left a; endfunction
  static function t right(B b); return tagged right b; endfunction
endclass"++LF++LF++
    pp_typedefs (topsort (typeannots_fns fns [])) ++ ""++LF ++ @pp_fns a b fns.
End sv.

Section Test.
  Import (notations) eexpr expr. Local Open Scope string_scope.

  (* See THIS EXAMPLE ABOVE for how to structure your code *)
  Compute sv.pp fns.Private_example_wholeprogramdef.packaged_cycle.

  (* The tests below are not recommendations, they are just here to exercise printing and parsing *)
  Let make_tuple {var fn} : var (Bits 32) -> eexpr var fn _ :=
    fun v => quartz_eexpr:( return ( #v , #v , ! #v ) ).
  Compute sv.pp (fns.Ret "make_tuple" "v" make_tuple).

  Let increment_element {var fn} : var (Array (Bits 32) 4) -> eexpr var fn _ :=
    fun arr => quartz_eexpr:(
      let i := const (Zmod.of_Z _ 1 : Bits 2) in
      let cur_val := #arr[#i] in
      let next_val := #cur_val + const (Zmod.of_Z _ 1 : Bits _) in
      let arr_new <- #arr[#i] = #next_val in
      return #arr_new).
  Compute sv.pp (fns.Ret "increment_element" "arr" increment_element).

  Record Pixel := { valid : Bool; red : bits 8; green : bits 8; blue : bits 8 }.

  Let invert_red {var fn} : var (type.reify'' Pixel) -> eexpr var fn _ :=
    fun p => quartz_eexpr:(
      let cur_red := #p..red in
      let inv_red := ~ #cur_red in
      let p_new <- #p..red = #inv_red in
      return #p_new).
  Compute sv.pp (fns.Ret "invert_red" "p" invert_red).

  Let hole_red := @typeWithHole.Struct "Pixel" [("valid", type.Bool)] "red" typeWithHole.HOLE [("green", type.Bits 8); ("blue", type.Bits 8)] (fun _ => eq_refl).

  Let invert_red2 {var fn} : var _ -> eexpr var fn _ :=
    fun p => quartz_eexpr:(
      let cur_red := #p .[ hole_red , $expr.tt ] in
      let inv_red : Bits 8 := ~ #cur_red in
      let p_new <- #p .[ hole_red , $expr.tt ] = #inv_red in
      return #p_new).
  Compute sv.pp (fns.Ret "invert_red2" "invert_red2" invert_red2).

  Record OpsRecord := { val_a : bits 32; val_b : bits 32; }.

  Let all_ops_test {var fn} : var (type.reify'' OpsRecord) -> eexpr var fn type.Bool :=
    fun p => quartz_eexpr:(
      let a := #p .. val_a in
      let b := #p .. val_b in
      let un_opp := - #a in
      let un_not := ~ #a in
      let is_z   := ! #a in
      let un_ur : Bits 16 := $(expr.Unop unop.UnsignedResize (expr.Var a)) in
      let un_sr : Bits 16 := $(expr.Unop unop.SignedResize (expr.Var a)) in
      let mul1 : Bits 32 := $(expr.Binop binop.Mul (expr.Var a) (expr.Var b)) in 
      let mul2 : Bits 32 := #a * #b in 
      let b_add := #a + #b in
      let b_sub := #a - #b in
      let b_and := #a & #b in
      let b_or  := #a | #b in
      let b_slu := #a << #un_ur in
      let b_sru := #a >> #un_ur in
      let b_srs := #a .>> #un_ur in
      let b_eq := #a == #b in
      let b_lt := #a < #b in
      let b_gt := #a > #b in
      let b_le := #a <= #b in
      let b_ge := #a >= #b in
      let b_lts := #a .< #b in
      let b_gts := #a .> #b in
      let b_les := #a .<= #b in
      let b_ges := #a .>= #b in
      let b_mkp := (#a, #un_ur) in
      return #is_z).
  Compute sv.pp (fns.Ret "all_ops_test" "p" all_ops_test).

  Let wrap_value {var fn} : var (Bits 32) -> eexpr var fn _ :=
    fun v => quartz_eexpr:(
      let is_z := ! #v in
      if #is_z
      then return left #v
      else return right (const (Zmod.of_Z _ 255 : Bits 8))).
  Compute sv.pp (fns.Ret "wrap_value" "v" wrap_value).

  Let wrap_value2 {var fn} : var (Bits 32) -> eexpr var fn _ :=
    fun v => quartz_eexpr:(
      return if ! #v
             then left #v
             else right (const (Zmod.of_Z _ 255 : Bits 8))).
  Compute sv.pp (fns.Ret "wrap_value2" "v" wrap_value2).

  Let rotl3 {var fn} : var (Bits 32) -> eexpr var fn _ :=
    fun v => quartz_eexpr:(
      let sl := #v << 32 'd 3 in
      let sr := #v >> 32 'd 29 in
      return ( #sl | #sr )
    ).
  Compute sv.pp (fns.Ret "rotl3" "v" rotl3).

  Let safe_val {var fn} : var (Bits 32) -> eexpr var fn _ :=
    fun v => quartz_eexpr:(
      let is_z := ! #v in
      if #is_z then
        return ( 32'd 1)
      else
        return #v
   ).
  Compute sv.pp (fns.Ret "safe_val" "v" safe_val).
End Test.

Module InterfaceExample.
Import fn.
Module Fifo.
Record Fifo {var} (t_state t_data : type) := {
  cap      : fn var t_state (type.Bits 32);
  length   : fn var t_state (type.Bits 32);
  full     : fn var t_state type.Bool;
  empty    : fn var t_state type.Bool;
  enq      : fn var (type.Pair t_state t_data) t_state;
  deq      : fn var t_state (type.Pair t_state t_data)
}.
End Fifo. Notation Fifo := Fifo.Fifo (only parsing).

Module fifo1. Section fifo1.
  Context (t : type).

  Record state := { valid : Bool; payload : t; }.

  Definition State := type.reify'' state.

  Import (notations) eexpr expr. Local Open Scope string_scope.

  Let cap {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return 32 'd 1)).

  Let length {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return if #st..valid then 32 'd 1 else 32 'd 0)).

  Let full {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return #st..valid)).

  Let empty {var} := Fn (fun (st : var State) => quartz_eexpr:(
    return ! #st..valid )).

  Let enq {var} := Fn (fun (p : var (type.Pair State t)) => quartz_eexpr:(
      let st := #p .1 in let d  := #p .2 in
    let st <- #st..valid = true in
    let st <- #st..payload = #d in
    return #st)).

  Let deq {var} := Fn (fun (st : var State) => quartz_eexpr:(
    let out_d := #st..payload in
    let st_new <- #st..valid = false in
    return (#st_new, #out_d))).

  Definition impl {var} : @Fifo var State t := {|
    Fifo.cap    := cap;
    Fifo.length := length;
    Fifo.full   := full;
    Fifo.empty  := empty;
    Fifo.enq    := enq;
    Fifo.deq    := deq
  |}.

  Coercion rep (v : state) : type.reify'' state :=
    ltac2:(let t := struct.rep &v in exact $t).

  Lemma not_full_and_empty (st : state) :
    fn.interp empty st <> fn.interp full st.
  Proof.
    cbn -[Zmod.eqb]. (* reduces [#st..valid] in [length] even though [t] is abstract. *)
    (* embed_bool (Zmod.eqb 0 (valid st)) <> valid st *) case (Zmod.bool_cases (valid st)); cbv; congruence.
  Qed.
End fifo1. End fifo1.

End InterfaceExample.
