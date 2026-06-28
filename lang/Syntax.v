#[export] Set Primitive Projections.
From Stdlib Require Import Vector String List BinInt (* Bits  *)Datatypes. Import ListNotations.
From quartz.lang Require Import domain ident_to_string.
Import (coercions) domain.BV.

From stdpp Require Import base bitvector.definitions vector.

From Ltac2 Require Import Ltac2 Array List Constr Proj Ind Constructor Char.
Declare ML Module "quartz.monomorphize_plugin".
Ltac2 @ external rmonomorphize_fast : constr -> constr := "quartz.monomorphize_plugin" "rmonomorphize_fast".
Ltac2 @ external deglob_fast : constr -> constr := "quartz.monomorphize_plugin" "deglob_fast".
Ltac2 @ external fn2fns_fast : constr -> constr -> constr := "quartz.monomorphize_plugin" "fn2fns_fast".

Module type.
  Local Unset Elimination Schemes.
  Local Set Boolean Equality Schemes.
  Inductive type :=
  | Bits (sz: N)
  | Pair (_ _ : type)
  | Either (_ _ : type)
  | Struct (name : string) (_ : list (string * type))
  | Array (t: type) (sz: nat).
  Notation bits := bv.
  Notation Unit := (Bits 0) (only parsing).
  Notation Bool := (Bits 1) (only parsing).
  Fixpoint interp t : Type :=
    match t with
    | Bits sz => bits sz
    | Pair a b => interp a * interp b
    | Either a b => interp a + interp b
    | Struct _ nts => fold_right (fun nt T => interp (snd nt) * T)%type unit nts
    | Array t n => vec (interp t) n
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
  (* Fixpoint default_array (n : nat) := *)
  (*   match n return Vector.t t n with *)
  (*   | O => Vector.nil _ *)
  (*   | S n => Vector.cons (type.interp t) (default t) n (default_array n) *)
  (*   end. *)
  Definition default_array (n : nat) : vec t n :=
    fun_to_vec (fun _ => default t).
  End WithDefault.
  Fixpoint default (t : type) : t :=
    match t return t with
    | Bits sz => Z_to_bv _ 0
    | Pair a b => (default a, default b)
    | Either a b => inl (default a) (* TODO: confirm this *)
    | Struct _ s => default_struct default s
    | Array t n => default_array default t n
    end.

  Definition tt : Unit := bv_0 _.

  Fixpoint fieldType (s : struct) (n : string) : type :=
    match s with
    | nil => Unit
    | cons nt s =>
      if String.eqb (fst nt) n
      then snd nt
      else fieldType s n
    end.

  Declare Scope quartz_type.
  Bind Scope quartz_type with type.
  Delimit Scope quartz_type with quartz_type.
  Notation "a * b" := (Pair a%quartz_type b%quartz_type) : quartz_type.

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
    | vec ?t ?n =>
        let rt := reify t in
        constr:(type.Array $rt $n)
    | _ => match Constr.Unsafe.kind t with Constr.Unsafe.Ind ind inst =>
      let pp := match Ind.get_projections (Ind.data ind) with Some pp => pp | _ => Control.throw (InductiveNotAPrimitiveRecord t) end in
      let r := Array.fold_right (fun pp acc =>
          let c := Option.get (Proj.to_constant pp) in
          let n := constr_string_of_string (Ident.to_string (List.last (Env.path (Std.ConstRef c)))) in
          let e := Constr.Unsafe.make (Constr.Unsafe.Constant c inst) in
          let t := match Constr.Unsafe.kind (Constr.type e) with Constr.Unsafe.Prod _ t => t | _ => 'Empty_set end in
          let rt := reify t in
          constr:(cons ($n, $rt) $acc)
        ) pp constr:(@nil (String.string * type)) in
      let basename := constr_string_of_ident (List.last (Env.path (Std.IndRef ind))) in
      constr:(type.Struct $basename $r)
    | _ => Control.throw (ReifyUnknown t)
  end end.

  Notation reify'' state := (ltac2:(let r := type.reify (pretype state) in exact $r)) (only parsing).

End type.
Notation type := type.type (only parsing).
Import type.

Module struct.
  Notation struct := type.struct (only parsing).
  Notation fieldType := type.fieldType (only parsing).

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

  Local Open Scope string_scope.
  Local Example get_ab_a : @get [("a", Bits 7); ("b", Bool)] "a" = fun r => fst r.
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.
  Local Example get_ab_b : @get [("a", Bits 7); ("b", Bool)] "b" = fun r => fst (snd r).
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.
  Local Example get_ab_c : @get [("a", Bits 7); ("b", Bool)] "c" = fun r => tt.
  Proof. cbv [get fst snd String.eqb Ascii.eqb Bool.eqb Struct_ interp fold_right]. trivial. Qed.

  Ltac2 Type exn ::= [ RepUnknown (constr) ].

  Ltac2 rep v :=
    match Constr.Unsafe.kind (Constr.type v) with
    | Constr.Unsafe.Ind ind inst =>
      let arrproj := Option.get (Ind.get_projections (Ind.data ind)) in
      Array.fold_right (fun p acc =>
        let c := Option.get (Proj.to_constant p) in
        let e := Constr.Unsafe.make (Constr.Unsafe.Constant c inst) in
        let e := constr:($e $v) in
        constr:(pair $e $acc)
        ) arrproj 'Datatypes.tt
    | _ => Control.throw (RepUnknown (Constr.type v))
    end.
End struct.

Module unop.
  Inductive unop : type -> type -> Type :=
  | IsZero {n} : unop (Bits n) Bool
  | Not {n} : unop (Bits n) (Bits n) (* bitwise completement *)
  | Opp {n} : unop (Bits n) (Bits n) (* arithmetic negation *)
  | Resize (signed : bool) {n m} : unop (Bits n) (Bits m) (* zero-extend or truncate *)
  | Left {l r} : unop l (Either l r)
  | Right {l r} : unop r (Either l r)
  | Slice {n} (s l: N) : unop (Bits n) (Bits l)
  .
  Open Scope bv_scope.
  Definition interp {a b} (op: unop a b) : type.interp a -> type.interp b :=
    match op in unop a b return a -> b with
    | IsZero => fun v => bool_to_bv _ (bv_unsigned v =? 0 )%Z
    | Not => bv_not
    | Opp => fun v => - v
    | Resize signed =>
        if signed
        then fun v => Z_to_bv _ (bv_signed v)
        else fun v => Z_to_bv _ (bv_unsigned v)
    | Left => inl
    | Right => inr
    | Slice s l => fun v => bv_extract s l v
    end.

  Definition UnsignedResize {n m} := @Resize false n m.
  Definition SignedResize {n m} := @Resize true n m.
End unop.
Notation unop := unop.unop (only parsing).

Module binop.
  Inductive compare := cLt | cGt | cLe | cGe.

  Inductive binop : type -> type -> type -> Type :=
  | Add {n} : binop (Bits n) (Bits n) (Bits n)
  | Sub {n} : binop (Bits n) (Bits n) (Bits n)
  | And {n} : binop (Bits n) (Bits n) (Bits n)
  | Or {n} : binop (Bits n) (Bits n) (Bits n)
  | Xor {n} : binop (Bits n) (Bits n) (Bits n)
  | Slu {n} : binop (Bits n) (Bits n) (Bits n)
  | Sru {n} : binop (Bits n) (Bits n) (Bits n)
  | Srs {n} : binop (Bits n) (Bits n) (Bits n)
  | Mul {n m z} : binop (Bits n) (Bits m) (Bits z)
  | EqBits {n} : binop (Bits n) (Bits n) Bool
  | Compare (signed: bool) (c: compare) {n} : binop (Bits n) (Bits n) Bool
  | MkPair {a b: type} : binop a b (Pair a b)
  | App (sz: N) {n m} : binop (Bits n) (Bits m) (Bits sz).
  Open Scope bv_scope.
  Definition interp {a b c} (op: binop a b c) : a -> b -> c :=
    match op in binop a b c return a -> b -> c with
    | Add => bv_add
    | Sub => fun x y => x - y
    | And => bv_and
    | Or => bv_or
    | Xor => bv_xor
    | Slu => bv_shiftl
    | Sru => bv_shiftr
    | Srs => bv_ashiftr
    | @Mul _ _ z => fun a b => Z_to_bv z (Z.mul (bv_unsigned a) (bv_unsigned b))
    | EqBits => fun a b => bool_to_bv _ (bv_unsigned a =? bv_unsigned b)%Z
    | Compare signed c => fun a b =>
        match c with cLt => Z.ltb | cGt => Z.gtb | cLe => Z.leb | cGe => Z.geb end
        (if signed then bv_signed a else bv_unsigned a)
        (if signed then bv_signed b else bv_unsigned b)
    | MkPair => Datatypes.pair
    | @App sz n m => (* fun x y => *) (* TODO: check semantics *)
              bv_concat sz
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
  | Array (sz : nat) (t : typeWithHole) (index_width : N).

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
        (List.nth_default (default _) (Vector.to_list r) (Z.to_nat (bv_unsigned (fst i)))) (snd i)
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
        Vector.upd r (Z.to_nat (bv_unsigned (fst i)))
                     (fun r => upd _ _ r (snd i) f)
    end.
  Arguments upd {_ _}.

  Ltac2 Type exn ::= [ ReifyFieldUnknown (constr) ].

  Ltac2 reify_field p0c :=
    match Constr.Unsafe.kind p0c with
    | Constr.Unsafe.Constant c0 inst =>
      match Proj.of_constant c0 with
      | Some p0 =>
        lazy_match! type.reify (Constr.Unsafe.make (Constr.Unsafe.Ind (Proj.ind p0) inst)) with
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
Notation typeWithHole := typeWithHole.typeWithHole (only parsing).

Coercion typeWithHole.plug : typeWithHole >-> Funclass.
Coercion typeWithHole.indices : typeWithHole >-> type.

Module expr.
  Section WithSubstitutionType.
    Context {var : type -> Type}.
    Context {fn : type -> type -> Type}.

    Inductive expr : type -> Type :=
    | Const {t} (c : type.interp t) : expr t
    | Var {t} (x : var t) : expr t
    | Get {t} (C : typeWithHole) (r : expr (C t)) (i : expr C) : expr t
    | Unop {t t1} (op : unop t1 t) (e1 : expr t1) : expr t
    | Binop {t t1 t2} (op : binop t1 t2 t) (e1 : expr t1) (e2 : expr t2) : expr t
    | If {t} (_ : expr Bool) (a b : expr t) : expr t
    | Call {t a} (_ : fn a t) (_ : expr a) : expr t.

    Definition tt := @Const Unit (bv_0 _).
    Definition true := @Const Bool true.
    Definition false := @Const Bool false.
    Definition zero {n} := @Const (Bits n) (bv_0 _).
  End WithSubstitutionType.
  Arguments expr : clear implicits.

  Fixpoint interp (t : type) (e : expr type.interp type.interpfn t) {struct e} : type.interp t :=
    match e in expr _ _ t0 return type.interp t0 with
    | Const c => c
    | Var x => x
    | Get _ r i => typeWithHole.get (interp _ r) (interp _ i)
    | Unop op e1 => unop.interp op (interp _ e1)
    | Binop op e1 e2 => binop.interp op (interp _ e1) (interp _ e2)
    | If e a b => if interp _ e : bool then interp _ a else interp _ b
    | Call f e1 => f (interp _ e1)
    end.
  Arguments interp {t} e.

  Declare Custom Entry quartz_expr.
  Notation "quartz_expr:( e )" := e (e custom quartz_expr, only parsing).

  Notation "( e )" := e (in custom quartz_expr, e custom quartz_expr at level 200).
  Notation "# v" := (expr.Var v) (in custom quartz_expr at level 0, v constr at level 0, format "'#' v").
  Notation "$ v" := v (in custom quartz_expr at level 0, v constr at level 0, format "'$' v").
  (* Notation "x" := (x) (in custom quartz_expr at level 0, x global). *)
  Notation "sz ''d' val" := (expr.Const (t:=Bits sz) (Z_to_bv _ val))
    (in custom quartz_expr at level 0, sz constr at level 0, val constr at level 0, format "sz ''d' val").
  Notation "'const' c" := (expr.Const c) (in custom quartz_expr at level 0, c constr at level 0).
  Notation "f '(' e ')'" := (expr.Call f e)
    (in custom quartz_expr at level 0, left associativity, f global, e custom quartz_expr at level 200).

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
  Notation "'left' e" := (expr.Unop unop.Left e) (in custom quartz_expr at level 0, right associativity).
  Notation "'right' e" := (expr.Unop unop.Right e) (in custom quartz_expr at level 0, right associativity).

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
  Notation "e1 ^ e2" := (expr.Binop binop.Xor e1 e2) (in custom quartz_expr at level 45, left associativity).
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

  Notation "e1 ++ e2" := (expr.Binop (binop.App _) e1 e2) (in custom quartz_expr at level 50, left associativity).

  Notation "'if' cond 'then' a 'else' b" := (expr.If cond a b)
    (in custom quartz_expr at level 200, cond custom quartz_expr at level 200, a custom quartz_expr at level 200, b custom quartz_expr at level 200).

  Notation "r '..' f" := (expr.Get (ltac2:(let (c, _) := Syntax.typeWithHole.reify_field (pretype f) in exact $c)) r expr.tt)
    (in custom quartz_expr at level 1, left associativity, f global, r custom quartz_expr, only parsing).
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

  Definition LetBlock {X} {Y} (a: X) b  : Y:=
    let x := a in b a.

  Fixpoint interp {t} (e: eexpr type.interp type.interpfn t) : t :=
    match e in eexpr _ _ t return t with
    | Ret e => expr.interp e
    | Let _ a b => (* let x := expr.interp a in interp (b x) *)
                  LetBlock (expr.interp a) (fun x => interp (b x))
    | Bind _ a b => LetBlock (interp a) (fun x => interp ( b x))
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
  Notation "'let' x ':=' a 'in' b" := (eexpr.Let (string_of_binder_name'' x) a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, a custom quartz_expr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'let' x : t ':=' a 'in' b" := (eexpr.Let (tx:=t) (string_of_binder_name'' x) a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, t constr at level 200, a custom quartz_expr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'let' x '<-' a 'in' b" := (eexpr.Bind (string_of_binder_name'' x) a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, a custom quartz_eexpr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'let' x : t '<-' a 'in' b" := (eexpr.Bind (tx := t) (string_of_binder_name'' x) a (fun x => b))
    (in custom quartz_eexpr at level 200, x name, t constr at level 200, a custom quartz_eexpr at level 200, b custom quartz_eexpr at level 200, right associativity).
  Notation "'if' cond 'then' a 'else' b" := (eexpr.If cond a b)
    (in custom quartz_eexpr at level 200, cond custom quartz_expr at level 200, a custom quartz_eexpr at level 200, b custom quartz_eexpr at level 200).
  Notation "'match' cond 'with' | 'left' l '=>' a | 'right' r '=>' b 'end'" := (eexpr.Case cond (fun l => a) (fun r => b))
    (in custom quartz_eexpr at level 200, cond custom quartz_expr at level 200, l name, a custom quartz_eexpr at level 200, r name, b custom quartz_eexpr at level 200).

  Notation "s '[' i ']' '=' v" :=
    (eexpr.Upd (C:=typeWithHole.Array _ typeWithHole.HOLE _) (expr.Binop binop.MkPair i expr.tt) s v)
    (in custom quartz_eexpr at level 200, s custom quartz_expr at level 0, i custom quartz_expr at level 200, v custom quartz_expr at level 200).
  Notation "s .[ C , i ] '=' v" := (eexpr.Upd (C:=C) i s v)
    (in custom quartz_eexpr at level 200, s custom quartz_expr at level 0, C constr at level 0, i custom quartz_expr at level 200, v custom quartz_expr at level 200).

  Notation "s '..' f '=' v" := (eexpr.Upd (C:=ltac2:(let (c, _) := Syntax.typeWithHole.reify_field (pretype f) in exact $c)) expr.tt s v)
    (in custom quartz_eexpr at level 200, s custom quartz_expr at level 0, f global, v custom quartz_expr at level 200, only parsing).
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
    | eexpr.Ret e1 => eexpr.Ret (expr_map_fn e1)
    | eexpr.Let x e1 C => eexpr.Let x (expr_map_fn e1) (fun v => @eexpr_map_fn _ (C v))
    | eexpr.Bind x e1 C => eexpr.Bind x (@eexpr_map_fn _ e1) (fun v => @eexpr_map_fn _ (C v))
    | If e1 a b => If (expr_map_fn e1) (@eexpr_map_fn _ a) (@eexpr_map_fn _ b)
    | Case e1 a b => Case (expr_map_fn e1) (fun l => @eexpr_map_fn _ (a l)) (fun r => @eexpr_map_fn _ (b r))
    | Upd i s v => Upd (expr_map_fn i) (expr_map_fn s) (expr_map_fn v)
    end.
  End WithF.

  Fixpoint interp {a b} (f : fn type.interp a b) {struct f} : type.interp a -> type.interp b :=
     fun v => eexpr.interp (eexpr_map_fn (@interp) (f.(body) v)).


End fn.
Local Notation fn := fn.fn (only parsing).

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

  Notation package_global_fns'' var fn f :=
    (ltac2:(
       let var := pretype var in
       let fn := pretype fn in
       let hyps := Control.hyps () in
       Message.print (Message.of_string "--- Ltac2 Env Hyps ---");
       List.iter (fun (id, _, _) => Message.print (Message.of_ident id)) hyps;
       let f := pretype f in
       let rec get_head c := match Unsafe.kind c with
         | Unsafe.App h _ => get_head h
         | _ => c
         end in
       let head_c := get_head f in
       let top_name := match Unsafe.kind head_c with
         | Unsafe.Constant c _ =>
             let rec last l := match l with [] => "main" | x :: [] => Ident.to_string x | _ :: xs => last xs end in
             last (Env.path (Std.ConstRef c))
         | _ => "main"
         end in
       let f_app := constr:($f $var) in
       let f_mono := Control.time (Some "rmonomorphize_fast") (fun () => rmonomorphize_fast f_app) in
       let top_name_str := constr_string_of_string top_name in
       let bundle := Constr.Unsafe.make (Constr.Unsafe.App var [| fn; '(@fns.Let); '(@fns.Ret); 'Datatypes.true; 'Datatypes.false; 'Ascii.Ascii; 'String.String; 'String.EmptyString; top_name_str; '(@expr.Var); '(@expr.Call); '(@eexpr.Ret) |]) in
       let res := Control.time (Some "phase3_fn2fns_fast") (fun () => fn2fns_fast bundle f_mono) in
       exact ($res : fns $var $fn _ _)
    )) (only parsing).
End fns.
Local Notation fns := fns.fns (only parsing).

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
    return ! #st..valid)).

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

  Lemma empty_ok (s : state) : fn.interp empty s = (bv_unsigned s.(valid) =? 0)%Z.
  Proof. trivial. Qed.

  Lemma not_full_and_empty (st : state) :
    fn.interp empty st <> fn.interp full st.
  Proof.
    cbn.
    destruct (BV.bool_cases (valid st)); vm_compute;
      cbv[bool_to_bv]; discriminate.
    (* cbn -[Zmod.eqb]. (* reduces [#st..valid] in [length] even though [t] is abstract. *) *)
    (* (* embed_bool (Zmod.eqb 0 (valid st)) <> valid st *) case (Zmod.bool_cases (valid st)); cbv; congruence. *)
  Qed.
End fifo1. End fifo1.

End InterfaceExample.
