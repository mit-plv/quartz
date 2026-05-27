From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
#[export] Set Primitive Projections.
From Stdlib Require Import Vector String List BinInt (* Bits  *)Datatypes. Import ListNotations.
From quartz.lang Require Import domain ident_to_string let_lift.
(* Import (coercions) domain.Zmod. *)

From stdpp Require Import base bitvector.definitions vector.


(* Open Scope Z_scope. *)
Module Import BV.
  Coercion embed_bool (b : bool) : bv 1 := bool_to_bv _ b.
  Coercion nonzero {m} (x : bv m) : bool := negb (bool_decide (x = bv_0 _)).
  Lemma nonzero_bool (b : bool) : nonzero b = b :> bool. Proof. case b; trivial. Qed.
  Inductive Cases2 : bv 1 -> Prop :=
  | Cases2_0 : Cases2 (bv_0 _) | Cases2_1 : Cases2 (Z_to_bv _ 1).
  Lemma cases2 (x : bv 1) : Cases2 x.
  Proof.
    destruct (decide (x = bv_0 _)) as [->|Hne].
    - constructor.
    - enough (x = Z_to_bv 1 1) as -> by constructor.
      apply (proj2 (bv_eq _ _ _)).
      assert (Hne' : bv_unsigned x ≠ 0%Z).
      { intro He. apply Hne. apply (proj2 (bv_eq _ _ _)).
        rewrite bv_0_unsigned. exact He. }
      assert (Heq : bv_unsigned (Z_to_bv 1 1) = 1%Z) by
        (apply Z_to_bv_small; unfold bv_modulus; simpl; lia).
      rewrite Heq.
      pose proof (bv_unsigned_in_range 1 x) as Hr.
      unfold bv_modulus in Hr. simpl in Hr. lia.
  Qed.
  Inductive BoolCases : bv 1 -> Prop :=
  | BoolTrue : BoolCases true | BoolFalse : BoolCases false.
  Lemma bool_cases (b : bv 1) : BoolCases b.
  Proof.
    destruct (cases2 b).
    - enough (embed_bool false = bv_0 1%N) as H by (rewrite <- H; exact BoolFalse).
      apply (proj2 (bv_eq _ _ _)).
      vm_compute. reflexivity.
    - exact BoolTrue.
  Qed.
End BV.

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
    | Bits sz => bv_0 _
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
    | vec ?t ?n =>
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
  Definition tt : Unit := bv_0 _.

  Fixpoint fieldType (s : struct) (n : string) : type :=
    match s with
    | nil => Unit
    | cons nt s =>
      if String.eqb (fst nt) n
      then snd nt
      else fieldType s n
    end.
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

Module unop.
  Inductive unop : type -> type -> Type :=
  | IsZero {n} : unop (Bits n) Bool
  | Not {n} : unop (Bits n) (Bits n) (* bitwise completement *)
  | Opp {n} : unop (Bits n) (Bits n) (* arithmetic negation *)
  | Resize (signed : bool) {n m} : unop (Bits n) (Bits m) (* zero-extend or truncate *)
  | Left {l r} : unop l (Either l r)
  | Right {l r} : unop r (Either l r)
  .
  Open Scope bv_scope.
  Definition interp {a b} (op: unop a b) : type.interp a -> type.interp b :=
    match op in unop a b return a -> b with
    | IsZero => fun v => bool_to_bv _ (bool_decide (v = bv_0 _))
    | Not => bv_not 
    | Opp => fun v => - v
    | Resize signed =>
        if signed
        then fun v => Z_to_bv _ (bv_signed v)
        else fun v => Z_to_bv _ (bv_unsigned v)
    | Left => inl
    | Right => inr
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
  | Slu {n m} : binop (Bits n) (Bits m) (Bits n)
  | Sru {n m} : binop (Bits n) (Bits m) (Bits n)
  | Srs {n m} : binop (Bits n) (Bits m) (Bits n)
  | Mul {n m z} : binop (Bits n) (Bits m) (Bits z) 
  | EqBits {n} : binop (Bits n) (Bits n) Bool
  | Compare (signed: bool) (c: compare) {n} : binop (Bits n) (Bits n) Bool
  | MkPair {a b: type} : binop a b (Pair a b)
  | App {n m} : binop (Bits n) (Bits m) (Bits (n + m)).
  Open Scope bv_scope.
  Definition interp {a b c} (op: binop a b c) : a -> b -> c :=
    match op in binop a b c return a -> b -> c with
    | Add => bv_add
    | Sub => fun x y => x - y
    | And => bv_and
    | Or => bv_or
    | Slu => fun a b => Z_to_bv _ (Z.shiftl (bv_unsigned a) (bv_unsigned b))
    | Sru => fun a b => Z_to_bv _ ((bv_unsigned a ≫ bv_unsigned b))
    | Srs => fun a b => Z_to_bv _ (bv_signed a ≫ (bv_unsigned b))
    | @Mul _ _ z => fun a b => Z_to_bv z (Z.mul (bv_unsigned a) (bv_unsigned b))
    | EqBits => fun a b => bool_to_bv _ (bv_unsigned a =? bv_unsigned b)%Z
    | Compare signed c => fun a b =>
        match c with cLt => Z.ltb | cGt => Z.gtb | cLe => Z.leb | cGe => Z.geb end
        (if signed then bv_signed a else bv_unsigned a)
        (if signed then bv_signed b else bv_unsigned b)
    | MkPair => Datatypes.pair
    | @App n m => (* fun x y => *) (* TODO: check semantics *)
              bv_concat (n + m)
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
Search vec.
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

    Definition tt := @Const Unit (bv_0 _).
    Definition true := @Const Bool true.
    Definition false := @Const Bool false.
    Definition zero {n} := @Const (Bits n) (bv_0 _).
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
  Notation "sz ''d' val" := (expr.Const (t:=Bits sz) (Z_to_bv _ val))
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

  Notation "e1 ++ e2" := (expr.Binop binop.App e1 e2) (in custom quartz_expr at level 50, left associativity).

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
    (in custom quartz_eexpr at level 200, f global, s custom quartz_expr at level 0, v custom quartz_expr at level 200, only parsing).
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
    Lemma interp_cycle : interp cycle = fun z => (z + Z_to_bv _ 1 + Z_to_bv _ (-1))%bv.
    Proof.
      cbn [cycle            interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp].
      (* = (fun v : Bits 8 => interp pred (interp succ v)) *)
      cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp].
      (* = RHS *)
      trivial.
    Qed.
    Lemma ok_cycle z : interp cycle z = z.
    Proof. rewrite interp_cycle, <-bv_add_assoc.
           rewrite bv_add_0_r ; auto.
    Qed.
  End Private_example_global_fn.

  Module Private_example_global_polyfn. (* polymorphic functions can't be packaged yet *)
    Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x => quartz_eexpr:(
      return ( #x + 8 'd 1 ))).
    Definition pred {var} {n} : fn var (Bits n) (Bits n) := Fn (fun y => quartz_eexpr:(
      let _u := succ ($(expr.Unop unop.UnsignedResize (expr.Var y)) ) in
      return ( #y + _ 'd (-1) ))).
    Definition cycle {var} := Fn (var:=var) (fun z => quartz_eexpr:(
      let r := pred ( succ ( #z ) ) in return #r)).
    Lemma interp_cycle : interp cycle = fun z => (z + Z_to_bv _ 1 + Z_to_bv _ (-1))%bv.
    Proof. cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp]. trivial. Qed.
    Lemma ok_cycle z : interp cycle z = z.
    Proof. rewrite interp_cycle, <-bv_add_assoc. 
           rewrite bv_add_0_r ; auto.
    Qed.
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

  Import Ltac2.Printf.

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
    let topfname := match Constr.decompose_app_list e with
      | (head, _) => match UConstr.kind head with
        | UConstr.Constant c _ => constr_string_of_string (Ident.to_string (List.last (Env.path (Std.ConstRef c))))
        | _ => printf "Failed to determine name of non-constant head: %t, using ""cycle""" head; constr:("cycle"%string)
        end
      end in
    let tga := lazy_match! Constr.type e with forall var, fn.fn var ?a _ => a end in
    let tgb := lazy_match! Constr.type e with forall var, fn.fn var _ ?b => b end in
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
      | _ => (* printf "UNRECOGNIZED %t" e; *) e
    end in
    let e := fn.let_lift_fns e in
    let e := app_lets e var in
    let rec replace_fn (e : constr) :=
      if Constr.equal e oldfn
      then fn else
      UConstr.map replace_fn e in
    let binder_name (b : binder) := match Binder.name b with
      | Some id => constr_string_of_ident id | None => constr:("x"%string) end in
    let lambda_name (body_constr : constr) := match UConstr.kind body_constr with
      | UConstr.Lambda lb _ => binder_name lb | _ => constr:("x"%string) end in
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
        | (f, [var'; _; _; body]) =>
           if Bool.neg (Constr.equal f constr:(@fn.Fn)) then e else
           if Bool.neg (Constr.equal var' var) then e else
           UConstr.make (UConstr.App fnRet [|topfname; lambda_name body; replace_fn body|])
        | _ => printf "UNRECOGNIZED %t" e; e
        end
    end in
    shallow_reify e.

  Notation package_global_fns'' var fn fns := (ltac2:(let e := fns.package_global_fns (pretype var) (pretype fn) (pretype fns) in exact $e)) (only parsing).

  Module Private_example_wholeprogramdef.
    Local Open Scope string_scope.
    Definition packaged_cycle {var fn} : fns _ _ _ _ :=
      package_global_fns'' var fn (@fn.Private_example_global_fn.cycle).
    Lemma packaged_ok : interp packaged_cycle = fn.interp fn.Private_example_global_fn.cycle.
    Proof. cbn beta iota delta [interp packaged_cycle]. trivial. Qed.
  End Private_example_wholeprogramdef.
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

  Lemma empty_ok (s : state) : fn.interp empty s = bool_decide (s.(valid) = bv_0 _).
  Proof. trivial. Qed.

  Lemma not_full_and_empty (st : state) :
    fn.interp empty st <> fn.interp full st.
  Proof.
    cbn.
    case (BV.bool_cases (valid st)); vm_compute bool_decide; 
      cbv[bool_to_bv]; discriminate.
    (* cbn -[Zmod.eqb]. (* reduces [#st..valid] in [length] even though [t] is abstract. *) *)
    (* (* embed_bool (Zmod.eqb 0 (valid st)) <> valid st *) case (Zmod.bool_cases (valid st)); cbv; congruence. *)
  Qed.
End fifo1. End fifo1.

End InterfaceExample.
