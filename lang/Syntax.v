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
  | Bool
  | Bits (sz: Z)
  | Pair (_ _ : type)
  | Either (_ _ : type)
  | Struct (_ : list (string * type))
  | Array (t: type) (sz: nat).
  Notation Unit := (Bits 0) (only parsing).

  Fixpoint interp t : Type :=
    match t with
    | Bool => bool
    | Bits sz => bits sz
    | Pair a b => interp a * interp b
    | Either a b => interp a + interp b
    | Struct nts => fold_right (fun nt T => interp (snd nt) * T)%type unit nts
    | Array t n => Vector.t (interp t) n
    end.
  Definition interpfn a b := interp a -> interp b.

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
    | Either a b => inl (default a) (* TODO: confirm this *)
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
        if b return Struct (nt::s) -> type.interp (if b then _ else _)
        then fst
        else fun v => get n (snd v)
    end.

  Fixpoint upd {s : struct} n : s -> (fieldType s n -> fieldType s n) -> s :=
    match s with
    | nil => fun s _ => s
    | cons nt s =>
        let b := String.eqb (fst nt) n in
        if b return let t := type.interp (if b then _ else _) in
                    Struct (nt::s) -> (t -> t) -> Struct (nt::s)
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
    | If e a b => if interp e then interp a else interp b
    | Call f e => f (interp e)
    end.

  Declare Custom Entry quartz_expr.
  Notation "quartz_expr:( e )" := e (e custom quartz_expr, only parsing).
  Notation "# v" := (expr.Var v) (in custom quartz_expr at level 0, v constr at level 0, format "'#' v").
  Notation "$ v" := v (in custom quartz_expr at level 0, v constr at level 0, format "'$' v").
  Notation "x" := (x) (in custom quartz_expr, x global, only parsing).
  Notation "f x" := (f x) (in custom quartz_expr at level 10).
  Notation "x == y" := (Binop (binop.EqBits) x y) (in custom quartz_expr at level 70).
  (*
  Notation "'let' x := e1 'in' e2"        := (Let "$let" e1 (fun x => e2))
    (in custom quartz_expr at level 200, x constr at level 0, e1 custom quartz_expr, e2 custom quartz_expr).
   *)

  (*
  Definition this (var : type -> Type) t := var t.
  Notation "this!" := (ltac:(match goal with x : @this _ _ |- ?g => exact (Var x) || exact x end))
    (in custom quartz_expr, only parsing).
  Notation "v 'at' f" := (ltac2:(let (c, t) := typeWithHole.reify_field (pretype f) in let v := pretype v in eexact (Get (C:=$c) (t:=$t) $v tt)))
    (in custom quartz_expr at level 10, f global, v custom quartz_expr, only parsing).
   *)
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
    | MatchEither {l r} (_ : expr (Either l r)) {t} (l : var l -> eexpr t) (r : var r -> eexpr t) : eexpr t
    | Upd {C : typeWithHole} (i : expr C) {t} (s := C t) (es : expr s) (v : expr t) : eexpr s.
  End WithSubstitutionType.
  Coercion Ret : expr >-> eexpr.
  Arguments eexpr : clear implicits.

  Fixpoint interp {t} (e: eexpr type.interp type.interpfn t) : t :=
    match e in eexpr _ _ t return t with
    | Ret e => expr.interp e
    | Let _ a b => let x := expr.interp a in interp (b x)
    | Bind _ a b => let x := interp a in interp (b x)
    | If e a b => if expr.interp e then interp a else interp b
    | MatchEither e l r => match expr.interp e with inl v => interp (l v) | inr v => interp (r v) end
    | Upd i s v => typeWithHole.upd (expr.interp s) (expr.interp i) (fun _ => expr.interp v)
    end.

  (*
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
   *)
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
    | MatchEither e a b => MatchEither (expr_map_fn e) (fun l => @eexpr_map_fn _ (a l)) (fun r => @eexpr_map_fn _ (b r))
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
    Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x =>
      Binop binop.Add (Var x) (Const (t:=Bits 8) (Zmod.of_Z _ 1))).

    Definition pred {var} : fn var (Bits 8) (Bits 8) := Fn (fun y =>
      eexpr.Let "_u" (Call succ (Unop (unop.UnsignedResize) (Var y))) (fun _u =>
      Binop binop.Add (Var y) (Const (t:=Bits 8) (Zmod.of_Z _ (-1))))).

    Definition cycle {var} := Fn (var:=var) (fun z =>
      eexpr.Let "r" (Call pred (Call succ (Var z))) (fun r =>
      Var r)).

    Lemma interp_cycle : interp cycle = fun z => (z + bits.of_Z _ 1 + bits.of_Z _ (-1))%Zmod.
    Proof.
      cbn [cycle            interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp].
      (* (fun v : Bits 8 => interp pred (interp succ v)) *)
      cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp].
      (* = RHS *)
      trivial.
    Qed.

    Lemma ok_cycle z : interp cycle z = z.
    Proof. rewrite interp_cycle, <-Zmod.add_assoc, (Zmod.of_Z_opp 1), Zmod.add_0_r; trivial. Qed.

    Definition lifted_cycle {var} : fn var _ _ := ltac2:(let e := let_lift_fns 'cycle in exact $e).

    Example let_lift_cycle : @lifted_cycle = @cycle.
    Proof. cbv beta delta [lifted_cycle]. cbv beta delta [cycle pred succ]. trivial. Qed.
  End Private_example_global_fn.

  Module Private_example_global_polyfn. (* polymorphic functions can't be packaged yet *)
    Definition succ {var} : fn var (Bits 8) (Bits 8) := Fn (fun x =>
      Binop binop.Add (Var x) (Const (t:=Bits 8) (Zmod.of_Z _ 1))).

    Definition pred {var} {n} : fn var (Bits n) (Bits n) := Fn (fun y =>
      eexpr.Let "_u" (Call succ (Unop (unop.UnsignedResize) (Var y))) (fun _u =>
      Binop binop.Add (Var y) (Const (t:=Bits n) (Zmod.of_Z _ (-1))))).

    Definition cycle {var} := Fn (var:=var) (fun z =>
      eexpr.Let "r" (Call (pred(n:=8)) (Call succ (Var z))) (fun r =>
      Var r)).

    Lemma interp_cycle : interp cycle = fun z => (z + bits.of_Z _ 1 + bits.of_Z _ (-1))%Zmod.
    Proof. cbn [cycle pred succ  interp body eexpr.interp eexpr_map_fn expr.interp expr_map_fn binop.interp]. trivial. Qed.

    Lemma ok_cycle z : interp cycle z = z.
    Proof. rewrite interp_cycle, <-Zmod.add_assoc, (Zmod.of_Z_opp 1), Zmod.add_0_r; trivial. Qed.

    Definition lifted_cycle {var} : fn var _ _ := ltac2:(let e := let_lift_fns 'cycle in exact $e).

    Example let_lift_cycle : @lifted_cycle = @cycle.
    Proof. cbv beta delta [lifted_cycle]. cbv beta delta [cycle pred succ]. trivial. Qed.
  End Private_example_global_polyfn.
End fn.

Module fns. (* deeply embedded environments of functions *)
  Import expr eexpr.
  Section WithSubstitutionType.
    Context {var : type -> Type}.
    Context {fn : type -> type -> Type}.
    Inductive fns {a b} :=
    | Let {a b} (func_name_hint arg_name_hint : string) (f : var a -> eexpr var fn b) (_ : fn a b -> fns)
    | Ret (arg_name_hint : string) (_ : var a -> eexpr var fn b).
  End WithSubstitutionType.
  Arguments fns : clear implicits.

  Fixpoint interp {a b} (fs : fns type.interp type.interpfn a b) : a -> b :=
    match fs with
    | Let _ _ f C => let f := fun a => eexpr.interp (f a) in interp (C f)
    | Ret _ f => fun a => eexpr.interp (f a)
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
    let tODO := constr:("tODO"%string) in
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
          printf "c %t" c;
          let lm := UConstr.make (UConstr.Lambda bv (UConstr.make (UConstr.Rel 2))) in
          let c := UConstr.substnl [lm] 0 (UConstr.liftn 1 2 c) in
          printf "c' %t" c;
          UConstr.make (UConstr.LetIn bf e (app_lets c a))
        | _ => 
          printf "OTHERLET %t" e;
          UConstr.make (UConstr.LetIn bf e (app_lets c a))
        end
      | _ => printf "OTHER %t" e; e
    end in
    let e := fn.let_lift_fns e in
    printf "%t" e; printf "==>";
    let e := app_lets e var in
    printf "%t" e;
    let rec replace_fn (e : constr) :=
      if Constr.equal e oldfn
      then fn else
      UConstr.map replace_fn e in
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
          UConstr.make (UConstr.App fnLet [|ta; t; tODO; tODO; replace_fn body; c|])
        | _ => e
        end
      | _ =>
        match Constr.decompose_app_list e with 
        | (f, [var'; ta; t; body]) =>
           if Bool.neg (Constr.equal f constr:(@fn.Fn)) then e else
           if Bool.neg (Constr.equal var' var) then e else
           UConstr.make (UConstr.App fnRet [|tODO; replace_fn body|])
        | _ => printf "OTHER %t" e; e
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
