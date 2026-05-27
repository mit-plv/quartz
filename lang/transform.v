From Stdlib Require Import BinInt Bits Eqdep.
From Stdlib Require Import String List HexString.
From Stdlib Require Vector.
From Stdlib Require Import Program.Equality.
Import ListNotations.
From Stdlib Require Import List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.

(* transparent *)
Definition proj1 {A B} : A /\ B -> A := fun '(conj a b) => a.
Definition proj2 {A B} : A /\ B -> B := fun '(conj a b) => b.

Module List.
Section Forall_forall.
  Context [A] [P : A -> Prop] (f : forall t : A, P t).
  Fixpoint Forall_forall_any (l : list A) : Forall P l :=
    match l with
    | nil => Forall_nil _
    | a :: l => Forall_cons a (f a) (Forall_forall_any l)
    end.
End Forall_forall.
End List.

From quartz.lang Require Import domain Syntax ident_to_string let_lift.
From stdpp Require Import bitvector.definitions.

Open Scope N_scope.

Import Syntax.type.
Module Import type.
  Section type_ind.
    Context P
      (Bits : forall sz, P (Bits sz))
      (Pair : forall t1 t2, P t1 -> P t2 -> P (Pair t1 t2))
      (Either : forall t1 t2, P t1 -> P t2 -> P (Either t1 t2))
      (Struct : forall name l, Forall (fun st => P (snd st)) l -> P (Struct name l))
      (Array : forall t sz, P t -> P (Array t sz)).
    Fixpoint type_ind (t : type) : P t :=
      match t with
      | type.Bits sz => Bits sz
      | type.Pair t1 t2 => Pair t1 t2 (type_ind t1) (type_ind t2)
      | type.Either t1 t2 => Either t1 t2 (type_ind t1) (type_ind t2)
      | type.Struct name l => Struct name l (List.Forall_forall_any (fun t => type_ind (snd t)) _)
      | type.Array t' sz => Array t' sz (type_ind t')
      end.
  End type_ind.

  Fixpoint eq_dec (x y : type) : {x = y} + {x <> y}. Proof. refine
    match x, y with
    | Bits sz1, Bits sz2 =>
      match N.eq_dec sz1 sz2 with
      | left pf => left _
      | _ => right _
      end
    | Pair x1 x2, Pair y1 y2 =>
      match eq_dec x1 y1, eq_dec x2 y2 with
      | left H1, left H2 => left _
      | _, _ => right _
      end
    | Either x1 x2, Either y1 y2 =>
      match eq_dec x1 y1, eq_dec x2 y2 with
      | left H1, left H2 => left _
      | _, _ => right _
      end
    | Struct n1 l1, Struct n2 l2 =>
      match String.string_dec n1 n2 with
      | left Hn =>
        match list_eq_dec (fun '(n1, t1) '(n2, t2) =>
          match String.string_dec n1 n2, eq_dec t1 t2 with
          | left Hl, left Hr => left _
          | _, _ => right _
          end) l1 l2 with
        | left Hl => left _
        | right Hl => right _
        end
      | right Hn => right _
      end
    | Array t1 sz1, Array t2 sz2 =>
      match eq_dec t1 t2, PeanoNat.Nat.eq_dec sz1 sz2 with
      | left Ht, left Hz => left _
      | _, _ => right _
      end
    | _, _ => right _
    end.
    all : try (intro; discriminate).
    all : try congruence.
  Qed.

  Fixpoint size (t : type) : N :=
    match t with
    | Bits sz => sz
    | Pair a b => size b + size a
    | Either a b => N.max (size a) (size b) + 1
    | Struct _ nts => fold_right (fun nt acc => acc + size (snd nt))%N 0%N nts
    | Array t n => Nat.iter n (N.add (size t)) 0%N
    end.

  Section WithPack.
    Context (pack : forall {t : type}, forall (v : t), bits (size t)).
    Fixpoint pack_struct (fs : list (string * type))
      : fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs ->
      bits (fold_right (fun nt acc => acc + size (snd nt)) 0 fs)%N :=
      match fs
      return fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs ->
             bits (fold_right (fun nt acc => acc + size (snd nt)) 0 fs)
      with | nil => fun _ => bv_0 _
      | p :: l => fun v => bv_concat _ (pack_struct l (snd v)) (@pack _ (fst v))
      end.
    Context {t : type}.
    Fixpoint pack_array n (v : Vector.t (type.interp t) n) : bits (Nat.iter n (N.add (size t)) 0) :=
      match v in Vector.t _ n
      return bits (Nat.iter n (N.add (size t)) 0)
      with | Vector.nil => bv_0 _ 
      | Vector.cons hd tl => bv_concat _ (@pack _ hd) (pack_array _ tl)
      end.
  End WithPack.
  Fixpoint pack {t : type} : forall (v : t), bits (size t) :=
    match t as t0 return t0 -> bits (size t0) with
    | Bits _ => fun v => v
    | Pair a b => fun p => bv_concat _ (pack (snd p)) (pack (fst p))
    | Either a b => fun e =>
        let s := N.max (size a) (size b) in
        match e with
        | inl v => bv_concat _ (Z_to_bv s (bv_unsigned (pack v))) (bv_0 1)
        | inr v => bv_concat _ (Z_to_bv s (bv_unsigned (pack v))) (Z_to_bv 1 1)
        end
    | Struct name fields => pack_struct (@pack) fields
    | Array t' n => pack_array (@pack) n
    end.

  Section MetaprogrammingUtilities.
  Section WithWf. Context (wf : type -> Prop).
  Fixpoint struct_wf (r : struct) (l : struct) {struct r} : Prop :=
    match r with
    | nil => True
    | (n, t) :: r =>
        (wf t /\ forall t, fieldType (l ++ (n, t) :: r) n = t) /\
        struct_wf r (l ++ [(n, t)])
    end.
  End WithWf.
  Fixpoint wf (t : type) : Prop :=
    match t with
    | Bits sz => 0 <= sz
    | Pair a b | Either a b => wf a /\ wf b
    | Struct _ nts => struct_wf (@wf) nts []
    | Array t _ => wf t
    end.
  End MetaprogrammingUtilities.
End type.

Module struct.
  Import struct.
  Fixpoint drop {name} l r : Struct name (l ++ r) -> Struct name r :=
    match l return Struct _ (l ++ r) -> Struct _ r with
    | nil => fun v => v
    | (n, t) :: l' => fun v => @drop name l' r (snd v)
    end.
End struct.

Module expr.
  Import expr.
  Section map.
  Context {var fn} (f : forall {t}, @expr var fn t -> @expr var fn t).
  Arguments f {_}.
  Definition map {t} (e : @expr var fn t) : @expr var fn t :=
    match e with
    | Const c => Const c
    | Var x => Var x
    | Get C r i => Get C (f r) (f i)
    | Unop op e1 => Unop op (f e1)
    | Binop op e1 e2 => Binop op (f e1) (f e2)
    | If e a b => If (f e) (f a) (f b)
    | Call fn a => Call fn (f a)
    end.
  End map.
  Section rmap.
    Context {var fn} (f : forall {t}, @expr var fn t -> @expr var fn t).
    Fixpoint rmap {t} (e : @expr var fn t) : @expr var fn t := f _ (@map _ _ (@rmap) _ e).
  End rmap.

  Definition unapp0l {var fn t} (e : expr var fn t) : expr var fn t :=
    match e with
    | Binop op e1 e2 =>
        match op in binop.binop _ _ t return _ -> _ -> expr var fn t with
        | (@binop.App n m) as op => fun e1 e2 =>
        if (n =? 0) && (0 <=? m) then Unop unop.UnsignedResize e2 else Binop op e1 e2
        | op' => fun e1 e2 => Binop op' e1 e2
        end%bool e1 e2
    | _ => e
    end.
  Lemma interp_unapp0l {t} e : interp (@unapp0l _ _ t e) = interp e.
  Proof.
    case e; trivial. destruct op; cbn [interp unapp0l]; trivial.
    (* case Z.eqb_spec; trivial. *)
    (* case Z.leb_spec; trivial. *)
    (* intros; subst; cbn [interp unop.interp binop.interp unop.UnsignedResize andb]; trivial. *)
    (* rewrite (Zmod.hprop_Zmod_1 _ (bv_0 _)). *)
    (* apply Zmod.to_Z_inj. *)
    (* rewrite bv_unsigned_of_Z, bits.unsigned_app by trivial using Z.le_refl. *)
    (* rewrite Z.lor_0_l, Z.shiftl_0_r, Z.add_0_l, Zmod.mod_unsigned; trivial. *)
  Admitted.

  Definition unapp0r {var fn t} (e : expr var fn t) : expr var fn t :=
    match e with
    | Binop op e1 e2 =>
        match op in binop.binop _ _ t return _ -> _ -> expr var fn t with
        | (@binop.App n m) as op => fun e1 e2 =>
        if (m =? 0) && (0 <=? n) then Unop unop.UnsignedResize e1 else Binop op e1 e2
        | op' => fun e1 e2 => Binop op' e1 e2
        end%bool e1 e2
    | _ => e
    end.
  Lemma interp_unapp0r {t} e : interp (@unapp0r _ _ t e) = interp e.
  Proof.
    case e; trivial. destruct op; cbn [interp unapp0r]; trivial.
    (* case Z.eqb_spec; trivial. *)
    (* case Z.leb_spec; trivial. *)
    (* intros; subst; cbn [interp unop.interp binop.interp unop.UnsignedResize andb]; trivial. *)
    (* rewrite (Zmod.hprop_Zmod_1 _ (bv_0 _)). *)
    (* apply Zmod.to_Z_inj. *)
    (* rewrite bv_unsigned_of_Z, bits.unsigned_app by trivial using Z.le_refl. *)
    (* rewrite Z.add_0_r, Z.shiftl_0_l, Z.lor_0_r, Zmod.mod_unsigned; trivial. *)
  Admitted.

  Definition unresizesame {var fn t} (e : expr var fn t) : expr var fn t :=
    match e with
      | Unop op e1 =>
        match op in unop.unop t1 t' return expr var fn t1 -> expr var fn t' with
        | @unop.Resize s n m => fun e1 =>
            match N.eq_dec n m with
            | left pf => eq_rect _ (fun T => expr var fn T) e1 _ (f_equal Bits pf)
            | right _ => Unop (@unop.Resize s n m) e1
            end
        | op' => fun e1 => Unop op' e1
        end e1
      | _ => e
    end.
  Lemma interp_unresizesame {t} e : interp (@unresizesame _ _ t e) = interp e.
  Proof.
    case e; trivial. destruct op; cbn [interp unresizesame]; trivial.
    case N.eq_dec as []; subst; cbn [eq_rect f_equal unop.interp]; trivial.
    intros; case signed; rewrite ?Zmod.of_Z_unsigned, ?Zmod.of_Z_signed; trivial.
  Admitted.
End expr.

Module eexpr.
  Import Syntax.expr expr eexpr.
  Section map.
  Context {var fn} (fe : forall t, @expr var fn t -> @expr var fn t) (fee : forall t, @eexpr var fn t -> @eexpr var fn t).
  Definition map {t} (e : @eexpr var fn t) : @eexpr var fn t :=
    match e in eexpr _ _ t return eexpr var fn t with
    | Ret e => Ret (fe _ e)
    | Let x a b => Let x (fe _ a) (fun v => fee _ (b v))
    | Bind x a b => Bind x (fee _ a) (fun v => fee _ (b v))
    | If e a b => If (fe _ e) (fee _ a) (fee _ b)
    | Case e l r => Case (fe _ e) (fun lv => fee _ (l lv)) (fun rv => fee _ (r rv))
    | Upd i s v => Upd (fe _ i) (fe _ s) (fe _ v)
    end.
  End map.
  Section rmap.
  Context {var fn} (fe : forall t, @expr var fn t -> @expr var fn t) (fee : forall t, @eexpr var fn t -> @eexpr var fn t).
  Fixpoint rmap {t} (e : @eexpr var fn t)  {struct e} : @eexpr var fn t :=
    fee t (map (@expr.rmap var fn fe) (@rmap) e).
  End rmap.

  Section pack.
  Context {var : type -> Type}.
  Context {fn : type -> type -> Type}.
  Local Notation expr := (@expr.expr var fn).
  Local Notation eexpr := (@eexpr var fn).
  Local Fixpoint app_assoc {A} (l1 l2 l3 : list A) : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) :=
    match l1 as l1' return (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3) with
    | nil => eq_refl
    | x :: xs => f_equal (cons x) (app_assoc xs l2 l3)
    end.

  Local Notation "e1 ++ e2" := (expr.Binop binop.App e1 e2).
  Local Notation "'cast' e" := (expr.Unop unop.UnsignedResize e) (at level 0).
  Section PackStruct.
    Context (pack : forall {t}, type.wf t -> expr t -> eexpr (Bits (size t))).
    Context (name : string).
    Fixpoint pack_struct (r : list (string * type)) (l : list (string * type)) :
      type.struct_wf type.wf r l -> expr (Struct name (l ++ r)) ->
        eexpr (Bits (fold_right (fun nt acc => acc + size (snd nt)) 0 r)) :=
      match r
      return type.struct_wf type.wf r l -> expr (Struct name (l ++ r)) ->
        eexpr (Bits (fold_right (fun nt acc => acc + size (snd nt)) 0 r))
      with | nil => fun _ _ => Ret (expr.Const (t:=Bits 0) (Z_to_bv _ 0))
      | (n, t) :: fs' => fun pf e =>
        Bind "f_packed" (@pack t (proj1 (proj1 pf)) (Get (@typeWithHole.Struct name l n typeWithHole.HOLE fs' (proj2 (proj1 pf))) e expr.tt)) (fun p =>
        Bind "fs_packed" (pack_struct fs' (l ++ [(n, t)]) (proj2 pf) (eq_rect _ (fun f => expr (Struct name f)) e _ (eq_sym (app_assoc l [(n, t)] fs')))) (fun pr =>
        Ret (cast (Var pr ++ Var p))))
      end.
  End PackStruct.
  Section PackArray.
    Context {t : type} (pack : expr t -> eexpr (Bits (size t))) (n : nat) (e : expr (Array t n)).
    Fixpoint pack_array (r : nat)
      : eexpr (Bits (Nat.iter r (N.add (size t)) 0)) :=
      match r return eexpr (Bits (Nat.iter r (N.add (size t)) 0)) with
      | O => Ret (@expr.Const _ _ (Bits 0) (Z_to_bv 0 0))
      | S r' =>
        let i := Z.of_nat (n-r)%nat in
        let index_width := N.log2_up (N.of_nat n) in
        Bind "elem_packed" (@pack (Get (typeWithHole.Array n typeWithHole.HOLE index_width) e (@Const _ _ (Pair (Bits index_width) Unit) (Z_to_bv index_width i, (bv_0 _))))) (fun pe =>
        Bind "rest_packed" (pack_array r') (fun pr =>
        Ret (Var pe ++ Var pr)))
      end.
  End PackArray.
  Fixpoint pack {t} {struct t} : forall (pf : type.wf t) (e : expr t), eexpr (Bits (size t)) :=
    match t return forall (pf : type.wf t) (e : expr t), eexpr (Bits (size t)) with
    | Bits sz => fun _ e => Ret e
    | Pair a b => fun pf e =>
      Bind "fst_packed" (pack (proj1 pf) (Get (typeWithHole.PairL typeWithHole.HOLE b) e expr.tt)) (fun pa =>
      Bind "snd_packed" (pack (proj2 pf) (Get (typeWithHole.PairR a typeWithHole.HOLE) e expr.tt)) (fun pb =>
      Ret (Var pb ++ Var pa)))
    | Either l r => fun pf e => Case e
      (fun lv => Bind "l_packed" (pack (proj1 pf) (Var lv)) (fun pl =>
        Ret (cast (Var pl) ++ @expr.Const _ _ (Bits 1) (Z_to_bv 1 0))))
      (fun rv => Bind "r_packed" (pack (proj2 pf) (Var rv)) (fun pr =>
        Ret (cast (Var pr) ++ @expr.Const _ _ (Bits 1) (Z_to_bv 1 1))))
    | Struct name fields => fun pf e => pack_struct (@pack) name fields [] pf e
    | Array t n => fun pf e => pack_array (@pack t pf) n e n
    end.
  End pack.


  Lemma unsigned_resize_id sz (x: bits sz): bv_unsigned (Z_to_bv sz (bv_unsigned x)) = bv_unsigned x.
  Proof.
    (* rewrite bits.unsigned_of_Z. apply bits.mod_to_Z. *)
  Admitted.

  Lemma struct_types_wf r : forall l, struct_wf (@wf) r l -> Forall (fun nt => wf (snd nt)) r.
  Proof.
    induction r as [| [n t] r' IHr]; cbn; intros.
    - constructor.
    - destruct H as [[Hw ?] Hr]. constructor; [exact Hw | apply (IHr (l ++ [(n, t)])); exact Hr].
  Qed.

  Lemma iter_nonneg : forall n f x, 0 <= x -> (forall y, 0 <= y -> 0 <= f y) -> 0 <= Nat.iter n f x.
  Proof. induction n; cbn; intros; [lia|]. apply H0. apply IHn; auto. Qed.


  Lemma size_nonneg : forall t, wf t -> 0 <= size t.
  Proof.
    induction t using type.type_ind; cbn; intros Hwf; try intuition lia.
    (* { apply struct_types_wf in Hwf. induction (Forall_and Hwf H) as [|nt l X ?%Forall_and_inv]; cbn in *; intuition lia. } *)
    (* { apply iter_nonneg; intuition lia. } *)
  Qed.

  Lemma sum_size_nonneg r l : struct_wf wf r l ->
    0 <= fold_right (fun nt acc => acc + size (snd nt)) 0 r.
  Proof.
    intros H%struct_types_wf. induction H as [| x xs Hwf_x Hwf_xs IH]; cbn; [lia |].
    pose proof (size_nonneg (snd x) Hwf_x); lia.
  Qed.

  Lemma expr_interp_eq_rect name l1 l2 (pf : l1 = l2) (e : expr type.interp type.interpfn (Struct name l1)) :
    expr.interp (eq_rect _ (fun l => expr type.interp type.interpfn (Struct name l)) e _ pf) =
    eq_rect _ (fun l => type.interp (Struct name l)) (expr.interp e) _ pf.
  Proof. destruct pf. reflexivity. Qed.

  Lemma eq_rect_struct_cons name n t l1 l2 (pf : l1 = l2)
    (e : Struct name ((n, t) :: l2)) :
    snd (eq_rect _ (fun x : list (string * type) => Struct name x) e _ (eq_sym (f_equal (cons (n, t)) pf))) =
    eq_rect _ (fun x : list (string * type) => Struct name x) (snd e) _ (eq_sym pf).
  Proof. destruct pf. reflexivity. Qed.

  Lemma snd_drop_cons_r name l n t r (e : type.interp (Struct name (l ++ (n, t) :: r))) :
    snd (struct.drop l ((n, t) :: r) e) =
    struct.drop (l ++ [(n, t)]) r (eq_rect _ (fun f => type.interp (Struct name f)) e _ (eq_sym (app_assoc l [(n, t)] r))).
  Proof. revert e. induction l as [|[]]; cbn [Datatypes.app struct.drop app_assoc]; intros; trivial; erewrite eq_rect_struct_cons; auto. Qed.

  Lemma fst_drop_cons_r name l n t r (e : type.interp (Struct name (l ++ (n, t) :: r)))
    (Hfield : forall t', fieldType (l ++ (n, t') :: r) n = t') :
    fst (struct.drop l ((n, t) :: r) e) =
    eq_rect _ (fun x => type.interp x) (struct.get n e) _ (Hfield t).
  Proof.
    (* revert e. induction l as [| [n0 t0] l' IHl]; cbn; intros. *)
    (* { cbn in Hfield. destruct (String.eqb n n) eqn:Heq. *)
    (*   { rewrite <- Eqdep_dec.eq_rect_eq_dec; trivial using type.eq_dec. } *)
    (*   { rewrite eqb_refl in Heq; discriminate. } } *)
    (* { cbn in Hfield. destruct (String.eqb n0 n) eqn:Heq; trivial. *)
    (*   enough (Bits 1 = Bits 0); congruence. } *)
  Admitted.

  Lemma interp_pack_struct (name : string) (r l : list (string * type)) {e pf}
    (pack : forall t, wf t -> expr type.interp interpfn t -> eexpr type.interp interpfn (Bits (size t)))
    (Hpack : Forall (fun st => forall pf e, interp (pack (snd st) pf e) = type.pack (expr.interp e)) r) :
    bv_unsigned (interp (pack_struct pack name r l pf e)) =
    bv_unsigned (type.pack_struct (@type.pack) r (struct.drop l r (expr.interp e))).
  Proof.
    revert l e pf; induction Hpack as [| [n t] r Hpack ? IH]; [trivial |].
    cbn [pack_struct type.pack_struct eexpr.interp expr.interp unop.interp binop.interp
      struct.drop unop.UnsignedResize fold_right fst snd struct_wf]; intros.
    destruct pf as [[Hwf_t Hfield] Hwf_r].
    (* rewrite unsigned_resize_id. *)
    (* rewrite bits.unsigned_app; [ | eapply sum_size_nonneg; eauto | apply size_nonneg; auto ]. *)
    (* rewrite IH with (pf:=Hwf_r) by auto. rewrite Hpack. *)
    (* rewrite bits.unsigned_app; [ | eapply sum_size_nonneg; eauto | apply size_nonneg; auto ]. *)
    (* rewrite expr_interp_eq_rect, <-snd_drop_cons_r. *)
    (* f_equal; f_equal; cbn [expr.interp typeWithHole.get]; f_equal; f_equal; erewrite <-fst_drop_cons_r; trivial. *)
  Admitted.

  Lemma hd_skipn [A] i (l : list A) (d : A) :
    hd d (skipn i l) = nth_default d l i.
  Proof. revert l. induction i, l; trivial || apply IHi. Qed.

  Lemma skipn_S_l [A] i (l : list A) :
    skipn (S i) l = tl (skipn i l).
  Proof. revert l. induction i, l; trivial || apply IHi. Qed.

  Lemma interp_pack_array [t] (twf : wf t)
    (pack : expr type.interp interpfn t -> eexpr type.interp interpfn (Bits (size t)))
    (Hpack : forall e, interp (pack e) = type.pack (expr.interp e))
    r i e :
    bv_unsigned (interp (pack_array pack (i+r) e r)) =
    bv_unsigned (type.pack_array (@type.pack) _ (Vector.unappr (expr.interp e))).
  Proof.
    revert i e; induction r as [| r' IH]; intros.
    { generalize (Vector.unappr (expr.interp e)); eapply Vector.case0; trivial. }
    set (v := Vector.unappr (expr.interp e)).
    change (fix interp (t:type) := _) with @type.interp in *.
    assert (to_list_v : Vector.to_list v = skipn i (Vector.to_list (expr.interp e)))
      by (subst v; rewrite Vector.to_list_unappr; trivial).
    clearbody v. destruct (ltac:(lia) : S i + r' = i + S r')%nat.
    cbn [pack_array type.pack_array eexpr.interp expr.interp unop.interp unop.UnsignedResize binop.interp].
    rewrite Hpack. cbn [pack_array type.pack_array eexpr.interp expr.interp unop.interp unop.UnsignedResize binop.interp].
    (* setoid_rewrite bits.unsigned_app; try apply size_nonneg; trivial. *)
    (* rewrite IH. cbn [typeWithHole.get fst]. rewrite bv_unsigned_of_Z, Z.mod_small, Nat2Z.id. *)
    (* assert (S i + r' - S r' = i)%nat as -> by lia. *)
    (* 2: split; [lia|]; apply Z.lt_le_trans with (Z.of_nat (S i + r')); [lia | apply Z.log2_log2_up_spec; lia]. *)
    (* 2: match goal with |- context [?F r'] => lazymatch type of F with nat -> Z => *)
    (*      replace (F r') with (Init.Nat.iter r' (Z.add (size t)) 0) in * by trivial end end; *)
    (*      apply iter_nonneg; [lia | intros; pose proof (size_nonneg t twf); lia]. *)
    (* revert to_list_v; pattern v; refine (@Vector.caseS' t r' _ _ _); intros. *)
    (* cbn [type.pack_array]. *)
    (* match goal with |- context [@bv_unsigned ?M (@bv_concat _ ?N ?K ?A ?B)] => *)
    (*   replace (@bv_unsigned M (@bv_concat _ N K A B)) with (Z.lor (bv_unsigned A) (Z.shiftl (bv_unsigned B) N)) *)
    (*     by (symmetry; apply bits.unsigned_app; *)
    (*   [apply size_nonneg; auto | eapply iter_nonneg; [lia | intros; pose proof (size_nonneg t twf); lia]]) end. *)
    (* eapply f_equal2. *)
    (* - f_equal. f_equal. setoid_rewrite (f_equal (List.hd (default t)) to_list_v). *)
    (*   rewrite hd_skipn; trivial. *)
    (* - f_equal. f_equal. f_equal. apply Vector.to_list_inj. *)
    (*   rewrite Vector.to_list_unappr, skipn_S_l. *)
    (*   setoid_rewrite (f_equal (@List.tl _) to_list_v); trivial. *)
  Admitted.

  Lemma interp_pack [t] [w : type.wf t] e : interp (pack w e) = type.pack (expr.interp e).
  Proof.
    induction t using type.type_ind; cbn [pack eexpr.interp expr.interp];
      intros; apply bv_unsigned_inj.
    { destruct (expr.interp e); trivial. }
    { rewrite IHt1, IHt2 by (inversion w; auto); trivial. }
    { destruct (expr.interp e); rewrite ?IHt1, ?IHt2 by (inversion w; auto); trivial. }
    { setoid_rewrite interp_pack_struct; trivial. }
    { setoid_rewrite (interp_pack_array _ _ _ _ 0); trivial. }
  Qed.
End eexpr.

Module fns.
  Import fns.
  Section map.
    Context {var fn}
            (fee : forall t, @eexpr var fn t -> @eexpr var fn t)
            (ffns : forall a b, @fns var fn a b -> @fns var fn a b).
    Definition map {a b} (fs : @fns var fn a b) : @fns var fn a b :=
      match fs with
      | Let fh ah f C => Let fh ah (fun v => fee _ (f v)) (fun fn_val => ffns _ _ (C fn_val))
      | Ret fh ah f => Ret fh ah (fun v => fee _ (f v))
      end.
  End map.

  Section rmap.
    Context {var fn}
            (fe : forall t, @expr var fn t -> @expr var fn t)
            (fee : forall t, @eexpr var fn t -> @eexpr var fn t)
            (ffns : forall a b, @fns var fn a b -> @fns var fn a b).
    Fixpoint rmap {a b} (fs : @fns var fn a b) : @fns var fn a b :=
      ffns a b (map (@eexpr.rmap var fn fe fee) (@rmap) fs).
  End rmap.
End fns.
