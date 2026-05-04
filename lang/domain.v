#[export] Set Primitive Projections.
From Stdlib Require Import BinInt Bits Eqdep.
From Stdlib Require Import String List HexString.
From Stdlib Require Vector.
Import ListNotations.

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

Module bits.
  Definition hex {n : Z} (v : bits n) : string :=
    let s := HexString.of_Z (Zmod.unsigned v) in
    String.substring 2 (String.length s - 2) s.
End bits.

Module Vector.
  Section WithA.
  Context {A : Type}.
  Fixpoint upd {n} (xs : Vector.t A n) (i : nat) (f : A -> A) : Vector.t A n :=
    match xs in Vector.t _ n return Vector.t A n with
    | Vector.nil _ => Vector.nil _
    | Vector.cons _ x _ xs =>
      match i with
      | O => Vector.cons _ (f x) _ xs
      | S i => Vector.cons _ x _ (upd xs  i f)
      end
    end.
  Definition tl {n} (v : Vector.t A n) : Vector.t A (Nat.pred n) :=
    match v with
    | Vector.nil _ => Vector.nil _
    | Vector.cons _ a _ v => v
    end.
  Fixpoint unappr {i n} {struct i} : forall (v : Vector.t A (i+n)), Vector.t A n :=
    match i with
    | O => fun v => v
    | S i => fun v => unappr (tl v)
    end.
  End WithA.
  Lemma to_list_unappr [A] i r (v : Vector.t A (i+r)) :
    Vector.to_list (@Vector.unappr A i r v) = skipn i (Vector.to_list v).
  Proof.
    induction i; trivial.
    pattern v; apply @Vector.caseS'; intros. apply IHi.
  Qed.
End Vector.
