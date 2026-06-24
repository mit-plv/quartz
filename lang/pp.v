From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt Bits Vector String Ascii List DecimalString HexString.
Import ListNotations.

From stdpp Require Import bitvector.definitions.
From quartz.lang Require Import Syntax let_lift.

Module pp.
  Local Open Scope bool_scope. Local Open Scope string_scope.
  Definition var (t : type) := string.
  Definition fn (a b : type) := string.

  Local Coercion Z_of_ascii (c : Ascii.ascii) : BinInt.Z := BinInt.Z.of_N (Ascii.N_of_ascii c).
  Definition isalpha (c : BinInt.Z) : bool := ((("A"%char <=? c)%Z && (c <=? "Z"%char)%Z) || (("a"%char <=? c)%Z && (c <=? "z"%char)%Z))%bool.
  Definition isdigit (c : BinInt.Z) : bool := (("0"%char <=? c)%Z && (c <=? "9"%char)%Z)%bool.

  Definition Z (n : BinInt.Z) : string := NilZero.string_of_int (BinInt.Z.to_int n).
  Definition N (n : N) : string := NilZero.string_of_int (BinInt.Z.to_int (Z.of_N n)).
  Definition nat (n : Datatypes.nat) : string := NilZero.string_of_uint (Nat.to_uint n).
  Definition bits {n : BinNums.N} (v : type.bits n) : string :=
    N n ++ "'h" ++
    let s := HexString.of_Z (bv_unsigned v) in
    String.substring 2 (String.length s - 2) s.
  Definition LF := "
".

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

End pp.
