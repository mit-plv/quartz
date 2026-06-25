From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".
From Stdlib Require Import BinInt Bits Vector String Ascii List DecimalString HexString.
Import ListNotations.

From quartz.lang Require Import Syntax.

Module pp.
  Local Open Scope bool_scope. Local Open Scope string_scope.
  Definition var (t : type) := string.
  Definition fn (a b : type) := string.

  Local Coercion Z_of_ascii (c : Ascii.ascii) : BinInt.Z := BinInt.Z.of_N (Ascii.N_of_ascii c).
  Definition isalpha (c : BinInt.Z) : bool := ((("A"%char <=? c)%Z && (c <=? "Z"%char)%Z) || (("a"%char <=? c)%Z && (c <=? "z"%char)%Z))%bool.
  Definition isdigit (c : BinInt.Z) : bool := (("0"%char <=? c)%Z && (c <=? "9"%char)%Z)%bool.

  Definition Z (n : BinInt.Z) : string := NilZero.string_of_int (BinInt.Z.to_int n).
  Definition nat (n : Datatypes.nat) : string := NilZero.string_of_uint (Nat.to_uint n).
  Definition bits {n : BinInt.Z} (v : bits n) : string :=
    Z n ++ "'h" ++
    let s := HexString.of_Z (Zmod.unsigned v) in
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
        let acc' := match op with
                   | @unop.Left l r | @unop.Right l r => typeannots_type r (typeannots_type l acc)
                   | _ => acc
                   end in
        typeannots_expr e1 acc'
    | @expr.Binop _ _ _ _ _ op e1 e2 =>
        let acc' := match op with
                   | @binop.MkPair a b => typeannots_type b (typeannots_type a acc)
                   | _ => acc
                   end in
        typeannots_expr e2 (typeannots_expr e1 acc')
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

  Fixpoint mangle_type (t : type) : string :=
    match t with
    | type.Unit => "U"
    | type.Bits sz =>
        let sz_str := Z sz in
        sz_str ++ "B"
    | type.Pair a b =>
        mangle_type a ++ "_" ++ mangle_type b ++ "_P"
    | type.Either a b =>
        mangle_type a ++ "_" ++ mangle_type b ++ "_E"
    | type.Struct name fields =>
        let fields_str :=
          let fix mangle_fields (fields : list (string * type)) : string :=
            match fields with
            | nil => ""
            | (fname, ftype) :: rest =>
                mangle_type ftype ++ (match mangle_fields rest with "" => "" | r => "_" ++ r end)
            end
          in mangle_fields fields
        in
        let name_len := nat (String.length name) in
        let n_fields := nat (List.length fields) in
        (if match fields_str with "" => true | _ => false end then "" else fields_str ++ "_") ++
        name ++ name_len ++ "_" ++ n_fields ++ "S"
    | type.Array t' sz =>
        let sz_str := nat sz in
        mangle_type t' ++ "_" ++ sz_str ++ "A"
    end.

  Fixpoint mangle_fields (fields : list (string * type)) : string :=
    match fields with
    | nil => ""
    | (fname, ftype) :: rest =>
        mangle_type ftype ++ (match mangle_fields rest with "" => "" | r => "_" ++ r end)
    end.

  Definition mangle_struct_name (name : string) (fields : list (string * type)) : string :=
    let fields_str := mangle_fields fields in
    let n_fields := nat (List.length fields) in
    name ++ "__" ++ (if match fields_str with "" => true | _ => false end then "" else fields_str ++ "_") ++ n_fields ++ "S".

  Definition topsort := fold_right insert_type [].
End pp.

