#[export] Set Primitive Projections.
From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
From Stdlib Require Import BinInt Bits Vector String Ascii List DecimalString HexString.
Import ListNotations.

From quartz.lang Require Import ident_to_string let_lift Syntax transform.

Module cpp.
  Local Open Scope bool_scope. Local Open Scope string_scope.
  Definition var (t : type) := string.
  Definition fn (a b : type) := string.

  Definition pp_Z (n : Z) : string := NilZero.string_of_int (Z.to_int n).
  Definition pp_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).
  Definition LF := "
".

  Local Coercion Z_of_ascii (c : Ascii.ascii) : Z := Z.of_N (Ascii.N_of_ascii c).
  Definition isalpha (c : Z) : bool := ((("A"%char <=? c)%Z && (c <=? "Z"%char)%Z) || (("a"%char <=? c)%Z && (c <=? "z"%char)%Z))%bool.
  Definition isdigit (c : Z) : bool := (("0"%char <=? c)%Z && (c <=? "9"%char)%Z)%bool.

  Fixpoint valid_ident_tail (s : string) : bool :=
    match s with
    | EmptyString => true
    | String c s => ((isalpha c || isdigit c || Z.eqb c "_"%char) && valid_ident_tail s)%bool
    end.

  Definition valid_ident (s : string) : string :=
    match s with
    | EmptyString => "`error ""empty name"" "
    | String c s' =>
      if (existsb (String.eqb s) [
        "alignas"; "alignof"; "auto"; "bool"; "break"; "case"; "char"; "const"; "constexpr"; "continue"; "default"; "do";
        "double"; "else"; "enum"; "extern"; "false"; "float"; "for"; "goto"; "if"; "inline"; "int"; "long"; "nullptr";
        "register"; "restrict"; "return"; "short"; "signed"; "sizeof"; "static"; "static_assert"; "struct"; "switch";
        "thread_local"; "true"; "typedef"; "typeof"; "typeof_unqual"; "union"; "unsigned"; "void"; "volatile"; "while";
        "asm"; "fortran"; "catch"; "char8_t"; "char16_t"; "char32_t"; "class"; "concept"; "consteval"; "constinit";
        "const_cast"; "decltype"; "delete"; "dynamic_cast"; "explicit"; "export"; "friend"; "mutable"; "namespace";
        "new"; "noexcept"; "operator"; "private"; "protected"; "public"; "reinterpret_cast"; "requires"; "static_cast";
        "template"; "this"; "throw"; "try"; "typeid"; "typename"; "using"; "virtual"; "wchar_t"
      ]) then "`error ""reserved name: " ++ s ++ """ "
      else if andb (orb (isalpha c) (Z.eqb c "_"%char)) (valid_ident_tail s')
           then "" else "`error ""invalid name: " ++ s ++ """ "
    end.

  Definition valid_type_shallow (t : type) : string :=
    match t with
    | type.Unit => ""
    | type.Bits sz => if (sz <? 0)%Z then "`error ""bitwidth must be nonnegative"" " else ""
    | type.Pair a b =>
        if (type.size a <=? 0)%Z || (type.size b <=? 0)%Z then "`error ""pair component must have positive size"" " else ""
    | type.Either a b =>
        if (type.size a <=? 0)%Z && (type.size b <=? 0)%Z then "`error ""one Either side must have positive size"" " else ""
    | type.Struct name _ => valid_ident name
    | type.Array t' sz => ""
    end.

  Fixpoint pp_type' (t : type) : string :=
    valid_type_shallow t ++
    match t with
    | type.Unit => "unit"
    | type.Bits sz => "unsigned _BitInt("++pp_Z sz++")"
    | type.Pair a b => "std::pair<"++pp_type' a++", "++pp_type' b++">"
    | type.Either a b => "std::variant<"++pp_type' a++", "++pp_type' b++">"
    | type.Struct name _ => name
    | type.Array t sz => "std::array<"++pp_type' t++", "++pp_nat sz++">"
    end.

  Definition pp_type (t : type) : string := pp_type' t.

  Definition pp_struct nts :=
    "struct { "++ fold_right (fun '(n, t') acc => valid_ident n ++ "[[no_unique_address]] " ++ pp_type t'++" "++n++"; "++acc) "" nts++ "}".

  Definition pp_typedef name nts :=
    "typedef "++pp_struct nts++" "++name++";"++LF.

  Fixpoint pp_typedefs (ts : list type) : string :=
    match ts with
    | nil => ""
    | type.Struct n nts :: ts => pp_typedef n nts ++ pp_typedefs ts
    | _ :: ts => pp_typedefs ts
    end.

  Fixpoint pp_const {t : type} : type.interp t -> string :=
    match t return type.interp t -> string with
    | type.Unit => fun b => "unit{}"
    | type.Bits sz => fun v => "(unsigned _BitInt("++pp_Z sz++"))"++pp_Z (Zmod.unsigned v)
    | type.Pair a b => fun p =>
        "std::make_pair("++@pp_const a (fst p)++", "++@pp_const b (snd p)++")"
    | type.Either a b => fun e =>
        match e with
        | inl v => "std::variant<"++pp_type a++", "++pp_type b++">(std::in_place_index<0>, "++@pp_const a v++")"
        | inr v => "std::variant<"++pp_type a++", "++pp_type b++">(std::in_place_index<1>, "++@pp_const b v++")"
        end
    | type.Struct name nts =>
        let fix pp_struct_val (fs : list (string * type))
          : fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs -> string :=
          match fs return fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs -> string with
          | nil => fun _ => ""
          | cons (n, t') rest => fun v =>
              let val_str := @pp_const t' (fst v) in
              let rest_str := pp_struct_val rest (snd v) in
              "."++n++"="++val_str ++
              (if match rest with nil => true | _ => false end then "" else ", ") ++
              rest_str
          end
        in fun s => name++"{ "++pp_struct_val nts s++" }"
    | type.Array t' sz =>
        let fix pp_vec {n} (v : Vector.t (type.interp t') n) : string :=
          match v in Vector.t _ n return string with
          | Vector.nil _ => ""
          | Vector.cons _ hd 0 tl => @pp_const t' hd
          | Vector.cons _ hd (S n') tl => @pp_const t' hd++", "++pp_vec tl
          end
        in fun v => pp_type t++"{ "++pp_vec v++" }"
    end.

  Fixpoint pp_hole (C : typeWithHole) (base : string) (idx : string) : string :=
    match C with
    | typeWithHole.HOLE => base
    | typeWithHole.PairL t1 _ => pp_hole t1 (base ++ ".first") idx
    | typeWithHole.PairR _ t2 => pp_hole t2 (base ++ ".second") idx
    | typeWithHole.Struct _ _ n t _ => pp_hole t (if String.eqb base "" then n else base ++ "." ++ n) idx
    | typeWithHole.Array _ t _ => pp_hole t ("at0(" ++ base ++ ", " ++ idx ++ ".first)") (idx ++ ".second")
    end.

  Definition pp_unop {t1 t2} (op : unop t1 t2) (e1_str : string) : string :=
    match op with
    | @unop.IsZero n => "(!"++e1_str++")"
    | @unop.Not n => "(~"++e1_str++")"
    | @unop.Opp n => "(-"++e1_str++")"
    | @unop.Resize false n m => "((unsigned _BitInt("++pp_Z m++"))("++e1_str++"))"
    | @unop.Resize true n m => "((unsigned _BitInt("++pp_Z m++"))((signed _BitInt("++pp_Z n++"))("++e1_str++")))"
    | @unop.Left l r => "std::variant<"++pp_type l++", "++pp_type r++">(std::in_place_index<0>, "++e1_str++")"
    | @unop.Right l r => "std::variant<"++pp_type l++", "++pp_type r++">(std::in_place_index<1>, "++e1_str++")"
    end.

  Definition pp_binop {t1 t2 t3} (op : binop t1 t2 t3) (e1_str e2_str : string) : string :=
    match op with
    | @binop.Add n => "("++e1_str++" + "++e2_str++")"
    | @binop.Sub n => "("++e1_str++" - "++e2_str++")"
    | @binop.And n => "("++e1_str++" & "++e2_str++")"
    | @binop.Or n => "("++e1_str++" | "++e2_str++")"
    | @binop.Slu n m => "slu<"++pp_Z n++", "++pp_Z m++">("++e1_str++", "++e2_str++")"
    | @binop.Sru n m => "sru<"++pp_Z n++", "++pp_Z m++">("++e1_str++", "++e2_str++")"
    | @binop.Srs n m => "srs<"++pp_Z n++", "++pp_Z m++">("++e1_str++", "++e2_str++")"
    | @binop.Mul n m z => "(unsigned _BitInt("++pp_Z z++"))("++e1_str++" * (unsigned _BitInt("++pp_Z (Z.max m z)++"))"++e2_str++")"
    | @binop.EqBits n => "("++e1_str++" == "++e2_str++")"
    | @binop.Compare signed c n =>
        let op_str := match c with
          | binop.cLt => "<" | binop.cGt => ">"
          | binop.cLe => "<=" | binop.cGe => ">="
        end in
        let e1_s := if signed then "((signed _BitInt("++pp_Z n++"))"++e1_str++")" else e1_str in
        let e2_s := if signed then "((signed _BitInt("++pp_Z n++"))"++e2_str++")" else e2_str in
        "("++e1_s++" "++op_str++" "++e2_s++")"
    | @binop.MkPair a b => "std::make_pair("++e1_str++", "++e2_str++")"
    | @binop.App n m => "((unsigned _BitInt("++pp_Z (n+m)++"))(((unsigned _BitInt("++pp_Z (n+m)++"))"++e2_str++") << "++pp_Z n++") | "++e1_str++")"
    end.

  Fixpoint pp_expr {t} (e : expr.expr var fn t) : string :=
    match e with
    | expr.Const c => pp_const c
    | expr.Var x => x
    | @expr.Get _ _ _ C r i => pp_hole C (pp_expr r) (pp_expr i)
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
        let stmt1 := ind ++ "const auto " ++ vname ++ " = " ++ pp_expr a ++ ";" in
        let '(stmt2, id') := pp_eexpr ind (aC vname) out_var (S id) in
        (stmt1 ++ ""++LF ++ stmt2, id')
    | @eexpr.Bind _ _ name_hint tx a _ aC =>
        let vname := name_hint ++ "_" ++ pp_nat id in
        let stmt_decl := ind ++ "{ " ++ pp_type tx ++ " " ++ vname ++ ";" in
        let '(stmt1, id1) := pp_eexpr ind a vname (S id) in
        let '(stmt2, id2) := pp_eexpr ind (aC vname) out_var id1 in
        (stmt_decl ++ ""++LF ++ stmt1 ++ ""++LF ++ stmt2 ++ " }", id2)
    | @eexpr.If _ _ _ cond a b =>
        let ind_nested := ind ++ "  " in
        let '(stmt_a, id1) := pp_eexpr ind_nested a out_var id in
        let '(stmt_b, id2) := pp_eexpr ind_nested b out_var id1 in
        (ind ++ "if (" ++ pp_expr cond ++ ") {"++LF ++
         stmt_a ++ ""++LF ++
         ind ++ "} else {"++LF ++
         stmt_b ++ ""++LF ++
         ind ++ "}", id2)
    | @eexpr.Case _ _ l_t r_t cond _ l_branch r_branch =>
        let c_var := "cond_" ++ pp_nat id in
        let l_var := "left_" ++ pp_nat id in
        let r_var := "right_" ++ pp_nat id in
        let ind_case := ind ++ "  " in
        let '(stmt_l, id1) := pp_eexpr ind_case (l_branch ("(*"++l_var++")")) out_var (S id) in
        let '(stmt_r, id2) := pp_eexpr ind_case (r_branch ("(*"++r_var++")")) out_var id1 in
        (ind ++ "{ const auto " ++ c_var ++ " = " ++ pp_expr cond ++ ";"++LF ++
         ind ++ "if (const auto " ++ l_var ++ " = std::get_if<0>(&" ++ c_var ++ ")) {"++LF ++
         stmt_l ++ ""++LF ++
         ind ++ "} else if (const auto " ++ r_var ++ " = std::get_if<1>(&" ++ c_var ++ ")) {"++LF ++
         stmt_r ++ ""++LF ++
         ind ++ "} }", id2)
    | @eexpr.Upd _ _ C i _ es v =>
        (ind ++ out_var ++ " = " ++ pp_expr es ++ ";"++LF ++ ind ++
         pp_hole C out_var (pp_expr i) ++ " = " ++ pp_expr v ++ ";", id)
    end.

  Fixpoint pp_stmt {s} (ind : string) (st : stmt.stmt var fn s) (id : nat) : string * nat :=
    match st with
    | stmt.Skip => ("", id)
    | @stmt.Let _ _ _ x tx a k =>
        let vname := x ++ "_" ++ pp_nat id in
        let stmt1 := ind ++ "const auto " ++ vname ++ " = " ++ pp_expr (a "") ++ ";" in
        let '(stmt2, id') := pp_stmt ind (k vname) (S id) in
        (stmt1 ++ LF ++ stmt2, id')
    | @stmt.Bind _ _ _ x tx a k =>
        let vname := x ++ "_" ++ pp_nat id in
        let stmt_decl := ind ++ "{ " ++ pp_type tx ++ " " ++ vname ++ ";" in
        let '(stmt1, id1) := pp_eexpr ind (a "") vname (S id) in
        let '(stmt2, id2) := pp_stmt ind (k vname) id1 in
        (stmt_decl ++ LF ++ stmt1 ++ LF ++ stmt2 ++ " }", id2)
    | @stmt.If _ _ _ cond a b =>
        let ind_nested := ind ++ "  " in
        let '(stmt_a, id1) := pp_stmt ind_nested a id in
        let '(stmt_b, id2) := pp_stmt ind_nested b id1 in
        (ind ++ "if (" ++ pp_expr (cond "") ++ ") {" ++ LF ++
         stmt_a ++ LF ++
         ind ++ "} else {" ++ LF ++
         stmt_b ++ LF ++
         ind ++ "}", id2)
    | @stmt.Case _ _ _ l_t r_t cond l_branch r_branch =>
        let c_var := "cond_" ++ pp_nat id in
        let l_var := "left_" ++ pp_nat id in
        let r_var := "right_" ++ pp_nat id in
        let ind_case := ind ++ "  " in
        let '(stmt_l, id1) := pp_stmt ind_case (l_branch ("(*"++l_var++")")) (S id) in
        let '(stmt_r, id2) := pp_stmt ind_case (r_branch ("(*"++r_var++")")) id1 in
        (ind ++ "{ const auto " ++ c_var ++ " = " ++ pp_expr (cond "") ++ ";" ++ LF ++
         ind ++ "if (const auto " ++ l_var ++ " = std::get_if<0>(&" ++ c_var ++ ")) {" ++ LF ++
         stmt_l ++ LF ++
         ind ++ "} else if (const auto " ++ r_var ++ " = std::get_if<1>(&" ++ c_var ++ ")) {" ++ LF ++
         stmt_r ++ LF ++
         ind ++ "} }", id2)
    | @stmt.Upd _ _ t l n C r pf i v =>
        (ind ++ pp_hole (@typeWithHole.Struct "" l n C r pf) "" (pp_expr (i "")) ++ " = " ++ pp_expr (v "") ++ ";", id)
    | @stmt.LetMut _ _ _ name_hint tx a k =>
        let vname := name_hint in
        let stmt1 := ind ++ pp_type tx ++ " " ++ vname ++ " = " ++ pp_expr (a "") ++ ";" in
        let '(stmt2, id') := pp_stmt ind k (S id) in
        (stmt1 ++ LF ++ stmt2, id')
    | @stmt.LetUpd _ _ _ name_hint C i t es v k =>
        let vname := name_hint ++ "_" ++ pp_nat id in
        let stmt1 := ind ++ "const auto " ++ vname ++ " = " ++ pp_expr (es "") ++ ";" in
        let stmt2 := ind ++ pp_hole C vname (pp_expr (i "")) ++ " = " ++ pp_expr (v "") ++ ";" in
        let '(stmt3, id') := pp_stmt ind (k vname) (S id) in
        (stmt1 ++ LF ++ stmt2 ++ LF ++ stmt3, id')
    | @stmt.Seq _ _ _ a b =>
        let '(stmt1, id1) := pp_stmt ind a id in
        let '(stmt2, id2) := pp_stmt ind b id1 in
        (stmt1 ++ LF ++ stmt2, id2)
    end.

  Definition pp_fn {a b} (fname argname : string) (fn_body : var a -> eexpr.eexpr var fn b) : string :=
    pp_type b ++ " " ++ fname ++ " (const " ++ pp_type a ++ "& " ++ argname ++ ") {"++LF ++
    "  " ++ pp_type b ++ " " ++ fname ++ "_out;"++LF ++
      fst (pp_eexpr "  " (fn_body argname) (fname ++ "_out") 0)++LF++
    "  return " ++ fname ++ "_out;"++LF++
    "}"++LF.

  Definition pp_fn_stmt {inputs outputs : type.struct} (fname : string) (body : stmt.stmt var fn (inputs ++ outputs)%list) : string :=
    let fix decl_inputs (l : type.struct) : string :=
      match l with
      | nil => ""
      | (n, t) :: rest => "  const auto " ++ n ++ " = args." ++ n ++ ";" ++ LF ++ decl_inputs rest
      end in
    let fix decl_outputs (l : type.struct) : string :=
      match l with
      | nil => ""
      | (n, t) :: rest => "  " ++ pp_type t ++ " " ++ n ++ " = " ++ pp_const (type.default t) ++ ";" ++ LF ++ decl_outputs rest
      end in
    let '(stmt_body, _) := pp_stmt "  " body 0 in
    let fix repack_outputs (l : type.struct) : string :=
      match l with
      | nil => ""
      | (n, t) :: rest => "." ++ n ++ "=" ++ n ++ (if match rest with nil => true | _ => false end then "" else ", ") ++ repack_outputs rest
      end in
    let ret_struct := pp_type (type.Struct (fname ++ "_out") outputs) ++ "{ " ++ repack_outputs outputs ++ " }" in
    pp_type (type.Struct (fname ++ "_out") outputs) ++ " " ++ fname ++ " (const " ++ pp_type (type.Struct (fname ++ "_in") inputs) ++ "& args) {" ++ LF ++
    decl_inputs inputs ++
    decl_outputs outputs ++
    stmt_body ++ LF ++
    "  return " ++ ret_struct ++ ";" ++ LF ++
    "}" ++ LF.

  Fixpoint pp_fns {a b} (fs : fns.fns var fn a b) : string :=
    match fs with
    | fns.Let fname argname fn_body C =>
      "static "++pp_fn fname argname fn_body ++ ""++LF ++ pp_fns (C fname)
    | @fns.LetStmt _ _ _ _ inputs outputs fname _ fn_body C =>
      "static "++@pp_fn_stmt inputs outputs fname fn_body ++ ""++LF ++ pp_fns (C fname)
    | fns.Ret fname argname fn_body => pp_fn fname argname fn_body
    | @fns.RetStmt _ _ inputs outputs fname _ fn_body =>
      @pp_fn_stmt inputs outputs fname fn_body
    end.

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
    | fns.LetStmt _ _ _ C =>
        typeannots_fns (C "") acc
    | fns.Ret _ _ fn_body =>
        typeannots_eexpr (fn_body "") acc
    | fns.RetStmt _ _ _ =>
        acc
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

  Definition ppRaw {a b} fns :="// Generated from Rocq by Quartz (experimental prototype version)
#include <variant>
#include <utility>
#include <array>
#include <cstddef>

struct unit {
    unit() = default;
    template <std::size_t N> operator unsigned _BitInt(N)() const { return 0; }
    template <std::size_t N> unit(unsigned _BitInt(N)) {}
};

template <typename T, std::size_t N>
T& at0(std::array<T, N>& arr, std::size_t idx) {
    if (idx < N) { return arr[idx]; }
    static thread_local T zero;
    zero = T{};
    return zero;
}

template <typename T, std::size_t N>
const T& at0(const std::array<T, N>& arr, std::size_t idx) {
    if (idx < N) { return arr[idx]; }
    static const T zero{};
    return zero;
}

template <std::size_t N, std::size_t M>
unsigned _BitInt(N) slu(unsigned _BitInt(N) a, unsigned _BitInt(M) b) {
    return b < N ? a << b : 0;
}

template <std::size_t N, std::size_t M>
unsigned _BitInt(N) sru(unsigned _BitInt(N) a, unsigned _BitInt(M) b) {
    return b < N ? a >> b : 0;
}

template <std::size_t N, std::size_t M>
unsigned _BitInt(N) srs(signed _BitInt(N) a, unsigned _BitInt(M) b) {
    return b < N ? a >> b : a >> (N - 1);
}

"++LF++
    pp_typedefs (topsort (typeannots_fns fns [])) ++ ""++LF ++ @pp_fns a b fns.
  Definition pp {a b} fns := @ppRaw a b (
    fns.rmap (fun _ e => expr.unresizesame (expr.unapp0l (expr.unapp0r e))) (fun _ => id) (fun a b => id) fns).

  Fixpoint wrap_pack {a b} (W : type.wf b) (fs : @fns.fns var fn a b) : @fns.fns var fn a (type.Bits (type.size b)) :=
    match fs in fns.fns _ _ a0 b0 return type.wf b0 -> fns.fns var fn a0 (type.Bits (type.size b0)) with
    | fns.Let fh ah f C => fun W => fns.Let fh ah f (fun f_val => wrap_pack W (C f_val))
    | @fns.LetStmt _ _ _ _ inputs outputs fh ah f C => fun W => @fns.LetStmt _ _ _ _ inputs outputs fh ah f (fun f_val => wrap_pack W (C f_val))
    | fns.Ret fh ah f => fun W => fns.Ret fh ah (fun va => eexpr.Bind "res" (f va) (fun vb => eexpr.pack W (expr.Var vb)))
    | @fns.RetStmt _ _ inputs outputs fname argname f => fun W => fns.Ret (fname ++ "_before_pack") argname (fun va => eexpr.Ret (expr.Const (t:=type.Bits (type.size _)) (bits.of_Z (type.size _) 0)))
    end W.

  Fixpoint get_ret_fname {a b} (fs : @fns.fns var fn a b) : string :=
    match fs with
    | fns.Let _ _ _ C => get_ret_fname (C "")
    | @fns.LetStmt _ _ _ _ _ _ fname _ _ C => get_ret_fname (C fname)
    | fns.Ret fname _ _ => fname
    | @fns.RetStmt _ _ _ _ fname _ _ => fname
    end.

  Definition pp_test_driver {a b} (W : type.wf b) (fs : @fns.fns var fn a b) : string :=
    let fname := get_ret_fname fs in
    pp (wrap_pack W fs) ++ LF ++
    "#include <iostream>" ++ LF ++
    "void print_hex(unit x) { std::cout << ""0'h0\n""; return; }" ++ LF ++
    "template <std::size_t N>" ++ LF ++
    "void print_hex(unsigned _BitInt(N) x) {" ++ LF ++
    "    std::cout << N << ""'h"";" ++ LF ++
    "    if (!x) { std::cout << ""0\n""; return; }" ++ LF ++
    "    int32_t i = (int32_t)((N + 3) / 4) - 1;" ++ LF ++
    "    for (; i >= 0; --i) {" ++ LF ++
    "        if (x >> (i * 4) & 0xF) break;" ++ LF ++
    "    }" ++ LF ++
    "    for (; i >= 0; --i) {" ++ LF ++
    "        std::cout << ""0123456789abcdef""[x >> (i * 4) & 0xF];" ++ LF ++
    "    }" ++ LF ++
    "    std::cout << ""\n"";" ++ LF ++
    "}" ++ LF ++
    "int main() {" ++ LF ++
    "  auto res = " ++ fname ++ "({});" ++ LF ++
    "  print_hex(res);" ++ LF ++
    "  return 0;" ++ LF ++
    "}" ++ LF.
End cpp.
