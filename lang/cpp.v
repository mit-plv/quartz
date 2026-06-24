#[export] Set Primitive Projections.
From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
From Stdlib Require Import BinInt Bits Vector String Ascii List DecimalString HexString NArith.
Import ListNotations.
From stdpp Require Import bitvector.definitions.
From quartz.lang Require Import ident_to_string let_lift Syntax transform pp.

Module cpp.
  Local Open Scope bool_scope. Local Open Scope string_scope.
  Definition var := pp.var.
  Definition fn := pp.fn.
  Local Notation pp_Z := pp.Z.
  Local Notation pp_N := pp.N.
  Local Notation pp_nat := pp.nat.
  Local Notation LF := pp.LF.
  Local Notation isalpha := pp.isalpha.
  Local Notation isdigit := pp.isdigit.
  Local Notation topsort := pp.topsort.
  Local Notation typeannots_fns := pp.typeannots_fns.
  Local Coercion Z_of_ascii (c : Ascii.ascii) : Z := Z.of_N (Ascii.N_of_ascii c).

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

  Open Scope N_scope.

  Definition valid_type_shallow (t : type) : string :=
    match t with
    | type.Unit => ""
    | type.Bits sz => if (sz <? 0)%N then "`error ""bitwidth must be nonnegative"" " else ""
    | type.Pair a b =>
        if (type.size a <=? 0)%N || (type.size b <=? 0)%N then "`error ""pair component must have positive size"" " else ""
    | type.Either a b =>
        if (type.size a <=? 0)%N && (type.size b <=? 0)%N then "`error ""one Either side must have positive size"" " else ""
    | type.Struct name _ => valid_ident name
    | type.Array t' sz => ""
    end.

  Fixpoint pp_type' (t : type) : string :=
    valid_type_shallow t ++
    match t with
    | type.Unit => "unit"
    | type.Bits sz => "unsigned _BitInt("++pp_N sz++")"
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
    | type.Bits sz => fun v => "(unsigned _BitInt("++pp_N sz++"))"++pp_Z (bv_unsigned v)
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
          | Vector.nil => ""
          | @Vector.cons _ hd 0 tl => @pp_const t' hd
          | @Vector.cons _ hd (S n') tl => @pp_const t' hd++", "++pp_vec tl
          end
        in fun v => pp_type t++"{ "++pp_vec v++" }"
    end.

  Fixpoint pp_hole (C : typeWithHole) (base : string) (idx : string) : string :=
    match C with
    | typeWithHole.HOLE => base
    | typeWithHole.PairL t1 _ => pp_hole t1 (base ++ ".first") idx
    | typeWithHole.PairR _ t2 => pp_hole t2 (base ++ ".second") idx
    | typeWithHole.Struct _ _ n t _ => pp_hole t (base ++ "." ++ n) idx
    | typeWithHole.Array _ t _ => pp_hole t ("at0(" ++ base ++ ", " ++ idx ++ ".first)") (idx ++ ".second")
    end.

  Definition pp_unop {t1 t2} (op : unop t1 t2) (e1_str : string) : string :=
    match op with
    | @unop.IsZero n => "((unsigned _BitInt(1))(! "++e1_str++"))"
    | @unop.Not n => "((unsigned _BitInt("++pp_N n++"))(~ "++e1_str++"))"
    | @unop.Opp n => "((unsigned _BitInt("++pp_N n++"))(- "++e1_str++"))"
    | @unop.Resize false n m => "((unsigned _BitInt("++pp_N m++"))("++e1_str++"))"
    | @unop.Resize true n m => "((unsigned _BitInt("++pp_N m++"))((signed _BitInt("++pp_N n++"))("++e1_str++")))"
    | @unop.Left l r => "std::variant<"++pp_type l++", "++pp_type r++">(std::in_place_index<0>, "++e1_str++")"
    | @unop.Right l r => "std::variant<"++pp_type l++", "++pp_type r++">(std::in_place_index<1>, "++e1_str++")"
    | @unop.Slice _ s l => "((unsigned _BitInt("++pp_N l++"))(("++e1_str++") >> "++pp_N s++"))"
    end.

  Definition pp_binop {t1 t2 t3} (op : binop t1 t2 t3) (e1_str e2_str : string) : string :=
    match op with
    | @binop.Add n => "((unsigned _BitInt("++pp_N n++"))("++e1_str++" + "++e2_str++"))"
    | @binop.Sub n => "((unsigned _BitInt("++pp_N n++"))("++e1_str++" - "++e2_str++"))"
    | @binop.And n => "((unsigned _BitInt("++pp_N n++"))("++e1_str++" & "++e2_str++"))"
    | @binop.Or n => "((unsigned _BitInt("++pp_N n++"))("++e1_str++" | "++e2_str++"))"
    | @binop.Xor n => "((unsigned _BitInt("++pp_N n++"))("++e1_str++" ^ "++e2_str++"))"
    | @binop.Slu n => "slu<"++pp_N n++">("++e1_str++", "++e2_str++")"
    | @binop.Sru n => "sru<"++pp_N n++">("++e1_str++", "++e2_str++")"
    | @binop.Srs n => "srs<"++pp_N n++">("++e1_str++", "++e2_str++")"
    | @binop.Mul n m z => "((unsigned _BitInt("++pp_N z++"))("++e1_str++" * (unsigned _BitInt("++pp_N (N.max m z)++"))"++e2_str++"))"
    | @binop.EqBits n => "((unsigned _BitInt(1))("++e1_str++" == "++e2_str++"))"
    | @binop.Compare signed c n =>
        let op_str := match c with
          | binop.cLt => "<" | binop.cGt => ">"
          | binop.cLe => "<=" | binop.cGe => ">="
        end in
        let e1_s := if signed then "((signed _BitInt("++pp_N n++"))"++e1_str++")" else e1_str in
        let e2_s := if signed then "((signed _BitInt("++pp_N n++"))"++e2_str++")" else e2_str in
        "((unsigned _BitInt(1))("++e1_s++" "++op_str++" "++e2_s++"))"
    | @binop.MkPair a b => "std::make_pair("++e1_str++", "++e2_str++")"
    | @binop.App sz n m => "((unsigned _BitInt("++pp_N sz++"))(((unsigned _BitInt("++pp_N (n+m)++"))"++e2_str++" << "++pp_N n++") | (unsigned _BitInt("++pp_N (n+m)++"))"++e1_str++"))"
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

  Definition pp_fn {a b} (fname argname : string) (fn_body : var a -> eexpr.eexpr var fn b) : string :=
    pp_type b ++ " " ++ fname ++ " (const " ++ pp_type a ++ "& " ++ argname ++ ") {"++LF ++
    "  " ++ pp_type b ++ " " ++ fname ++ "_out;"++LF ++
      fst (pp_eexpr "  " (fn_body argname) (fname ++ "_out") 0)++LF++
    "  return " ++ fname ++ "_out;"++LF++
    "}"++LF.

  Fixpoint pp_fns {a b} (fs : fns.fns var fn a b) : string :=
    match fs with
    | fns.Let fname argname fn_body C =>
      "static "++pp_fn fname argname fn_body ++ ""++LF ++ pp_fns (C fname)
    | fns.Ret fname argname fn_body => pp_fn fname argname fn_body
    end.

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

template <std::size_t N>
unsigned _BitInt(N) slu(unsigned _BitInt(N) a, unsigned _BitInt(N) b) {
    return b < N ? a << b : 0;
}

template <std::size_t N>
unsigned _BitInt(N) sru(unsigned _BitInt(N) a, unsigned _BitInt(N) b) {
    return b < N ? a >> b : 0;
}

template <std::size_t N>
unsigned _BitInt(N) srs(signed _BitInt(N) a, unsigned _BitInt(N) b) {
    return b < N ? a >> b : a >> (N - 1);
}

"++LF++
    pp_typedefs (topsort (typeannots_fns fns [])) ++ ""++LF ++ @pp_fns a b fns.
  Definition pp {a b} fns := @ppRaw a b (
    fns.rmap (fun _ e => expr.unresizesame (expr.unapp0l (expr.unapp0r e))) (fun _ => id) (fun a b => id) fns).

  Fixpoint wrap_pack {a b} (W : type.wf b) (fs : @fns.fns var fn a b) : @fns.fns var fn a (type.Bits (type.size b)) :=
    match fs with
    | fns.Let fh ah f C => fns.Let fh ah f (fun f_val => wrap_pack W (C f_val))
    | fns.Ret fh ah f => fns.Ret fh ah (fun va => eexpr.Bind "res" (f va) (fun vb => eexpr.pack W (expr.Var vb)))
    end.

  Fixpoint get_ret_fname {a b} (fs : @fns.fns var fn a b) : string :=
    match fs with
    | fns.Let _ _ _ C => get_ret_fname (C "")
    | fns.Ret fname _ _ => fname
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
