#[export] Set Primitive Projections.
From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
From Stdlib Require Import BinInt Bits Vector String List DecimalString HexString.
Import ListNotations.

From quartz.lang Require Import ident_to_string let_lift Syntax transform.

Module sv.
  Local Open Scope bool_scope. Local Open Scope string_scope.
  Definition var (t : type) := string.
  Definition fn (a b : type) := string.

  Definition pp_Z (n : Z) : string := NilZero.string_of_int (Z.to_int n).
  Definition pp_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).
  Definition LF := "
".

  Fixpoint pp_type' (t : type) (dims : string) : string :=
    match t with
    | type.Unit => "unit" ++ dims
    | type.Bits sz => "bit" ++ dims ++ "["++pp_Z (sz - 1)++":0]"
    | type.Pair a b => "Pair#("++pp_type' a ""++", "++pp_type' b ""++")::t" ++ dims
    | type.Either a b => "Either#("++pp_type' a ""++", "++pp_type' b ""++")::t" ++ dims
    | type.Struct name _ => name ++ dims
    | type.Array t' sz => pp_type' t' (dims ++ "["++pp_nat sz++"-1:0]")
    end.

  Definition pp_type (t : type) : string := pp_type' t "".

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
    | type.Struct name nts =>
        let fix pp_struct_val (fs : list (string * type))
          : fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs -> string :=
          match fs return fold_right (fun nt T => type.interp (snd nt) * T)%type unit fs -> string with
          | nil => fun _ => ""
          | cons (n, t') rest => fun v =>
              let val_str := @pp_const t' (fst v) in
              let rest_str := pp_struct_val rest (snd v) in
              n++": "++val_str ++
              (if match rest with nil => true | _ => false end then "" else ", ") ++
              rest_str
          end
        in fun s => name++"'{ "++pp_struct_val nts s++" }"
    | type.Array t' sz =>
        let fix pp_vec {n} (v : Vector.t (type.interp t') n) : string :=
          match v in Vector.t _ n return string with
          | Vector.nil _ => ""
          | Vector.cons _ hd 0 tl => @pp_const t' hd
          | Vector.cons _ hd (S n') tl => pp_vec tl++", "++@pp_const t' hd
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
    | @unop.IsZero n => "(!"++e1_str++")"
    | @unop.Not n => "(~"++e1_str++")"
    | @unop.Opp n => "(-"++e1_str++")"
    | @unop.Resize false n m => pp_Z m ++ "'($unsigned("++e1_str++"))"
    | @unop.Resize true n m => "$unsigned(" ++ pp_Z m ++ "'($signed("++e1_str++")))"
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
    | @binop.Mul n m z => pp_Z z ++ "'(" ++e1_str++" * "++e2_str++")"
    | @binop.EqBits n => "("++e1_str++" == "++e2_str++")"
    | @binop.Compare signed c n =>
        let op_str := match c with
          | binop.cLt => "<" | binop.cGt => ">"
          | binop.cLe => "<=" | binop.cGe => ">="
        end in
        let e1_s := if signed then "$signed("++e1_str++")" else e1_str in
        let e2_s := if signed then "$signed("++e2_str++")" else e2_str in
        "("++e1_s++" "++op_str++" "++e2_s++")"
    | @binop.MkPair a b => "Pair#("++pp_type a++", "++pp_type b++")::mk("++e1_str++", "++e2_str++")"
    | @binop.App n m => "{"++e2_str++", "++e1_str++"}"
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
        let stmt1 := ind ++ "begin " ++ pp_type tx ++ " " ++ vname ++ " = " ++ pp_expr a ++ ";" in
        let '(stmt2, id') := pp_eexpr ind (aC vname) out_var (S id) in
        (stmt1 ++ ""++LF ++ stmt2 ++ " end", id')
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

  Definition ppRaw {a b} fns :=
    "// Generated from Rocq by Quartz (experimental prototype version)
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
  Definition pp {a b} fns := @ppRaw a b (
    fns.rmap (fun _ e => expr.unresizesame (expr.unapp0l (expr.unapp0r e))) (fun _ => id) (fun a b => id) fns).
End sv.
