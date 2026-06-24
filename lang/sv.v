#[export] Set Primitive Projections.
From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.
From Stdlib Require Import BinInt Bits Vector String Ascii List DecimalString HexString NArith.
Import ListNotations.
From stdpp Require Import bitvector.definitions.
From quartz.lang Require Import ident_to_string let_lift Syntax transform pp.

Module sv.
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
    | String c s => ((isalpha c || isdigit c || (c =? "_"%char)%Z || (c =? "$"%char)%Z) && valid_ident_tail s)%bool
    end.

  Definition valid_ident (s : string) : string :=
    match s with
    | EmptyString => "`error ""empty name"" "
    | String c s' =>
      if (existsb (String.eqb s) [
        "always"; "and"; "assign"; "begin"; "buf"; "bufif0"; "bufif1"; "case"; "casex"; "casez"; "cmos"; "deassign";
        "default"; "defparam"; "disable"; "edge"; "else"; "end"; "endcase"; "endfunction"; "endmodule"; "endprimitive";
        "endspecify"; "endtable"; "endtask"; "event"; "for"; "force"; "forever"; "fork"; "function"; "highz0";
        "highz1"; "if"; "ifnone"; "initial"; "inout"; "input"; "integer"; "join"; "large"; "macromodule"; "medium";
        "module"; "nand"; "negedge"; "nmos"; "nor"; "not"; "notif0"; "notif1"; "or"; "output"; "parameter"; "pmos";
        "posedge"; "primitive"; "pull0"; "pull1"; "pulldown"; "pullup"; "rcmos"; "real"; "realtime"; "reg"; "release";
        "repeat"; "rnmos"; "rpmos"; "rtran"; "rtranif0"; "rtranif1"; "scalared"; "small"; "specify"; "specparam";
        "strong0"; "strong1"; "supply0"; "supply1"; "table"; "task"; "time"; "tran"; "tranif0"; "tranif1"; "tri";
        "tri0"; "tri1"; "triand"; "trior"; "trireg"; "vectored"; "wait"; "wand"; "weak0"; "weak1"; "while"; "wire";
        "wor"; "xnor"; "xor"; "automatic"; "cell"; "config"; "design"; "endconfig"; "endgenerate"; "generate";
        "genvar"; "incdir"; "include"; "instance"; "liblist"; "library"; "localparam"; "noshowcancelled";
        "pulsestyle_ondetect"; "pulsestyle_onevent"; "showcancelled"; "signed"; "unsigned"; "use"; "uwire"; "alias";
        "always_comb"; "always_ff"; "always_latch"; "assert"; "assume"; "before"; "bind"; "bins"; "binsof"; "bit";
        "break"; "byte"; "chandle"; "class"; "clocking"; "const"; "constraint"; "context"; "continue"; "cover";
        "covergroup"; "coverpoint"; "cross"; "dist"; "do"; "endclass"; "endclocking"; "endgroup"; "endinterface";
        "endpackage"; "endprogram"; "endproperty"; "endsequence"; "enum"; "expect"; "export"; "extends"; "extern";
        "final"; "first_match"; "foreach"; "forkjoin"; "iff"; "ignore_bins"; "illegal_bins"; "import"; "inside";
        "int"; "interface"; "intersect"; "join_any"; "join_none"; "local"; "logic"; "longint"; "matches"; "modport";
        "new"; "null"; "package"; "packed"; "priority"; "program"; "property"; "protected"; "pure"; "rand"; "randc";
        "randcase"; "randsequence"; "ref"; "return"; "sequence"; "shortint"; "shortreal"; "solve"; "static"; "string";
        "struct"; "super"; "tagged"; "this"; "throughout"; "timeprecision"; "timeunit"; "type"; "typedef"; "union";
        "unique"; "var"; "virtual"; "void"; "wait_order"; "wildcard"; "with"; "within"; "accept_on"; "checker";
        "endchecker"; "eventually"; "global"; "implies"; "let"; "nexttime"; "reject_on"; "restrict"; "s_always";
        "s_eventually"; "s_nexttime"; "s_until"; "s_until_with"; "strong"; "sync_accept_on"; "sync_reject_on";
        "unique0"; "until"; "until_with"; "untyped"; "weak"; "implements"; "interconnect"; "nettype"; "sof"
      ]) then "`error ""reserved name: " ++ s ++ """ "
      else if andb (orb (isalpha c) (Z.eqb c "_"%char)) (valid_ident_tail s')
           then "" else "`error ""invalid name: " ++ s ++ """ "
    end.

  Definition valid_array (t' : type) : string :=
    if (type.size t' <=? 0)%N then "`error ""array element must have positive size"" " else "".

  Definition valid_type_shallow (t : type) : string :=
    match t with
    | type.Unit => ""
    | type.Bits sz => if (sz <? 0)%N then "`error ""bitwidth must be nonnegative"" " else ""
    | type.Pair a b =>
        if (type.size a <=? 0)%N || (type.size b <=? 0)%N then "`error ""pair component must have positive size"" " else ""
    | type.Either a b =>
        if (type.size a <=? 0)%N && (type.size b <=? 0)%N then "`error ""either components cannot be both zero-sized"" " else ""
    | type.Struct name _ => valid_ident name
    | type.Array t' sz => valid_array t'
    end.

  Definition valid_field (n : string) (t' : type) : string :=
    if (type.size t' <=? 0)%N then "`error ""field " ++ n ++ " must have positive size"" " else "".

  Fixpoint pp_type' (t : type) (dims : string) : string :=
    valid_type_shallow t ++
    match t with
    | type.Unit => "unit" ++ dims
    | type.Bits sz => "bit" ++ dims ++ "["++pp_N (sz - 1)++":0]"
    | type.Pair a b => "Pair#("++pp_type' a ""++", "++pp_type' b ""++")::t" ++ dims
    | type.Either a b => "Either#("++pp_type' a ""++", "++pp_type' b ""++")::t" ++ dims
    | type.Struct name _ => name ++ dims
    | type.Array t' sz => pp_type' t' (dims ++ "["++pp_nat sz++"-1:0]")
    end.

  Definition pp_type (t : type) : string := pp_type' t "".

  Definition pp_struct nts :=
    "struct packed { "++ fold_right (fun '(n, t') acc => valid_field n t' ++ valid_ident n ++ pp_type t'++" "++n++"; "++acc) "" nts++ "}".

  Definition pp_typedef name nts :=
    fold_right (fun '(n, t') acc => valid_field n t' ++ acc) "" nts ++
    "typedef "++pp_struct nts++" "++name++";"++LF.

  Fixpoint pp_typedefs (ts : list type) : string :=
    match ts with
    | nil => ""
    | type.Struct n nts :: ts => pp_typedef n nts ++ pp_typedefs ts
    | _ :: ts => pp_typedefs ts
    end.

  Fixpoint pp_const {t : type} : type.interp t -> string :=
    match t return type.interp t -> string with
    | type.Unit => fun b => "tt"
    | type.Bits sz => fun v => pp_N sz++"'d"++pp_Z (bv_unsigned v)
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
          | Vector.nil => ""
          | @Vector.cons _ hd 0 tl => @pp_const t' hd
          | @Vector.cons _ hd (S n') tl => pp_vec tl++", "++@pp_const t' hd
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
    | @unop.Resize false n m => pp_N m ++ "'($unsigned("++e1_str++"))"
    | @unop.Resize true n m => "$unsigned(" ++ pp_N m ++ "'($signed("++e1_str++")))"
    | @unop.Left l r => "Either#("++pp_type l++", "++pp_type r++")::left("++e1_str++")"
    | @unop.Right l r => "Either#("++pp_type l++", "++pp_type r++")::right("++e1_str++")"
    | @unop.Slice _ s l => pp_N l ++ "'((" ++ e1_str ++ ") >> " ++ pp_N s ++ ")"
    end.

  Definition pp_binop {t1 t2 t3} (op : binop t1 t2 t3) (e1_str e2_str : string) : string :=
    match op with
    | @binop.Add n => "("++e1_str++" + "++e2_str++")"
    | @binop.Sub n => "("++e1_str++" - "++e2_str++")"
    | @binop.And n => "("++e1_str++" & "++e2_str++")"
    | @binop.Or n => "("++e1_str++" | "++e2_str++")"
    | @binop.Xor n => "("++e1_str++" ^ "++e2_str++")"
    | @binop.Slu n => "("++e1_str++" << "++e2_str++")"
    | @binop.Sru n => "("++e1_str++" >> "++e2_str++")"
    | @binop.Srs n => "$unsigned(($signed("++e1_str++") >>> "++e2_str++"))"
    | @binop.Mul n m z => pp_N z ++ "'(" ++e1_str++" * "++e2_str++")"
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
    | @binop.App sz n m => pp_N sz ++ "'({"++e2_str++", "++e1_str++"})"
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

  Local Open Scope string_scope.

  Definition ppRaw {a b} fns :=
    "// Generated from Rocq by Quartz (experimental prototype version)
typedef enum bit { tt } unit; // no zero-size types in SystemVerilog :/

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
  Definition pp {a b} fns :=
    (match b with type.Unit => "`error ""top-level return type cannot be unit"" " ++ LF | _ => "" end) ++
    @ppRaw a b (fns.rmap (fun _ e => expr.unresizesame (expr.unapp0l (expr.unapp0r e))) (fun _ => id) (fun a b => id) fns).
End sv.
