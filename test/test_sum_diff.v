From Stdlib Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr stmt.
Local Open Scope string_scope.

(* TODO: in "=" Notation, replace reify_field with something that takes a string, then remove this struct *)
Record SumDiffEnv := { x : bits 32; y : bits 32; sum : bits 32; diff : bits 32 }.

Local Fixpoint takeWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | x :: xs => if p x then x :: takeWhile p xs else nil
  end.

(* TODO: would it work to make notation "#" check whether the variable passed to it is a `var`, and if not, convert the argument to string and act like "!!"? Or do we want something else anyway? *)
Local Notation "!! x" := ((fun _ => let MUTVAR := x in _ )) (at level 0).
Local Notation "!! x" := ((let MUTVAR := x in _ )) (in custom quartz_expr at level 0, x constr).

Definition sum_diff_body {var fn} : stmt.stmt var fn _ := ltac:(refine (
  quartz_stmt:({
    sum = (!! "x") + (!! "y");
    if (!! "x") == 32'd0 then
      { sum = (!! "y") + 32 'd 0 * !! "sum" }
    else
      { mut z := (!! "x") in
        skip } ;
    diff = (!! "x") - !! "y"
  }));
  (* Ltac to elaborate references to local variables. TODO: find `MUTVAR` using a type annotation like is used to find `locals`, put this tactic inside a notation for defining a quartz_stmt function *)
  match goal with
  | locals : stmt.locals (Struct_ ?s) |- _ =>
    let s := eval cbn [typeWithHole.plug] in s in
    let field := eval cbv in MUTVAR in
    let l := eval cbn in (takeWhile (fun '(n, t) => negb (String.eqb n field)) s) in
    let r := eval cbn in (skipn (S (length l)) s) in
    refine (expr.Get (@typeWithHole.Struct "" l field typeWithHole.HOLE r (fun _ => eq_refl)) (expr.Var locals) expr.tt)
  end;
  exact l).

  (* TODO: convert the belwo to use notations once improved *)
Definition test_sum_diff_inner {var fn} : fns.fns var fn Unit (Bits 64) :=
  @fns.LetStmt var fn
    Unit
    (Bits 64)
    (("x", Bits 32)::("y", Bits 32)::nil)
    (("sum", Bits 32)::("diff", Bits 32)::nil)
    "sum_diff_stmt" "arg"
    sum_diff_body (fun f_sd =>
  fns.Ret "test_sum_diff_inner" "arg" (fun va =>
    eexpr.Let "dummy_in" (expr.Const (t:=type.Struct "sum_diff_stmt_in" (("x", Bits 32)::("y", Bits 32)::nil)) (bits.of_Z 32 10, (bits.of_Z 32 5, Datatypes.tt))) (fun vin =>
    eexpr.Let "res" (expr.Call f_sd (expr.Var vin)) (fun res =>
      eexpr.Let "s" (expr.Get (@typeWithHole.Struct "sum_diff_stmt_out" nil "sum" typeWithHole.HOLE (("diff", Bits 32)::nil) (fun _ => eq_refl)) (expr.Var res) expr.tt) (fun s =>
      eexpr.Let "d" (expr.Get (@typeWithHole.Struct "sum_diff_stmt_out" (("sum", Bits 32)::nil) "diff" typeWithHole.HOLE nil (fun _ => eq_refl)) (expr.Var res) expr.tt) (fun d =>
        eexpr.Ret (expr.Binop binop.App (expr.Var s) (expr.Var d))
      )))))).

Definition test_sum_diff {var fn} := @test_sum_diff_inner var fn.
