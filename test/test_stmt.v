From Stdlib Require Import BinInt Bits String List.
Require Import quartz.lang.Syntax. Import type.
Import (notations) type expr eexpr stmt.
Local Open Scope string_scope.

Definition test_stmt_body {var fn} : stmt.stmt var fn (("a", Bits 32)::("b", Bits 32)::nil) :=
  stmt.LetMut "v" (fun _ => expr.Const (t:=Bits 32) (bits.of_Z 32 10)) (
    stmt.Seq
      (@stmt.Upd _ _ (Bits 32) nil "v" typeWithHole.HOLE (("a", Bits 32)::("b", Bits 32)::nil)
        (fun _ => eq_refl)
        (fun _ => expr.tt)
        (fun _ => expr.Const (t:=Bits 32) (bits.of_Z 32 42)))
      (@stmt.Upd _ _ (Bits 32) (("v", Bits 32)::("a", Bits 32)::nil) "b" typeWithHole.HOLE nil
        (fun _ => eq_refl)
        (fun _ => expr.tt)
        (fun env => expr.Get (@typeWithHole.Struct "" nil "v" typeWithHole.HOLE (("a", Bits 32)::("b", Bits 32)::nil) (fun _ => eq_refl)) (expr.Var env) expr.tt))
  ).

Definition test_stmt_inner {var fn} : fns.fns var fn Unit (Bits 32) :=
  @fns.LetStmt var fn
    Unit
    (Bits 32)
    (("a", Bits 32)::nil)
    (("b", Bits 32)::nil)
    "test_stmt_stmt" "arg"
    test_stmt_body (fun f_inner =>
  fns.Ret "test_stmt_inner" "arg" (fun va =>
    eexpr.Let "dummy_in" (expr.Const (t:=type.Struct "test_stmt_stmt_in" (("a", Bits 32)::nil)) (bits.of_Z 32 0, Datatypes.tt)) (fun vin =>
    eexpr.Let "res" (expr.Call f_inner (expr.Var vin)) (fun res =>
      eexpr.Ret (expr.Get (@typeWithHole.Struct "test_stmt_stmt_out" nil "b" typeWithHole.HOLE nil (fun _ => eq_refl)) (expr.Var res) expr.tt)
  )))).

Definition test_stmt {var fn} := @test_stmt_inner var fn.
