From Ltac2 Require Import Ltac2.
Module UConstr := Constr.Unsafe.

Local Ltac2 Type collect_consts_state := {
  mutable lets : (ident option * constr * Constr.Binder.relevance * constr) list;
  mutable m : (constant, int) FMap.t;
  mutable n : int;
}.
Ltac2 collect_consts (filter : constant -> instance -> bool) (e : constr) :=
  let st := { lets := []; m := FMap.empty FSet.Tags.constant_tag; n := 0 } in
  let rec collect (e : constr) : unit :=
    match UConstr.kind e with
    | UConstr.Constant c i =>
      if FMap.mem c (st.(m)) then () else
      if Bool.neg (filter c i) then () else (
      match Control.case (fun () => Std.eval_cbv { RedFlags.none with Std.rConst := [Std.ConstRef c]} e) with
      | Err _ => () | Val (body, _) =>
      if Constr.equal e body then () else (
      st.(m) := FMap.add c (-1) (st.(m));
      let rec last l := match l with [] => None | x :: [] => (Some x) | _x :: xs => last xs end in
      let name := last (Env.path (Std.ConstRef c)) in
      let typ := Constr.type e in
      collect typ; collect body;
      let relevance := if Constr.equal (Std.eval_hnf (Constr.type typ)) 'SProp then Constr.Binder.Irrelevant else Constr.Binder.Relevant in (* Question: is this line always correct? *)
      st.(lets) := ((name, typ, relevance, body) :: st.(lets));
      st.(m) := FMap.add c (st.(n)) (st.(m));
      st.(n) := Int.add (st.(n)) 1
      )end)
    | _ => UConstr.iter collect e
    end in
  collect e; (st.(lets), st.(m), st.(n)).

Ltac2 rec replace_consts (m : (constant, int) FMap.t) (n : int) (e : constr) : constr :=
  match UConstr.kind e with
  | UConstr.Constant c _ =>
    match FMap.find_opt c m with
    | Some i => UConstr.make (UConstr.Rel (Int.sub n i))
    | None => e
    end
  | _ => UConstr.map_with_binders (fun n _ => Int.add n 1) (fun n c => replace_consts m n c) n e
  end.

Ltac2 let_lift_constants (filter : constant -> instance -> bool) (e : constr) : constr :=
  let (lets, m, n) := collect_consts filter e in
  snd (List.fold_left (fun (n, cont) (name_opt, typ, relevance, body) =>
    let typ := replace_consts m n typ in
    let body := replace_consts m n body in
    let binder := Constr.Binder.unsafe_make name_opt relevance typ in
    (Int.sub n 1, UConstr.make (UConstr.LetIn binder body cont))
    ) (Int.sub n 1, replace_consts m n e) lets).

Ltac2 let_lift_all_constants e := let_lift_constants (fun _ _ => true) e.

(*
Module Private_test.
Definition n : nat. exact O. Defined.
Ltac2 Eval let_lift_all_constants 'n.
Definition A : Type := nat.
Definition a : A. exact O. Defined.
Ltac2 Eval let_lift_all_constants 'a.
Definition B : Set := nat.
Definition b : B. exact O. Defined.
Ltac2 Eval let_lift_all_constants 'b.
Definition base_val := 42.
Definition t := nat.
Definition m : t. exact O. Qed.
Definition base_2  x  (y : nat) : nat := x + base_val * y.
Ltac2 Eval let_lift_all_constants 'base_2.
Definition base_2'  x  (y : t) : nat := x + base_val * y.
Ltac2 Eval let_lift_all_constants 'base_2'.
From Stdlib Require Import Zmod.
Check (eq_refl : Z.div_eucl = ltac2:(let e := let_lift_all_constants 'Z.div_eucl in exact $e)).
End Private_test.
*)
