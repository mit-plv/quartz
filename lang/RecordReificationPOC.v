From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind.
Module UConstr := Constr.Unsafe.

Module type.
  Inductive type :=
  | Unit
  | Bool
  | Pair (t1 t2: type).

  Fixpoint type_denote tau : Type :=
    match tau with
    | Unit => unit
    | Bool => bool
    | Pair t1 t2 => (type_denote t1) * (type_denote t2)
    end.

  Inductive typeWithHole :=
  | HOLE
  | PairL (t1 : typeWithHole) (t2: type)
  | PairR (t1 : type) (t2: typeWithHole)
  | Array (sz: nat) (idx: nat) (t: typeWithHole).

  Ltac2 Type exn ::= [ ReifyUnknown (constr) ].

  Ltac2 rec reify t :=
    lazy_match! t with
    | prod ?t1 ?t2 =>
        let rt1 := reify t1 in
        let rt2 := reify t2 in
        constr:(type.Pair $rt1 $rt2)
    | bool => 'type.Bool
    | unit => 'Unit
    | _ => Control.throw (ReifyUnknown t)
    end.

  Ltac2 reify_record_fields inst arrproj :=
    Array.fold_left (fun acc pp =>
      (* let ind := Proj.ind pp in *)
      (* let i := Proj.index pp in *)
      match Proj.to_constant pp with
      | Some c =>
          let e := UConstr.make (UConstr.Constant c inst) in
          let t := match UConstr.kind (Constr.type e) with UConstr.Prod _ t => t | _ => 'Empty_set end in
          let rt := type.reify t in
          match acc with
          | Some acc => Some constr:(Pair $acc $rt)
          | _ => Some rt
          end
      | _ => Some 'Empty_set
      end
    ) None arrproj.

  Ltac2 reify_record r :=
    match UConstr.kind r with
    | UConstr.Ind ind inst =>
      match Ind.get_projections (Ind.data ind) with
      | Some arrproj => reify_record_fields inst arrproj
      | _ => None
      end
    | _ => None
    end.

  Ltac2 lower_record_value v :=
    match UConstr.kind (Constr.type v) with
    | UConstr.Ind ind inst =>
      match Ind.get_projections (Ind.data ind) with
      | Some arrproj => 
          Array.fold_left (fun acc p =>
            match Proj.to_constant p with
            | Some c =>
                let e := UConstr.make (UConstr.Constant c inst) in
                let e := constr:($e $v) in
                match acc with
                | Some acc => Some constr:(pair $acc $e)
                | _ => Some e
                end
            | None => None
            end) None arrproj
      | _ => None
      end
    | _ => None
    end.

  Ltac2 reify_projection p0c :=
    match UConstr.kind p0c with
    | UConstr.Constant c0 inst =>
      match Proj.of_constant c0 with
      | Some p0 =>
        let ind := Proj.ind p0 in
        let n := Proj.index p0 in
        match Ind.get_projections (Ind.data ind) with
        | Some arrproj =>
            let before := reify_record_fields inst (Array.sub arrproj 0 n) in
            Array.fold_left (fun acc pp =>
              match Proj.to_constant pp with
              | Some c =>
                  let e := UConstr.make (UConstr.Constant c inst) in
                  let t := match UConstr.kind (Constr.type e) with UConstr.Prod _ t => t | _ => 'Empty_set end in
                  let rt := type.reify t in
                  constr:(PairL $acc $rt)
              | _ => 'Empty_set
              end
            )
            (match before with
             | Some before => constr:(PairR $before HOLE)
             | _ => 'HOLE (* TODO: recurse here for nested lvalue? *)
             end)
            (Array.sub arrproj (Int.add 1 n) (Int.sub (Array.length arrproj) (Int.add 1 n)))
        | _ => 'Empty_set
        end
      | _ =>
        'Empty_set
      end
    | _ =>
      'Empty_set
    end.
End type.

Declare Scope rtype_scope.
Delimit Scope rtype_scope with rtype.
Infix "*" := type.Pair : rtype_scope.

Declare Scope ltype_scope.
Delimit Scope ltype_scope with ltype.
Infix "* >" := type.PairR : ltype_scope.
Infix "*" := type.PairL : ltype_scope.

Set Primitive Projections.

Module example.

Record r := { a : bool ; b : (unit * bool) ; c : unit }.

Ltac2 Eval type.reify_record 'r.
Ltac2 Eval type.reify_projection 'b.
Ltac2 Eval type.reify_projection 'a.
Ltac2 Eval type.reify_projection 'c.
Definition lower_r (v : r) :=
  ltac2:(match type.lower_record_value &v with
         | Some t => exact $t | _ => () end).
Print lower_r.

Definition spec_of_f (P : r -> Prop) (Q : r -> r -> Prop) (f_impl : _ -> _) :=
  forall x, P x ->
  let y_computed := f_impl (lower_r x) in
  exists y, y_computed = lower_r y /\
  Q x y.

End example.
