Require Coq.Strings.String.
Require Import Ltac2.Ltac2. Import Ltac2.Option Ltac2.Constr Ltac2.Constr.Unsafe.

Module Import Private.
  Import Coq.Lists.List Coq.Strings.Ascii BinNat.
  Local Ltac2 rec list_constr_of_constr_list xs :=
    match! xs with cons ?x ?xs => x :: list_constr_of_constr_list xs | nil => [] end.
  Local Definition f : ltac:(do 256 refine (ascii->_); exact unit) := ltac:(intros;exact tt).
  Definition app : unit := ltac2:(
    let args := eval cbv in (map (fun n => ascii_of_N (N.of_nat n)) (seq 0 256)) in
    refine (make (App 'f (Array.of_list (list_constr_of_constr_list args))))).
End Private.

Ltac2 constr_string_of_string (s : string) :=
  let asciis := match kind (eval red in app) with App _ x => x | _ => Control.throw No_value end in
  let scons := 'String.String in
  let l := String.length s in
  let rec f i :=
    if Int.equal i l then 'String.EmptyString else
    make (App scons (Array.of_list [Array.get asciis (Char.to_int (String.get s i)); f (Int.add i 1)])) in
  f 0.
(* Ltac2 Eval constr_string_of_string "hello world". *)

Ltac2 constr_string_of_ident (i : ident) := constr_string_of_string (Ident.to_string i).
