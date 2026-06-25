open Ltac2_plugin.Tac2ffi
open Ltac2_plugin.Tac2externals
open Ltac2_plugin.Tac2expr
open Names
open EConstr

module CMap = Map.Make(Constant.CanOrd)
module IMap = Map.Make(Int)

type const_item = {
  name : Id.t;
  typ : EConstr.t;
  body : EConstr.t;
}



let rec skipn n l = match n, l with 0, _ -> l | _, [] -> [] | n, _::xs -> skipn (n - 1) xs

let is_opaque_constant c =
  let s = Constant.to_string c in
  String.starts_with ~prefix:"Coq." s ||
  String.starts_with ~prefix:"Stdlib." s ||
  String.starts_with ~prefix:"Corelib." s ||
  String.starts_with ~prefix:"quartz.lang.Syntax." s

let get_transparent_def env c u =
  let cb = Environ.lookup_constant c env in
  match cb.Declarations.const_body with
  | Declarations.Def c_body ->
      let c_val = EConstr.of_constr c_body in
      Some (Vars.subst_instance_constr u c_val)
  | _ -> None

let collect_consts env sigma e =
  let lets = ref [] in
  let visited = ref CMap.empty in
  let counter = ref 0 in

  let rec collect e =
    match EConstr.kind sigma e with
    | Const (c, u) ->
        if CMap.mem c !visited || is_opaque_constant c then ()
        else begin
          visited := CMap.add c (-1) !visited;
          match get_transparent_def env c u with
          | Some body ->
              let ty = Retyping.get_type_of env sigma e in
              collect ty;
              collect body;
              let idx = !counter in
              counter := idx + 1;
              visited := CMap.add c idx !visited;
              let name = Constant.label c |> Label.to_id in
              lets := { name; typ = ty; body } :: !lets
          | None -> ()
        end
    | _ -> EConstr.iter sigma collect e
  in
  collect e;
  (List.rev !lets, !visited)

let rec replace_consts sigma m limit d e =
  match EConstr.kind sigma e with
  | Const (c, _u) ->
      begin match CMap.find_opt c m with
      | Some i when i >= 0 && i < limit ->
          mkRel (limit - i + d)
      | _ -> e
      end
  | _ ->
      EConstr.map_with_binders sigma (fun d -> d + 1)
        (fun d' sub -> replace_consts sigma m limit d' sub) d e

let deglob env sigma e =
  let (lets, m) = collect_consts env sigma e in
  let n_total = List.length lets in
  let limit = ref n_total in
  let e_replaced = replace_consts sigma m n_total 0 e in
  List.fold_right (fun item cont ->
    let n = !limit in
    limit := n - 1;
    let typ_replaced = replace_consts sigma m (n - 1) 0 item.typ in
    let body_replaced = replace_consts sigma m (n - 1) 0 item.body in
    let annot = Context.make_annot (Name.Name item.name) EConstr.ERelevance.relevant in
    mkLetIn (annot, body_replaced, typ_replaced, cont)
  ) lets e_replaced

(* Phase 3: unnest_lets *)

let rec swap_rels sigma k c =
  match EConstr.kind sigma c with
  | Rel i ->
      if i = k + 1 then mkRel (k + 2)
      else if i = k + 2 then mkRel (k + 1)
      else c
  | _ ->
      EConstr.map_with_binders sigma (fun k' -> k' + 1)
        (fun k' sub -> swap_rels sigma k' sub) k c

let find_letin_index sigma args =
  let len = Array.length args in
  let rec loop i =
    if i = len then None
    else match EConstr.kind sigma args.(i) with
    | LetIn _ -> Some i
    | _ -> loop (i + 1)
  in
  loop 0

let rec unnest_letin_aux sigma annot_x v ty_x c k =
  match EConstr.kind sigma v with
  | LetIn (annot_y, a, ty_y, b) ->
      let inner = unnest_letin_aux sigma annot_x b ty_x c (k + 1) in
      mkLetIn (annot_y, a, ty_y, inner)
  | _ ->
      if k = 0 then
        mkLetIn (annot_x, v, ty_x, c)
      else
        let ty_x' = Vars.liftn k 1 ty_x in
        let c' = Vars.liftn k 2 c in
        mkLetIn (annot_x, v, ty_x', c')

let unnest_letin sigma annot_x ty_x v c =
  unnest_letin_aux sigma annot_x v ty_x c 0

let rec unnest_app sigma head args =
  match EConstr.kind sigma head with
  | LetIn (annot_y, a, ty_y, b) ->
      let args' = Array.map (Vars.liftn 1 1) args in
      mkLetIn (annot_y, a, ty_y, unnest_app sigma b args')
  | _ ->
      match find_letin_index sigma args with
      | Some i ->
          let arg_i = args.(i) in
          begin match EConstr.kind sigma arg_i with
          | LetIn (annot_y, a, ty_y, b) ->
              let head' = Vars.liftn 1 1 head in
              let args' = Array.mapi (fun j arg ->
                if j = i then b else Vars.liftn 1 1 arg
              ) args in
              mkLetIn (annot_y, a, ty_y, unnest_app sigma head' args')
          | _ -> assert false
          end
      | None ->
          mkApp (head, args)

let rec unnest_binder sigma mk_binder annot_x body ty_x =
  match EConstr.kind sigma body with
  | LetIn (annot_y, a, ty_y, b_body) ->
      if Vars.noccurn sigma 1 a && Vars.noccurn sigma 1 ty_y then
        let a' = Vars.liftn (-1) 1 a in
        let ty_y' = Vars.liftn (-1) 1 ty_y in
        let ty_x' = Vars.liftn 1 1 ty_x in
        let annot_x' = Context.make_annot annot_x.Context.binder_name annot_x.Context.binder_relevance in
        let annot_y' = Context.make_annot annot_y.Context.binder_name annot_y.Context.binder_relevance in
        let b_body' = swap_rels sigma 0 b_body in
        mkLetIn (annot_y', a', ty_y', unnest_binder sigma mk_binder annot_x' b_body' ty_x')
      else
        mk_binder annot_x ty_x body
  | _ ->
      mk_binder annot_x ty_x body

let rec unnest_cast_aux sigma kind_c val_ ty k =
  match EConstr.kind sigma val_ with
  | LetIn (annot_y, a, ty_y, b) ->
      let inner = unnest_cast_aux sigma kind_c b ty (k + 1) in
      mkLetIn (annot_y, a, ty_y, inner)
  | _ ->
      if k = 0 then mkCast (val_, kind_c, ty)
      else mkCast (val_, kind_c, Vars.liftn k 1 ty)

let unnest_cast sigma kind_c val_ ty =
  unnest_cast_aux sigma kind_c val_ ty 0

let rec unnest_proj sigma p r c =
  match EConstr.kind sigma c with
  | LetIn (annot_y, a, ty_y, b) ->
      mkLetIn (annot_y, a, ty_y, unnest_proj sigma p r b)
  | _ -> mkProj (p, r, c)

let rec unnest_case_aux sigma ci u pms p iv scrut branches k =
  match EConstr.kind sigma scrut with
  | LetIn (annot_y, a, ty_y, b) ->
      let inner = unnest_case_aux sigma ci u pms p iv b branches (k + 1) in
      mkLetIn (annot_y, a, ty_y, inner)
  | _ ->
      if k = 0 then mkCase (ci, u, pms, p, iv, scrut, branches)
      else
        let p' = match p with ((nas, ty), r) -> ((nas, Vars.liftn k 1 ty), r) in
        let branches' = Array.map (fun (nas, br) -> (nas, Vars.liftn k 1 br)) branches in
        mkCase (ci, u, pms, p', iv, scrut, branches')

let unnest_case sigma ci u pms p iv scrut branches =
  unnest_case_aux sigma ci u pms p iv scrut branches 0

let rec unnest_lets sigma e =
  match EConstr.kind sigma e with
  | LetIn (annot, v, ty, c) ->
      let v' = unnest_lets sigma v in
      let c' = unnest_lets sigma c in
      unnest_letin sigma annot ty v' c'
  | App (head, args) ->
      if isConst sigma head then
        begin match EConstr.kind sigma head with
        | Const (c, _) when Constant.to_string c = "Stdlib.Strings.String.String" -> e
        | _ ->
            let head' = unnest_lets sigma head in
            let args' = Array.map (unnest_lets sigma) args in
            unnest_app sigma head' args'
        end
      else
        let head' = unnest_lets sigma head in
        let args' = Array.map (unnest_lets sigma) args in
        unnest_app sigma head' args'
  | Lambda (annot, ty, body) ->
      let body' = unnest_lets sigma body in
      unnest_binder sigma (fun b ty_b body_b -> mkLambda (b, ty_b, body_b)) annot body' ty
  | Prod (annot, ty, body) ->
      let body' = unnest_lets sigma body in
      unnest_binder sigma (fun b ty_b body_b -> mkProd (b, ty_b, body_b)) annot body' ty
  | Cast (val_, kind_c, ty) ->
      let val' = unnest_lets sigma val_ in
      unnest_cast sigma kind_c val' ty
  | Proj (p, r, c) ->
      let c' = unnest_lets sigma c in
      unnest_proj sigma p r c'
  | Case (ci, u, pms, p, iv, scrut, branches) ->
      let scrut' = unnest_lets sigma scrut in
      let branches' = Array.map (fun (nas, br) -> (nas, unnest_lets sigma br)) branches in
      unnest_case sigma ci u pms p iv scrut' branches'
  | _ ->
      EConstr.map sigma (unnest_lets sigma) e

(* Phase 4: monomorphize *)

type let_item = {
  annot : (Name.t, EConstr.ERelevance.t) Context.pbinder_annot;
  val_ : EConstr.t;
  ty : EConstr.t;
}

let rec peel_lets sigma c =
  match EConstr.kind sigma c with
  | LetIn (annot, v, ty, body) ->
      let (lets, final) = peel_lets sigma body in
      ({ annot; val_ = v; ty } :: lets, final)
  | _ -> ([], c)

let rec count_lets sigma c =
  match EConstr.kind sigma c with
  | LetIn (_, _, _, body) -> 1 + count_lets sigma body
  | _ -> 0

let rec is_acceptable sigma k d c =
  match EConstr.kind sigma c with
  | Rel i ->
      if i > d && i - d <= k then false
      else true
  | _ ->
      let ok = ref true in
      EConstr.iter_with_binders sigma (fun d -> d + 1)
        (fun d' sub -> if not (is_acceptable sigma k d' sub) then ok := false) d c;
      !ok

let rec longest_acceptable_prefix sigma k args =
  match args with
  | [] -> []
  | x :: xs ->
      if is_acceptable sigma k 0 x then
        x :: longest_acceptable_prefix sigma k xs
      else []

let is_leaf_or_fn_fn sigma t =
  match EConstr.kind sigma t with
  | Rel _ | Var _ | Const _ | Construct _ | Sort _ | Int _ | Float _ | String _ -> true
  | App (f, _) when isConst sigma f -> true
  | _ -> false

let rec lambda_to_let sigma c =
  match EConstr.kind sigma c with
  | App (f, args) ->
      let f' = lambda_to_let sigma f in
      let args' = Array.map (lambda_to_let sigma) args in
      begin match EConstr.kind sigma f' with
      | Lambda (b, _ty, body) ->
          let arg0 = args'.(0) in
          let remaining = Array.sub args' 1 (Array.length args' - 1) in
          if is_leaf_or_fn_fn sigma arg0 then
            let body' = Vars.substnl [arg0] 0 body in
            let new_app = if Array.length remaining = 0 then body' else mkApp (body', remaining) in
            lambda_to_let sigma new_app
          else
            let shifted_remaining = Array.map (Vars.liftn 1 1) remaining in
            let inner_app = if Array.length remaining = 0 then body else mkApp (body, shifted_remaining) in
            let reduced_inner = lambda_to_let sigma inner_app in
            mkLetIn (b, arg0, _ty, reduced_inner)
      | LetIn (b, v, ty, body) ->
          let shifted_args = Array.map (Vars.liftn 1 1) args' in
          let inner_app = mkApp (body, shifted_args) in
          let reduced_inner = lambda_to_let sigma inner_app in
          mkLetIn (b, v, ty, reduced_inner)
      | _ ->
          if Array.length args' = 0 then f' else mkApp (f', args')
      end
  | LetIn (b, v, ty, body) ->
      mkLetIn (b, lambda_to_let sigma v, ty, lambda_to_let sigma body)
  | Lambda (b, ty, body) ->
      mkLambda (b, ty, lambda_to_let sigma body)
  | _ -> EConstr.map sigma (lambda_to_let sigma) c

let rec remove_unused_lets sigma c =
  match EConstr.kind sigma c with
  | LetIn (annot, v, ty, body) ->
      let body' = remove_unused_lets sigma body in
      if Vars.noccurn sigma 1 body' then
        Vars.liftn (-1) 1 body'
      else
        mkLetIn (annot, v, ty, body')
  | _ -> c

let dependency_level sigma n c =
  let max_dep = ref (-1) in
  let rec check d sub =
    match EConstr.kind sigma sub with
    | Rel i when i > d ->
        let idx = i - d - 1 in
        if idx < n then
          let level = n - 1 - idx in
          if level > !max_dep then max_dep := level
    | _ -> EConstr.iter_with_binders sigma (fun d -> d + 1) check d sub
  in
  check 0 c;
  !max_dep

let map_rel n total_binders birth_lets d i =
  if i <= d then i
  else
    let idx = i - d - 1 in
    if idx < n then
      let level = n - 1 - idx in
      let birth = birth_lets.(level) in
      total_binders - birth + d
    else
      idx + (total_binders - n) + 1 + d

let rec convert_and_replace sigma n total_binders birth_lets birth_specs d c =
  match EConstr.kind sigma c with
  | Rel i ->
      if i < 0 then
        let spec_id = -i in
        begin match IMap.find_opt spec_id birth_specs with
        | Some birth -> mkRel (total_binders - birth + d)
        | None -> c
        end
      else
        mkRel (map_rel n total_binders birth_lets d i)
  | _ ->
      EConstr.map_with_binders sigma (fun d -> d + 1)
        (fun d' sub -> convert_and_replace sigma n total_binders birth_lets birth_specs d' sub) d c

let rec instantiate_type env sigma t args =
  match args with
  | [] -> t
  | arg :: args' ->
      let t_hnf = Reductionops.whd_all env sigma t in
      match EConstr.kind sigma t_hnf with
      | Prod (_b, _ty, body) ->
          instantiate_type env sigma (Vars.substnl [arg] 0 body) args'
      | _ -> mkApp (t, Array.of_list args)

let rec unnest_letin_no_shift sigma b_x v ty_x c =
  match EConstr.kind sigma v with
  | LetIn (annot, a, b_ty, b) ->
      let inner = unnest_letin_no_shift sigma b_x b ty_x c in
      mkLetIn (annot, a, b_ty, inner)
  | _ ->
      mkLetIn (b_x, v, ty_x, c)

let is_fn_ind env sigma c =
  match EConstr.kind sigma c with
  | Ind ((mutind, i_ind), _) -> (
      try
        let mib = Environ.lookup_mind mutind env in
        let oib = mib.Declarations.mind_packets.(i_ind) in
        Id.to_string oib.Declarations.mind_typename = "fn"
      with _ -> false)
  | _ -> false

let is_fn_Fn_ctor env sigma c =
  match EConstr.kind sigma c with
  | Construct (((mutind, i_ind), i_ctor), _) -> (
      try
        let mib = Environ.lookup_mind mutind env in
        let oib = mib.Declarations.mind_packets.(i_ind) in
        Id.to_string oib.Declarations.mind_typename = "fn" && i_ctor = 1
      with _ -> false)
  | _ -> false

let get_fn_args a =
  let len = Array.length a in
  (a.(len - 3), a.(len - 2), a.(len - 1))

let rec normalize_val env sigma c =
  let (h, args) = EConstr.decompose_app sigma c in
  match EConstr.kind sigma h with
  | Const (cst, u) -> (
      try
        let cb = Environ.lookup_constant cst env in
        match cb.Declarations.const_body with
        | Declarations.Def body ->
            let body_c = EConstr.of_constr body in
            let rec apply_args curr args_list =
              match args_list with
              | [] -> curr
              | a :: rest -> (
                  match EConstr.kind sigma curr with
                  | Lambda (_, _, b) -> apply_args (Vars.subst1 a b) rest
                  | _ -> mkApp (curr, Array.of_list args_list))
            in
            let res = apply_args body_c (Array.to_list args) in
            normalize_val env sigma res
        | _ -> c
      with _ -> c)
  | _ -> c

let rec strip_lambdas sigma c =
  match EConstr.kind sigma c with
  | Lambda (_, _, b) -> strip_lambdas sigma b
  | _ -> c

let rec reconstruct env sigma n lets groups birth_lets birth_specs total_binders idx final_body =
  if idx = n then
    convert_and_replace sigma n total_binders birth_lets birth_specs 0 final_body
  else
    let item = lets.(idx) in
    let t_recon = convert_and_replace sigma n total_binders birth_lets birth_specs 0 item.ty in
    let v_recon = convert_and_replace sigma n total_binders birth_lets birth_specs 0 item.val_ in
    let annot_idx = Context.make_annot item.annot.Context.binder_name item.annot.Context.binder_relevance in
    birth_lets.(idx) <- total_binders;
    let tb' = total_binders + 1 in

    let rec insert_specs specs b_specs tb =
      match specs with
      | [] ->
          reconstruct env sigma n lets groups birth_lets b_specs tb (idx + 1) final_body
      | (id, (lf, args)) :: xs ->
          let item_lf = lets.(lf) in
          let app_norm = if args = [] then item_lf.val_ else mkApp (item_lf.val_, Array.of_list args) in
          let let_norm = lambda_to_let sigma app_norm in
          let val_recon = convert_and_replace sigma n tb birth_lets b_specs 0 let_norm in
          let k = count_lets sigma val_recon in
          let tb_spec = tb + k in
          let t_f_recon = convert_and_replace sigma n tb_spec birth_lets b_specs 0 item_lf.ty in
          let conv_args = List.map (convert_and_replace sigma n tb_spec birth_lets b_specs 0) args in
          let ty_recon =
            let inst_ty = instantiate_type env sigma t_f_recon conv_args in
            let (h_v, args_v) = EConstr.decompose_app sigma val_recon in
            if is_fn_Fn_ctor env sigma h_v && Array.length args_v >= 3 then
              let (ta, tb, _) = get_fn_args args_v in
              let (h_inst, args_inst) = EConstr.decompose_app sigma inst_ty in
              if is_fn_ind env sigma h_inst && Array.length args_inst >= 3 then mkApp (h_inst, [| args_inst.(0); ta; tb |])
              else mkApp (h_inst, [| ta; tb |])
            else inst_ty
          in
          let name_str = match item_lf.annot.Context.binder_name with
          | Name id_b -> Id.to_string id_b
          | Anonymous -> "anon"
          in
          let spec_name = Id.of_string (Printf.sprintf "%s_specialization_%d" name_str id) in
          let b_spec = Context.make_annot (Name spec_name) EConstr.ERelevance.relevant in
          let b_specs' = IMap.add id tb_spec b_specs in
          let inner = insert_specs xs b_specs' (tb_spec + 1) in
          unnest_letin_no_shift sigma b_spec val_recon ty_recon inner
    in
    let inner = insert_specs groups.(idx) birth_specs tb' in
    mkLetIn (annot_idx, v_recon, t_recon, inner)

let rec monomorphize_rec env sigma iteration next_id c =
  let (lets_list, final_body) = peel_lets sigma c in
  let n = List.length lets_list in
  if n = 0 then c
  else
    let lets = Array.of_list lets_list in
    let lets_types = Array.map (fun item -> item.ty) lets in
    let specs_map = ref IMap.empty in
    let counter = ref next_id in

    let rec preprocess k sub =
      match EConstr.kind sigma sub with
      | App (f, args_arr) ->
          let args = Array.to_list args_arr in
          let res_app = match EConstr.kind sigma f with
          | Rel i when i >= k + 1 && i <= k + n ->
              let idx = i - k - 1 in
              let level = n - 1 - idx in
              let t_f = lets_types.(level) in
              if not (EConstr.isProd sigma t_f) then sub
              else
                let (_, res_ty) = EConstr.decompose_prod sigma t_f in
                let (h, _) = EConstr.decompose_app sigma res_ty in
                begin match EConstr.kind sigma h with
                | Ind ((mutind, i_ind), _) ->
                    let mib = Environ.lookup_mind mutind env in
                    let oib = mib.Declarations.mind_packets.(i_ind) in
                    if Id.to_string oib.Declarations.mind_typename <> "fn" then sub
                    else
                      let acc_args = longest_acceptable_prefix sigma k args in
                      if acc_args = [] then sub
                      else
                        let shifted = List.map (Vars.liftn (-k) 1) acc_args in
                        let local = match IMap.find_opt level !specs_map with Some l -> l | None -> [] in
                        let id = match List.find_opt (fun (_, s) -> List.equal (EConstr.eq_constr sigma) s shifted) local with
                        | Some (id, _) -> id
                        | None ->
                            let id = !counter in
                            counter := id + 1;
                            specs_map := IMap.add level ((id, shifted) :: local) !specs_map;
                            id
                        in
                        let sentinel = mkRel (-id) in
                        let rem = skipn (List.length acc_args) args in
                        if rem = [] then sentinel else mkApp (sentinel, Array.of_list rem)
                | _ -> sub
                end
          | _ -> sub
          in
          if EConstr.eq_constr sigma res_app sub then
            EConstr.map_with_binders sigma (fun k' -> k' + 1) preprocess k sub
          else
            EConstr.map_with_binders sigma (fun k' -> k' + 1) preprocess k res_app
      | _ -> EConstr.map_with_binders sigma (fun k' -> k' + 1) preprocess k sub
    in

    let tagged_lets = Array.mapi (fun i item ->
      let v_norm = Vars.liftn (n - i) 1 item.val_ in
      let t_norm = Vars.liftn (n - i) 1 item.ty in
      { item with val_ = preprocess 0 v_norm; ty = preprocess 0 t_norm }
    ) lets in
    let tagged_final = preprocess 0 final_body in

    let flat_specs = IMap.fold (fun level local acc ->
      List.fold_left (fun acc' (id, args) -> (id, (level, args)) :: acc') acc local
    ) !specs_map [] in

    if flat_specs = [] then c
    else
      let groups = Array.make n [] in
      List.iter (fun (id, (lf, args)) ->
        let dep = List.fold_left (fun acc arg -> max acc (dependency_level sigma n arg)) (-1) args in
        let ins = max lf dep in
        groups.(ins) <- (id, (lf, args)) :: groups.(ins)
      ) flat_specs;

      let birth_lets = Array.make n 0 in
      let recon = reconstruct env sigma n tagged_lets groups birth_lets IMap.empty 0 0 tagged_final in
      let cleaned = remove_unused_lets sigma recon in
      monomorphize_rec env sigma (iteration + 1) !counter cleaned



let rmonomorphize_fast c env sigma =
  monomorphize_rec env sigma 1 1 (unnest_lets sigma (deglob env sigma c))

let fn2fns_fast bundle e env sigma =
  let (var_top, b_args) = EConstr.decompose_app sigma bundle in
  let target_fn = b_args.(0) in
  let c_fns_Let = b_args.(1) in
  let c_fns_Ret = b_args.(2) in
  let c_true = b_args.(3) in
  let c_false = b_args.(4) in
  let c_Ascii = b_args.(5) in
  let c_String = b_args.(6) in
  let c_EmptyString = b_args.(7) in
  let top_name_str = b_args.(8) in
  let c_expr_Var = b_args.(9) in
  let c_expr_Call = b_args.(10) in
  let c_eexpr_Ret = b_args.(11) in

  let is_fn_ind c =
    match EConstr.kind sigma c with
    | Ind ((mutind, i_ind), _) -> (
        try
          let mib = Environ.lookup_mind mutind env in
          let oib = mib.Declarations.mind_packets.(i_ind) in
          Id.to_string oib.Declarations.mind_typename = "fn"
        with _ -> false)
    | _ -> false
  in
  let is_fn_Fn_ctor c = is_fn_Fn_ctor env sigma c in
  let (_, final_body) = peel_lets sigma e in
  let (_, args_final) = EConstr.decompose_app sigma final_body in
  let (ta_top, tb_top) =
    if Array.length args_final >= 3 then (args_final.(1), args_final.(2))
    else
      let ty_e = Retyping.get_type_of env sigma e in
      let ty_norm = Reductionops.whd_all env sigma ty_e in
      let (_, ty_args) = EConstr.decompose_app sigma ty_norm in
      let n = Array.length ty_args in
      if n >= 2 then (ty_args.(n - 2), ty_args.(n - 1))
      else failwith "fn2fns_fast: ty_args length < 2"
  in

  let is_target_fn_fn = is_fn_ind (fst (EConstr.decompose_app sigma target_fn)) in
  let is_var_fn c = match EConstr.kind sigma c with Var id -> (Id.to_string id = "fn" || Id.to_string id = "fn0") && not (is_fn_ind target_fn) | _ -> false in
  let rec replace_fn d c =
    match EConstr.kind sigma c with
    | Ind _ -> if is_fn_ind c then Vars.liftn d 1 target_fn else c
    | Var _ -> if is_var_fn c then Vars.liftn d 1 target_fn else c
    | Rel _ | Const _ | Construct _ | Sort _ | Int _ | Float _ | String _ -> c
    | Lambda (b, ty, body) ->
        let ty' = replace_fn d ty in
        let body' = replace_fn (d + 1) body in
        if EConstr.eq_constr sigma ty' ty && EConstr.eq_constr sigma body' body then c
        else mkLambda (b, ty', body')
    | LetIn (b, v, ty, cont) ->
        let ty' = replace_fn d ty in
        let v' = replace_fn d v in
        let cont' = replace_fn (d + 1) cont in
        if EConstr.eq_constr sigma ty' ty && EConstr.eq_constr sigma v' v && EConstr.eq_constr sigma cont' cont then c
        else mkLetIn (b, v', ty', cont')
    | App (f, args) ->
        let (head_term, args_full) = EConstr.decompose_app sigma c in
        let cond1 = is_fn_ind head_term in
        let cond2 = is_var_fn head_term in
        let cond3 = EConstr.isRel sigma head_term && Array.length args_full >= 2 && is_target_fn_fn in
        if cond1 || cond2 || cond3 then
          let _ = Feedback.msg_notice Pp.(str "--- replace_fn matched ---") in
          let _ = Feedback.msg_notice Pp.(str "  c: " ++ Printer.pr_econstr_env env sigma c) in
          let _ = Feedback.msg_notice Pp.(str "  h: " ++ Printer.pr_econstr_env env sigma head_term) in
          let _ = Feedback.msg_notice Pp.(str "  cond1 (is_fn_ind): " ++ str (string_of_bool cond1)) in
          let _ = Feedback.msg_notice Pp.(str "  cond2 (is_var_fn): " ++ str (string_of_bool cond2)) in
          let _ = Feedback.msg_notice Pp.(str "  cond3 (is_rel_len2_targetfn): " ++ str (string_of_bool cond3)) in
          let norm_h = Vars.liftn d 1 target_fn in
          let tail_clean = Array.map (replace_fn d) args_full in
          let len = Array.length tail_clean in
          if not is_target_fn_fn && len >= 2 then
            mkApp (norm_h, [| tail_clean.(len - 2); tail_clean.(len - 1) |])
          else if not is_target_fn_fn && len = 1 then
            norm_h
          else
            mkApp (norm_h, tail_clean)
        else if is_fn_Fn_ctor head_term then c
        else
          let f' = replace_fn d f in
          let args' = Array.map (replace_fn d) args in
          if EConstr.eq_constr sigma f' f && Array.for_all2 (EConstr.eq_constr sigma) args' args then c
          else mkApp (f', args')
    | _ ->
        EConstr.map_with_binders sigma (fun d' -> d' + 1) replace_fn d c
  in

  let make_coq_char c =
    let code = Char.code c in
    let bit k = if (code land (1 lsl k)) <> 0 then c_true else c_false in
    mkApp (c_Ascii, [| bit 0; bit 1; bit 2; bit 3; bit 4; bit 5; bit 6; bit 7 |])
  in
  let make_coq_string s =
    let len = String.length s in
    let rec loop i =
      if i = len then c_EmptyString
      else mkApp (c_String, [| make_coq_char s.[i]; loop (i + 1) |])
    in
    loop 0
  in
  let safe_whd_all env sigma c =
    try Reductionops.whd_all env sigma c with _ -> c
  in
  let rec translate cur_env d curr =
    let get_fn_args a =
      let len = Array.length a in
      (a.(len - 3), a.(len - 2), a.(len - 1))
    in
    match EConstr.kind sigma curr with
    | LetIn (binder, val_, ty, cont) ->
        let (h_val, args_val) =
          let (h, a) = EConstr.decompose_app sigma val_ in
          if is_fn_Fn_ctor h && Array.length a >= 3 then (h, a)
          else if Array.length a = 0 then
            match EConstr.kind sigma val_ with
            | Const _ -> EConstr.decompose_app sigma (safe_whd_all env sigma val_)
            | _ -> (h, a)
          else (h, a)
        in
        if is_fn_Fn_ctor h_val && Array.length args_val >= 3 then
          let (ta, tb, lam) = get_fn_args args_val in
          let func_name_str = match binder.Context.binder_name with Name id -> make_coq_string (Id.to_string id) | Anonymous -> make_coq_string "anon" in
          let lam_clean = replace_fn d lam in
          let arg_name_str = match EConstr.kind sigma lam with
            | Lambda (b_arg, _, _) -> (match b_arg.Context.binder_name with Name id -> make_coq_string (Id.to_string id) | Anonymous -> make_coq_string "x")
            | _ -> make_coq_string "x"
          in
          let r_fn = Vars.liftn d 1 target_fn in
          let b_f_type = mkApp (r_fn, [| ta; tb |]) in
          let b_f = Context.make_annot binder.Context.binder_name EConstr.ERelevance.relevant in
          let cur_env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (b_f, b_f_type)) cur_env in
          let cont' = translate cur_env' (d + 1) cont in
          let cont_abs = mkLambda (b_f, b_f_type, cont') in
          let fns_args = [| var_top; r_fn; ta_top; tb_top; ta; tb; func_name_str; arg_name_str; lam_clean; cont_abs |] in
          mkApp (c_fns_Let, fns_args)
        else
          let val_clean = val_ in
          let ty_clean = replace_fn d ty in
          let cur_env' = EConstr.push_rel (Context.Rel.Declaration.LocalDef (binder, val_clean, ty_clean)) cur_env in
          let cont_clean = translate cur_env' (d + 1) cont in
          mkLetIn (binder, val_clean, ty_clean, cont_clean)
    | _ ->
        let (h_curr, args_curr) =
          let (h, a) = EConstr.decompose_app sigma curr in
          if is_fn_Fn_ctor h && Array.length a >= 3 then (h, a)
          else EConstr.decompose_app sigma (safe_whd_all cur_env sigma curr)
        in
        if is_fn_Fn_ctor h_curr && Array.length args_curr >= 3 then
          let (_, _, lam) = get_fn_args args_curr in
          let lam_clean = replace_fn d lam in
          let fns_args = [| var_top; Vars.liftn d 1 target_fn; ta_top; tb_top; top_name_str; make_coq_string "x"; lam_clean |] in
          mkApp (c_fns_Ret, fns_args)
        else
          let r_fn_inner = Vars.liftn (d + 1) 1 target_fn in
          let curr_clean = Vars.liftn 1 1 (replace_fn d curr) in
          let var_x = mkApp (c_expr_Var, [| var_top; r_fn_inner; ta_top; mkRel 1 |]) in
          let call_curr = mkApp (c_expr_Call, [| var_top; r_fn_inner; tb_top; ta_top; curr_clean; var_x |]) in
          let ret_call = mkApp (c_eexpr_Ret, [| var_top; r_fn_inner; tb_top; call_curr |]) in
          let b_x_type = mkApp (var_top, [| ta_top |]) in
          let b_x = Context.make_annot (Name (Id.of_string "x")) EConstr.ERelevance.relevant in
          let lam_main = mkLambda (b_x, b_x_type, ret_call) in
          let fns_args = [| var_top; Vars.liftn d 1 target_fn; ta_top; tb_top; top_name_str; make_coq_string "x"; lam_main |] in
          mkApp (c_fns_Ret, fns_args)
  in
  let res = translate env 0 e in
  res

let () =
  define
    { mltac_plugin = "quartz.monomorphize_plugin"; mltac_tactic = "deglob_fast" }
    (constr @-> eret constr)
    (fun c env sigma -> deglob env sigma c);
  define
    { mltac_plugin = "quartz.monomorphize_plugin"; mltac_tactic = "rmonomorphize_fast" }
    (constr @-> eret constr)
    (fun c env sigma -> rmonomorphize_fast c env sigma);
  define
    { mltac_plugin = "quartz.monomorphize_plugin"; mltac_tactic = "fn2fns_fast" }
    (constr @-> constr @-> eret constr)
    (fun b e env sigma -> fn2fns_fast b e env sigma)
