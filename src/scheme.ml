(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)
type context = (Core.variable, Type.ty) Common.assoc
type ty_scheme = context * Type.ty * Constraints.t
type dirty_scheme = context * Type.dirty * Constraints.t
type t = context * Type.ty * Constraints.t * Type.substitution
type change = t -> t

let refresh (ctx, ty, cnstrs) =
  let sbst = Type.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Constraints.subst_constraints sbst cnstrs

let ty_param_less p q (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_ty_constraint p q cnstrs, sbst)
and dirt_param_less ~pos d1 d2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_dirt_constraint d1 d2 cnstrs, sbst)
and region_param_less ~pos d1 d2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_region_constraint d1 d2 cnstrs, sbst)
and region_less ~pos r1 r2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_region_constraint r1 r2 cnstrs, sbst)
and region_covers r i (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_region_bound r [Constraints.Instance i] cnstrs, sbst)
and just new_cnstrs (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.join_disjoint_constraints new_cnstrs cnstrs, sbst)
and add_region_bound r bnd (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_region_bound r bnd cnstrs, sbst)

let rec add_rest_substitution ~pos d drt' (ctx, ty, cnstrs, sbst) =
  let drt' = Type.subst_dirt sbst drt' in
  let sbst' = {
    Type.identity_subst with 
    Type.dirt_param = (fun d' -> if d' = d then drt' else Type.simple_dirt d')
  } in
  let (pred, succ, new_dirt_grph) = Constraints.remove_dirt cnstrs d in
  let cnstrs = {cnstrs with Constraints.dirt_graph = new_dirt_grph} in
  let ty_sch = (Common.assoc_map (Type.subst_ty sbst') ctx, Type.subst_ty sbst' ty, cnstrs, Type.compose_subst sbst' sbst) in
  let ty_sch = List.fold_right (fun q ty_sch -> dirt_less ~pos (Type.simple_dirt q) drt' ty_sch) pred ty_sch in
  List.fold_right (fun q ty_sch -> dirt_less ~pos drt' (Type.simple_dirt q) ty_sch) succ ty_sch

and dirt_less ~pos drt1 drt2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  ignore ty_sch;
  let {Type.ops = ops1; Type.rest = rest1} = Type.subst_dirt sbst drt1
  and {Type.ops = ops2; Type.rest = rest2} = Type.subst_dirt sbst drt2 in
  let new_ops ops1 ops2 =
    let ops2 = List.map fst ops2 in
    let add_op (op, _) news =
      if List.mem op ops2 then news else (op, Type.fresh_region_param ()) :: news
    in
    List.fold_right add_op ops1 []
  in
  let new_ops1 = new_ops ops2 ops1
  and new_ops2 = new_ops ops1 ops2 in
  match new_ops1, new_ops2 with
  | [], [] ->
      let op_less (op, dt1) ty_sch =
        begin match Common.lookup op ops2 with
        | Some dt2 -> region_param_less ~pos dt1 dt2 ty_sch
        | None -> assert false
      end
      in
      List.fold_right op_less ops1 (dirt_param_less ~pos rest1 rest2 ty_sch)
  | _, _ ->
      dirt_less ~pos drt1 drt2 (
      add_rest_substitution ~pos rest1 {Type.ops = new_ops1; Type.rest = Type.fresh_dirt_param ()}
      (add_rest_substitution ~pos rest2 {Type.ops = new_ops2; Type.rest = Type.fresh_dirt_param ()} ty_sch))

let rec ty_less ~pos ty1 ty2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  match Type.subst_ty sbst ty1, Type.subst_ty sbst ty2 with

  | (ty1, ty2) when ty1 = ty2 -> ty_sch

  | (Type.TyParam p, Type.TyParam q) -> ty_param_less p q ty_sch

  | (Type.TyParam p, ty) ->
      let ty' = Type.replace ty in
      ty_less ~pos ty' ty (add_substitution ~pos p ty' ty_sch)

  | (ty, Type.TyParam p) ->
      let ty' = Type.replace ty in
      ty_less ~pos ty ty' (add_substitution ~pos p ty' ty_sch)

  | (Type.Arrow (ty1, drty1), Type.Arrow (ty2, drty2)) ->
      ty_less ~pos ty2 ty1 (dirty_less ~pos drty1 drty2 ty_sch)

  | (Type.Tuple tys1, Type.Tuple tys2)
      when List.length tys1 = List.length tys2 ->
      List.fold_right2 (ty_less ~pos) tys1 tys2 ty_sch

  | (Type.Apply (ty_name1, args1), Type.Apply (ty_name2, args2)) when ty_name1 = ty_name2 ->
      begin match Tctx.lookup_params ty_name1 with
      | None -> Error.typing ~pos "Undefined type %s" ty_name1
      | Some ps -> args_less ~pos ps args1 args2 ty_sch
      end

  | (Type.Effect (ty_name1, args1, rgn1), Type.Effect (ty_name2, args2, rgn2)) when ty_name1 = ty_name2 ->
      begin match Tctx.lookup_params ty_name1 with
      | None -> Error.typing ~pos "Undefined type %s" ty_name1
      | Some ps ->
          region_less ~pos rgn1 rgn2 (
            args_less ~pos ps args1 args2 ty_sch
          )
      end

  (* The following two cases cannot be merged into one, as the whole matching
     fails if both types are Apply, but only the second one is transparent. *)
  | (Type.Apply (ty_name, args), ty) when Tctx.transparent ~pos ty_name ->
      begin match Tctx.ty_apply ~pos ty_name args with
      | Tctx.Inline ty' -> ty_less ~pos ty' ty ty_sch
      | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
      end

  | (ty, Type.Apply (ty_name, args)) when Tctx.transparent ~pos ty_name ->
      begin match Tctx.ty_apply ~pos ty_name args with
      | Tctx.Inline ty' -> ty_less ~pos ty ty' ty_sch
      | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
      end

  | (Type.Handler ((tyv1, drt1), tyf1), Type.Handler ((tyv2, drt2), tyf2)) ->
      dirt_less ~pos drt2 drt1 (ty_less ~pos tyv2 tyv1 (dirty_less ~pos tyf1 tyf2 ty_sch))

  | (ty1, ty2) ->
      let ty1, ty2 = Type.beautify2 ty1 ty2 in
      Error.typing ~pos "This expression has type %t but it should have type %t." (Type.print ty1) (Type.print ty2)

and add_substitution ~pos p ty' (ctx, ty, cnstrs, sbst) =
  let ty' = Type.subst_ty sbst ty' in
  let sbst' = {
    Type.identity_subst with 
    Type.ty_param = (fun p' -> if p' = p then ty' else Type.TyParam p')
  } in
  let (pred, succ, new_ty_grph) = Constraints.remove_ty cnstrs p in
  let cnstrs = {cnstrs with Constraints.ty_graph = new_ty_grph} in
  let ty_sch = (Common.assoc_map (Type.subst_ty sbst') ctx, Type.subst_ty sbst' ty, cnstrs, Type.compose_subst sbst' sbst) in
  let ty_sch = List.fold_right (fun q ty_sch -> ty_less ~pos (Type.TyParam q) ty' ty_sch) pred ty_sch in
  List.fold_right (fun q ty_sch -> ty_less ~pos ty' (Type.TyParam q) ty_sch) succ ty_sch

and args_less ~pos (ps, ds, rs) (ts1, ds1, rs1) (ts2, ds2, rs2) ty_sch =
  (* NB: it is assumed here that
     List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
  let for_parameters add ps lst1 lst2 ty_sch =
    List.fold_right2 (fun (_, (cov, contra)) (ty1, ty2) ty_sch ->
                        let ty_sch = if cov then add ~pos ty1 ty2 ty_sch else ty_sch in
                        if contra then add ~pos ty2 ty1 ty_sch else ty_sch) ps (List.combine lst1 lst2) ty_sch
  in
  let ty_sch = for_parameters ty_less ps ts1 ts2 ty_sch in
  let ty_sch = for_parameters dirt_less ds ds1 ds2 ty_sch in
  for_parameters region_less rs rs1 rs2 ty_sch

and dirty_less ~pos (ty1, d1) (ty2, d2) ty_sch =
  ty_less ~pos ty1 ty2 (dirt_less ~pos d1 d2 ty_sch)

let trim_context ~pos ctx_p (ctx, ty, cnstrs, sbst) =
  let trim (x, t) (ctx, ty, cnstrs, sbst) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs, sbst)
    | Some u -> ty_less ~pos u t (ctx, ty, cnstrs, sbst)
  in
  List.fold_right trim ctx ([], ty, cnstrs, sbst)

let less_context ~pos ctx_p (ctx, ty, cnstrs, sbst) =
  let trim (x, t) (ctx, ty, cnstrs, sbst) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs, sbst)
    | Some u -> ty_less ~pos u t ((x, u) :: ctx, ty, cnstrs, sbst)
  in
  List.fold_right trim ctx ([], ty, cnstrs, sbst)


let (@@@) = Trio.append

let pos_neg_tyscheme (ctx, ty, cnstrs) =
  let add_ctx_pos_neg (_, ctx_ty) (pos, neg) =
    let pos_ctx_ty, neg_ctx_ty = Type.pos_neg_params Tctx.get_variances ctx_ty in
    neg_ctx_ty @@@ pos, pos_ctx_ty @@@ neg
  in
  let (((_, _, pos_rs) as pos), neg) = List.fold_right add_ctx_pos_neg ctx (Type.pos_neg_params Tctx.get_variances ty) in
  let add_region_bound bnd posi = match bnd with
  | Constraints.Without (d, _) -> d :: posi
  | Constraints.Instance _ -> posi
  in
  let posi_regions = List.fold_right (fun (d, bnds, _) posi ->
                                      match bnds with None -> posi | Some bnds -> if List.mem d pos_rs then List.fold_right add_region_bound bnds posi else posi) (Constraints.Region.bounds cnstrs.Constraints.region_graph) [] in
  let pos = ([], [], posi_regions) @@@ pos in
  let add_region_bound bnd (posi, nega) = match bnd with
  | Constraints.Without (r, rs) -> (([], [], r :: rs) @@@ posi, nega)
  | Constraints.Instance _ -> (posi, nega)
  in
  let (((_, _, pos_rs) as posi), nega) = (Trio.uniq pos, Trio.uniq neg) in
  let (posi, nega) = List.fold_right (fun (d, bnds, _) (posi, nega) ->
                                      match bnds with None -> (posi, nega) | Some bnds -> (if List.mem d pos_rs then List.fold_right add_region_bound bnds (posi, nega) else (posi, nega))) (Constraints.Region.bounds cnstrs.Constraints.region_graph) (posi, nega) in
  Trio.uniq posi, Trio.uniq nega

let garbage_collect pos neg (ctx, ty, cnstrs) =
  ctx, ty, Constraints.garbage_collect pos neg cnstrs

let normalize_context ~pos (ctx, ty, cstr, sbst) =
  let collect (x, ty) ctx =
    match Common.lookup x ctx with
    | None -> (x, ref [ty]) :: ctx
    | Some tys -> tys := ty :: !tys; ctx
  in
  let ctx = List.fold_right collect ctx [] in

  let add (x, tys) (ctx, typ, cnstrs, sbst) =
    match !tys with
    | [] -> assert false
    | [ty] -> ((x, Type.subst_ty sbst ty) :: ctx, typ, cnstrs, sbst)
    | tys ->
        let ty' = Type.fresh_ty () in
        let ctx' = (x, ty') :: ctx in
        List.fold_right (fun ty ty_sch -> ty_less ~pos ty' ty ty_sch) tys (ctx', typ, cnstrs, sbst)
  in
  List.fold_right add ctx ([], ty, cstr, sbst)

let subst_ty_scheme sbst (ctx, ty, cnstrs) =
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Constraints.subst_constraints sbst cnstrs

let subst_dirty_scheme sbst (ctx, drty, cnstrs) =
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_dirty sbst drty, Constraints.subst_constraints sbst cnstrs

let add_to_top ~pos (top_ctx, top_cstrs, top_sbst) ctx cstrs =
  let (top_ctx, _, top_cstrs, top_sbst) = List.fold_right Common.id (normalize_context ~pos :: cstrs) (ctx @ top_ctx, Type.universal_ty, top_cstrs, top_sbst) in
  top_ctx, top_cstrs, top_sbst

let finalize ctx ty chngs =
  let ctx, ty, cnstrs, sbst = List.fold_right Common.id chngs (ctx, ty, Constraints.empty, Type.identity_subst) in
  subst_ty_scheme sbst (ctx, ty, cnstrs)

let finalize_ty_scheme ~pos ctx ty chngs =
  let ty_sch = finalize ctx ty (normalize_context ~pos :: chngs) in
  let pos, neg = pos_neg_tyscheme ty_sch in
  garbage_collect pos neg ty_sch

let finalize_dirty_scheme ~pos ctx drty chngs =
  match finalize_ty_scheme ~pos ctx (Type.Arrow (Type.unit_ty, drty)) chngs with
  | ctx, Type.Arrow (_, drty), cstr -> (ctx, drty, cstr)
  | _ -> assert false

let finalize_pattern_scheme ~pos ctx ty chngs =
  let ty_sch = finalize ctx ty chngs in
  (* Note that we change the polarities in pattern types *)
  let neg, pos = pos_neg_tyscheme ty_sch in
  garbage_collect pos neg ty_sch


let context ctx ppf =
  match ctx with
  | [] -> ()
  | _ -> Print.print ppf "(@[%t@]).@ " (Print.sequence "," (fun (x, t) ppf -> Print.print ppf "%t : %t" (Print.variable x) (Type.print t)) ctx)

let collapse ((_, _, cnstrs) as ty_sch) =
  let collapse_graph g sbst =
    let x = Type.fresh_ty_param () in
    let keys = Constraints.Ty.keys g in
    Type.compose_subst {
      Type.identity_subst with
      Type.ty_param = (
        fun p -> Type.TyParam (if List.mem p keys then x else p)
      )
    } sbst
  in
  let sbst = List.fold_right collapse_graph cnstrs.Constraints.ty_graph Type.identity_subst in
  subst_ty_scheme sbst ty_sch

let print_ty_scheme ty_sch ppf =
  let sbst = Type.beautifying_subst () in
  let ty_sch = collapse ty_sch in
  let (ctx, ty, _) = subst_ty_scheme sbst ty_sch in
  let non_poly = Trio.flatten_map (fun (x, t) -> let pos, neg = Type.pos_neg_params Tctx.get_variances t in pos @@@ neg) ctx in
  Type.print ~non_poly ty ppf

let print_dirty_scheme drty_sch ppf =
  let (ctx, (ty, _), cnstrs) = drty_sch in
  print_ty_scheme (ctx, ty, cnstrs) ppf
(*   let sbst = Type.beautifying_subst () in
  let (ctx, (ty, drt), cnstrs) = subst_dirty_scheme sbst drty_sch in
  Print.print ppf "%t%t ! %t | %t"
    (context ctx)
    (Type.print ty)
    (Type.print_dirt drt)
    (Constraints.print cnstrs) *)

