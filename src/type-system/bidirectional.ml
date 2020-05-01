open CoreUtils
module Syntax = AnnotatedSyntax
module Ctx = SimpleCtx

type state = Ctx.t

let initial_state = Ctx.empty


let rec vsubtype ty1 ty2 ~loc =
  match ty1, ty2 with
  | Type.TyParam _, _ | _, Type.TyParam _ ->
      Error.typing ~loc 
        ( "EEFF does not support type parameters outside of type definitions.@,"
        ^^ " A type parameter comparison of `%t` and `%t` was attempted,"
        ^^ " which is an implementation bug." )
        (Type.print_vty ([], ty1)) (Type.print_vty ([], ty2)) 
  | Type.Basic x1, Type.Basic x2 -> x1 = x2
  | Type.Apply (name1, tys1), Type.Apply (name2, tys2) ->
      CoreTypes.TyName.compare name1 name2 = 0 
      && List.for_all2 (vsubtype ~loc) tys1 tys2 
  | Type.Apply (name, tys), ty -> (
      if Tctx.transparent ~loc:Location.unknown name then
        match Tctx.ty_apply ~loc:Location.unknown name tys with
        | Tctx.Inline t -> (vsubtype ~loc) t ty
        | Tctx.Sum _ -> assert false (* not transparent *)
      else false )
  | ty, Type.Apply (name, tys) -> (
      if Tctx.transparent ~loc:Location.unknown name then
        match Tctx.ty_apply ~loc:Location.unknown name tys with
        | Tctx.Inline t -> (vsubtype ~loc) ty t
        | Tctx.Sum _ -> assert false (* not transparent *)
      else false )
  | Type.Tuple tys1, Type.Tuple tys2 -> 
      List.for_all2 (vsubtype ~loc) tys1 tys2
  | Type.Arrow (in_ty1, out_cty1), Type.Arrow (in_ty2, out_cty2) ->
      vsubtype ~loc in_ty2 in_ty1 && csubtype ~loc out_cty1 out_cty2     
  | Type.Handler (in_cty1, out_cty1), Type.Handler (in_cty2, out_cty2) ->
      csubtype ~loc in_cty2 in_cty1 && csubtype ~loc out_cty1 out_cty2      
  | _, _ -> false

and csubtype cty1 cty2 ~loc =
  let Type.Cty (ty1, effs1) = cty1 in
  let Type.Cty (ty2, effs2) = cty2 in
  vsubtype ~loc ty1 ty2 && eff_subtype effs1 effs2

and eff_subtype effs1 effs2 = 
  List.for_all (fun x -> List.mem x effs2) effs1 

(* and ctypes_match cty1 cty2 =
  let Type.Cty (ty1, effsig1) = cty1 in
  let Type.Cty (ty2, effsig2) = cty2 in
  let rec sig_match = function
    | [] -> true
    | eff :: effs -> (
        match Assoc.lookup eff effsig1, Assoc.lookup eff effsig2 with
        | None, None -> sig_match effs
        | None, Some _
        | Some _, None -> false
        | Some (ty1, ty2), Some (ty1',ty2') ->
            vtypes_match ty1 ty2 && vtypes_match ty1' ty2' && sig_match effs)
  in
  vtypes_match ty1 ty2
  && sig_match (Assoc.keys_of effsig1 @ Assoc.keys_of effsig2) *)

let extend_ctx ctx binds =
  Assoc.fold_left
    (fun acc (x, ty) -> Ctx.extend acc x (Ctx.generalize ctx true ty)) 
    ctx binds

let rec pattern_check ctx p ty =
  let loc = p.at in
  match p.it with
  | Syntax.PVar x -> Assoc.of_list [(x, ty)]
  | Syntax.PNonbinding -> Assoc.empty
  | Syntax.PConst const ->
      let real_ty = Type.Basic (Const.infer_ty const) in
      if vsubtype real_ty ty ~loc then Assoc.empty else
        Error.typing ~loc 
          ("Constant pattern `%t` is of type `%t` but checked against type `%t`.")
          (Const.print const) (Type.print_vty ([], real_ty))
          (Type.print_vty ([], ty))
  | Syntax.PTuple ps -> 
      begin match ty with
      | Type.Tuple tys ->
          let rec checker ps tys binds =
            match ps, tys with
            | [], [] -> binds
            | p :: ps, ty :: tys ->
                let b = pattern_check ctx p ty in
                let binds' = Assoc.concat binds b in
                checker ps tys binds'
            | [], tys ->
                Error.typing ~loc 
                  ( "Tuple pattern is checked against type `%t` but does not "
                  ^^ "have enough components to typecheck." )
                  (Type.print_vty ([], ty))
            | ps, [] ->
                Error.typing ~loc 
                  ( "Tuple pattern is expected to be of type `%t` but has too "
                  ^^ "many components to typecheck." )
                  (Type.print_vty ([], ty))
          in
          checker ps tys Assoc.empty
      | _ ->
          (* Catch that unit as well. *)
          if vsubtype ~loc ty (Type.Tuple []) then Assoc.empty else
          Error.typing ~loc 
            ( "A tuple pattern is checked against an incompatible type of `%t`." )
            (Type.print_vty ([], ty))
      end
  | Syntax.PVariant (lbl, arg_p_opt) ->
      begin match Tctx.find_variant lbl with
      | None -> 
          Error.typing ~loc 
            "Constructor pattern `%t` does not belong to a known type."
            (CoreTypes.Label.print lbl)
      | Some (inf_name, inf_params, _, inf_arg_ty_opt) -> (
          match ty with
          | Type.Apply (chk_name, chck_params) 
            when CoreTypes.TyName.compare chk_name inf_name = 0 ->
              let sbst = List.combine inf_params chck_params |> Assoc.of_list in
              begin match arg_p_opt, inf_arg_ty_opt with
                | None, Some arg_ty ->
                    Error.typing ~loc 
                      ( "Constructor pattern `%t` requires an argument of type `%t` "
                      ^^ "but is used with no arguments." )
                      (CoreTypes.Label.print lbl) (Type.print_vty ([], arg_ty))
                | Some arg_p, None ->
                    Error.typing ~loc 
                      ( "Constructor pattern `%t` does not accept arguments, but is provided with some." )
                      (CoreTypes.Label.print lbl)
                | None, None -> Assoc.empty
                | Some arg_p, Some arg_ty -> 
                    (pattern_check ctx arg_p (Type.subst_ty sbst arg_ty))
              end
          | _ ->
            Error.typing ~loc 
              ("Constructor pattern `%t` belongs to variant `%t` but is checked"
              ^^ " against the type `%t`.")
              (CoreTypes.Label.print lbl) (CoreTypes.TyName.print inf_name)
              (Type.print_vty ([], ty)))
      end

and value_check ctx v ty =
  let loc = v.at in
  match v.it with
  | Syntax.Var x -> 
      (* Could be done via modeswitch but this gives better errors. *)
      let real_ty = Ctx.lookup ~loc ctx x in
      if vsubtype ~loc real_ty ty then () else
        Error.typing ~loc 
          "Variable `%t` of type `%t` is checked against the type `%t`."
          (CoreTypes.Variable.print x) (Type.print_vty ([], real_ty))
          (Type.print_vty ([], ty))
  | Syntax.Const const -> 
      (* Could be done via modeswitch but this gives better errors. *)
      let real_ty = Type.Basic (Const.infer_ty const) in
      if vsubtype ~loc real_ty ty then () else
        Error.typing ~loc 
          "Constant `%t` of type `%t` is checked against the type `%t`."
          (Const.print const) (Type.print_vty ([], real_ty))
          (Type.print_vty ([], ty))
  | Syntax.Tuple vs -> 
      begin match ty with
      | Type.Tuple tys ->
          let rec checker vs tys =
            match vs, tys with
            | [], [] -> ()
            | v :: vs, ty :: tys ->
                (value_check ctx v ty; checker vs tys)
            | [], tys ->
                Error.typing ~loc 
                  ( "Tuple is checked against type `%t` but does not "
                  ^^ "have enough components to typecheck." )
                  (Type.print_vty ([], ty))
            | vs, [] ->
                Error.typing ~loc 
                  ( "Tuple is checked against type `%t` but has too "
                  ^^ "many components to typecheck." )
                  (Type.print_vty ([], ty))
          in
          checker vs tys
      | _ ->
          if vsubtype ~loc ty (Type.Tuple []) then () else 
          Error.typing ~loc 
            ( "A tuple is checked against the incompatible type `%t`." )
            (Type.print_vty ([], ty))
      end
  | Syntax.VAnnotated (v, ann_ty) ->
      if vsubtype ~loc ann_ty ty then value_check ctx v ann_ty else
        Error.typing ~loc 
          ( "Value is checked against type `%t` but is annotated with"
          ^^ " the incompatible type `%t`." )
          (Type.print_vty ([], ty)) (Type.print_vty ([], ann_ty))
  | Syntax.Variant (lbl, arg_opt) -> 
      begin match Tctx.find_variant lbl with
      | None -> 
          Error.typing ~loc 
            "Constructor pattern `%t` does not belong to a known type."
            (CoreTypes.Label.print lbl)
      | Some (inf_name, inf_params, _, inf_arg_ty_opt) -> (
          match ty with
          | Type.Apply (chk_name, chck_params) 
            when CoreTypes.TyName.compare chk_name inf_name = 0 ->
              let sbst = List.combine inf_params chck_params |> Assoc.of_list in
              begin match arg_opt, inf_arg_ty_opt with
                | None, Some arg_ty ->
                    Error.typing ~loc 
                      ( "Constructor pattern `%t` requires an argument of type `%t` "
                      ^^ "but is used with no arguments." )
                      (CoreTypes.Label.print lbl) (Type.print_vty ([], arg_ty))
                | Some arg, None ->
                    Error.typing ~loc 
                      ( "Constructor pattern `%t` does not accept arguments, but is provided with some." )
                      (CoreTypes.Label.print lbl)
                | None, None -> ()
                | Some arg, Some arg_ty -> 
                    (value_check ctx arg (Type.subst_ty sbst arg_ty))
              end
          | _ ->
            Error.typing ~loc 
              ("Constructor pattern `%t` belongs to variant `%t` but is checked"
              ^^ " against the type `%t`.")
              (CoreTypes.Label.print lbl) (CoreTypes.TyName.print inf_name)
              (Type.print_vty ([], ty)))
      end
  | Syntax.Lambda (p, c) -> (
      match ty with
      | Type.Arrow (ty1, ty2) ->
          let binds = pattern_check ctx p ty1 in
          computation_check (extend_ctx ctx binds) c ty2
      | _ ->
          Error.typing ~loc 
            ( "The function is checked against the incompatible type `%t`." )
            (Type.print_vty ([], ty))
      )
  | Syntax.Handler { Syntax.effect_clauses= ops; Syntax.value_clause= (p, c) }
    -> (
      match ty with
      | Type.Handler (ty1, ty2) -> (
          effect_clauses_check ctx ops (ty1, ty2);
          let Type.Cty (vty1,_) = ty1 in
          let binds = pattern_check ctx p vty1 in
          computation_check (extend_ctx ctx binds) c ty2
          )
      | _ ->
          Error.typing ~loc 
            ( "The handler is checked against the incompatible type `%t`." )
            (Type.print_vty ([], ty))
      )
  (* Mode switch for values is currently not used in favor of better 
    error reporting.

    | _ ->
      (* Mode switch *)
      let synth_vty = value_synth ctx v in
      if vsubtype ~loc synth_vty ty then () else
      Error.typing ~loc 
        ("The value was synthesized the type `%t`,@,  "
        ^^ "`however the expected type of this value is `%t`.")
        (Type.print_vty ([], synth_vty))
        (Type.print_vty ([], ty)) *)

and value_synth ctx v =
  let loc = v.at in
  match v.it with
  | Syntax.Var x -> Ctx.lookup ~loc ctx x
  | Syntax.Const const -> Type.Basic (Const.infer_ty const)
  | Syntax.Tuple vs ->
      Type.Tuple (left_to_right_map (value_synth ctx) vs)
  | Syntax.VAnnotated (v, ty) -> (value_check ctx v ty; ty)
  | Syntax.Variant (lbl, arg_opt) ->
      begin match Tctx.find_variant lbl with
      | None -> 
          Error.typing ~loc 
            "Constructor pattern `%t` does not belong to a known type."
            (CoreTypes.Label.print lbl)
      | Some (inf_name, inf_params, _, inf_arg_ty_opt) -> (
          match inf_params with
          | _ :: _ ->
              Error.typing ~loc 
              ("Constructor pattern `%t` belongs to a non-concrete variant"
              ^^ " type `%t`. @,"
              ^^ "Type parameters are not inferable in current system "
              ^^ "and therefore cannot be synthesized. @,"
              ^^ "Please provide type annotations.")
              (CoreTypes.Label.print lbl)
              (Type.print_vty ([], Tctx.apply_to_params inf_name inf_params))
          | [] ->
            begin match arg_opt, inf_arg_ty_opt with
            | None, Some arg_ty ->
                Error.typing ~loc 
                  ( "Constructor pattern `%t` requires an argument of type `%t` "
                  ^^ "but is used with no arguments." )
                  (CoreTypes.Label.print lbl) (Type.print_vty ([], arg_ty))
            | Some arg, None ->
                Error.typing ~loc 
                  ( "Constructor pattern `%t` does not accept arguments, but is provided with some." )
                  (CoreTypes.Label.print lbl)
            | None, None -> Tctx.apply_to_params inf_name []
            | Some arg, Some arg_ty -> 
                (value_check ctx arg arg_ty);
                Tctx.apply_to_params inf_name inf_params
            end
          ) 
      end
  | Syntax.Lambda abs ->
      Error.typing ~loc 
        ( "Cannot synthesize types for functions. Please provide annotations." )
  | Syntax.Handler { Syntax.effect_clauses= ops; Syntax.value_clause= a_val }
    ->
      Error.typing ~loc 
        ( "Cannot synthesize types for handlers. Please provide annotations." )

  
and computation_check ctx c cty =
  let loc = c.at in
  match c.it with
  | Syntax.CAnnotated (c, ann_ty) ->
      if csubtype ~loc ann_ty cty then computation_check ctx c ann_ty else
        Error.typing ~loc 
          ( "Computation is expected to be of type `%t` @,but is annotated with"
          ^^ " type `%t`." )
          (Type.print_cty ([], cty)) (Type.print_cty ([], ann_ty))
  | Syntax.Value v -> 
      let Type.Cty (vty, _) = cty in
      value_check ctx v vty
  | Syntax.Match (v, []) -> value_check ctx v Type.empty_ty
  | Syntax.Match (v, lst) ->
      let in_ty = value_synth ctx v in
      let check_case (p, c') =
        let binds = pattern_check ctx p in_ty in
        computation_check (extend_ctx ctx binds) c' cty
      in
      List.iter check_case lst
  | Syntax.Let (defs, c) ->
      let Type.Cty(_, effsig) = cty in
      let def_checker binds (p, c) =
        let Type.Cty(vty, synth_effsig) = computation_synth ctx c in
        let b = pattern_check ctx p vty in
        if eff_subtype synth_effsig effsig then
          Assoc.concat binds b
        else
          Error.typing ~loc 
            ("Encountered effect signature missmatch of types @,`%t` and @,`%t` "
              ^^ "while resolving `let` definitions (possibly implicit). @,"
              ^^ "Possible effects are `%t`, @,but types only allow effects from "
              ^^ "signature @,`%t`.")
            (Type.print_cty ([], Type.Cty(vty, synth_effsig)))
            (Type.print_cty ([], cty))
            (Type.print_sig synth_effsig)
            (Type.print_sig effsig)
      in
      let binds = List.fold_left def_checker Assoc.empty defs in
      computation_check (extend_ctx ctx binds) c cty
  | Syntax.LetRec (defs, c) ->
      let ty_collect binds (name, ty, abs) =
        Assoc.update name ty binds
      in
      let binds = Assoc.rev (List.fold_left ty_collect Assoc.empty defs) in
      let ctx' = extend_ctx ctx binds in 
      let def_checker (name, ty, (p, c)) =
        match ty with
        | Type.Arrow (ty1, ty2) ->
            let b = pattern_check ctx' p ty1 in
            let ctx'' = extend_ctx ctx' b in
            computation_check ctx'' c ty2
        | _ ->
            Error.typing ~loc 
              ("The recursive function `%t` is annotated with the non-function"
              ^^ " type @,`%t`. @,Only functions are allowed in recursive"
              ^^ " definitions.")
              (CoreTypes.Variable.print name) (Type.print_vty ([], ty))
      in
      List.iter def_checker defs;
      computation_check ctx' c cty
  | Syntax.Check c ->
      if csubtype ~loc cty (Type.Cty (Type.unit_ty, [])) then
        ignore (computation_synth ctx c)
      else
        Error.typing ~loc 
          ("Command [Check] is used to display values at runtime and returns "
          ^^ "`%t`. However the expected type of this computation is `%t`.")
          (Type.print_cty ([], Type.Cty (Type.unit_ty, [])))
          (Type.print_cty ([], cty))
  | _ ->
      (* Mode switch *)
      let synth_cty = computation_synth ctx c in
      if csubtype ~loc synth_cty cty then () else
      Error.typing ~loc 
        ("The computation was synthesized the type `%t`, @,"
        ^^ "however the expected type of this computation is `%t`.")
        (Type.print_cty ([], synth_cty))
        (Type.print_cty ([], cty))



and computation_synth ctx c =
  let loc = c.at in
  match c.it with
  | Syntax.CAnnotated (c, ann_ty) -> (computation_check ctx c ann_ty; ann_ty)
  | Syntax.Apply (v1, v2) ->
      let ty1 = value_synth ctx v1 in
      (match ty1 with
      | Type.Arrow(in_ty, out_ty) -> value_check ctx v2 in_ty; out_ty
      | real_ty ->
          Error.typing ~loc 
            ("Trying to apply a non-function element of type `%t`.")
            (Type.print_vty ([], real_ty)) )
  | Syntax.Value v -> Type.Cty (value_synth ctx v, [])
  | Syntax.Match (v, []) ->
      Error.typing ~loc 
        ("Unable to synthesize type of match statement when matching something of @,`%t` "
        ^^ "type. @,Please provide annotations.")
        (Type.print_vty ([], Type.empty_ty))
  | Syntax.Match (v, (p, c') :: []) ->
      let in_ty = value_synth ctx v in
      let binds = pattern_check ctx p in_ty in
      computation_synth (extend_ctx ctx binds) c'
  | Syntax.Match (v, lst) ->
      Error.typing ~loc 
        ("Unable to synthesize type of a branching match statement. "
        ^^ "@,Please provide annotations.")
  | Syntax.Handle (v1, c2) ->
      let ty1 = value_synth ctx v1 in
      (match ty1 with
      | Type.Handler (in_ty, out_ty) ->
          let () = computation_check ctx c2 in_ty in
          out_ty
      | real_ty ->
          Error.typing ~loc 
            ("Trying to handle with a non-handler element of type @,`%t`.")
            (Type.print_vty ([], real_ty)) )
  | Syntax.Let (defs, c) ->
      let def_checker binds (p, c) =
        (* WARNING!! DOES NOT CHECK SIGNATURE MATCH! *)
        let Type.Cty(vty, effsig) = computation_synth ctx c in
        let b = pattern_check ctx p vty in
        Assoc.concat binds b
      in
      let binds = List.fold_left def_checker Assoc.empty defs in
      computation_synth (extend_ctx ctx binds) c
  | Syntax.LetRec (defs, c) ->
      let ty_collect binds (name, ty, abs) =
        Assoc.update name ty binds
      in
      let binds = Assoc.rev (List.fold_left ty_collect Assoc.empty defs) in
      let ctx' = extend_ctx ctx binds in 
      let def_checker (name, ty, (p, c)) =
        match ty with
        | Type.Arrow (ty1, ty2) ->
            let b = pattern_check ctx' p ty1 in
            let ctx'' = extend_ctx ctx' b in
            computation_check ctx'' c ty2
        | _ ->
            Error.typing ~loc 
              ("The recursive function `%t` @,is annotated with the non-function"
              ^^ " type `%t`. @,Only functions are allowed in recursive"
              ^^ " definitions.")
              (CoreTypes.Variable.print name) (Type.print_vty ([], ty))
      in
      List.iter def_checker defs;
      computation_synth ctx' c
  | Syntax.Effect (eff, arg) -> (
      match Ctx.infer_effect ctx eff with
      | None ->
          Error.typing ~loc 
            ( "Effect `%t` has no known type." )
            (CoreTypes.Effect.print eff)
      | Some (ty1, ty2) ->
          value_check ctx arg ty1; Type.Cty(ty2, [eff])
    )
  | Syntax.Check c -> 
      ignore (computation_synth ctx c); Type.Cty (Type.unit_ty, [])

and effect_clauses_check ctx ops (ty1, ty2) =
  let rec checker (op, (px, pk, c_op)) =
    match Ctx.infer_effect ctx op with
    | None ->
        Error.typing ~loc:px.at 
          ( "Effect `%t` has no known type." )
          (CoreTypes.Effect.print op)
    | Some (op_ty1, op_ty2) -> 
        let ctx' = extend_ctx ctx (pattern_check ctx px op_ty1) in
        let ctx'' = 
          extend_ctx ctx' (pattern_check ctx pk (Type.Arrow (op_ty2, ty2)))
        in
        computation_check ctx'' c_op ty2   
  in
  Assoc.iter checker ops

let infer_top_comp ctx c =
  let cty = computation_synth ctx c in
  Exhaust.check_comp c ;
  (ctx, ([], cty))

let infer_top_let ~loc ctx defs =
  let def_checker binds (p, c) =
    (* WARNING!! DOES NOT CHECK SIGNATURE MATCH! *)
    let Type.Cty(vty, effsig) = computation_synth ctx c in
    let b = pattern_check ctx p vty in
    Assoc.concat binds b
  in
  let binds = List.fold_left def_checker Assoc.empty defs in
  let ctx' = extend_ctx ctx binds in
  let vars = 
    Assoc.to_list binds 
    |> List.map (fun (x, ty) -> (x, Ctx.generalize ctx true ty))
  in
  List.iter
    (fun (p, c) -> Exhaust.is_irrefutable p ; Exhaust.check_comp c)
    defs ;
  (vars, ctx')

let infer_top_let_rec ~loc ctx defs =
  let ty_collect binds (name, ty, abs) =
    Assoc.update name ty binds
  in
  let binds = Assoc.rev (List.fold_left ty_collect Assoc.empty defs) in
  let ctx' = extend_ctx ctx binds in 
  let def_checker (name, ty, (p, c)) =
    match ty with
    | Type.Arrow (ty1, ty2) ->
        let b = pattern_check ctx' p ty1 in
        let ctx'' = extend_ctx ctx' b in
        computation_check ctx'' c ty2
    | _ ->
        Error.typing ~loc 
          ("The recursive function `%t` @,is annotated with the non-function"
          ^^ " type `%t`. @,Only functions are allowed in recursive"
          ^^ " definitions.")
          (CoreTypes.Variable.print name) (Type.print_vty ([], ty))
  in
  List.iter def_checker defs;
  let vars = 
    Assoc.to_list binds 
    |> List.map (fun (x, ty) -> (x, Ctx.generalize ctx true ty))
  in
  List.iter
    (fun (name, ty, (p, c)) -> Exhaust.is_irrefutable p ; Exhaust.check_comp c)
    defs ;
  (vars, ctx')