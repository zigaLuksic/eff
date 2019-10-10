open CoreUtils
module Syntax = AnnotatedSyntax
module Ctx = SimpleCtx

type state = Ctx.t

let initial_state = Ctx.empty


let rec types_match ty1 ty2 =
  match ty1, ty2 with
  | Type.TyParam ty_par1, Type.TyParam ty_par2 ->
      CoreTypes.TyParam.compare ty_par1 ty_par2 = 0
  | Type.Basic x1, Type.Basic x2 -> x1 = x2
  | Type.Apply (name1, tys1), Type.Apply (name2, tys2) ->
      name1 = name2 && List.for_all2 types_match tys1 tys2
  | Type.Apply (name, tys), ty | ty, Type.Apply (name, tys) -> (
      if Tctx.transparent ~loc:Location.unknown name then
        match Tctx.ty_apply ~loc:Location.unknown name tys with
        | Tctx.Inline t -> types_match t ty
        | Tctx.Sum _ -> assert false (* not transparent *)
      else false )
  | Type.Tuple tys1, Type.Tuple tys2 -> 
      List.for_all2 types_match tys1 tys2
  | Type.Arrow (in_ty1, out_ty1), Type.Arrow (in_ty2, out_ty2) 
  | Type.Handler (in_ty1, out_ty1), Type.Handler (in_ty2, out_ty2) ->
      types_match in_ty2 in_ty1 && types_match out_ty1 out_ty2      
  | _, _ -> false

let extend_ctx ctx binds =
  Assoc.fold_left
    (fun acc (x, ty) -> Ctx.extend acc x (Ctx.generalize ctx true ty)) 
    ctx binds

let rec pattern_check ctx p ty =
  let loc = p.at in
  match p.it with
  | Syntax.PVar x -> Assoc.of_list [(x, ty)]
  | Syntax.PAnnotated (p, ann_ty) ->
      if types_match ty ann_ty then pattern_check ctx p ann_ty else
        Error.typing ~loc 
          ( "Pattern is checked against type [%t] but annotated with"
          ^^ " type [%t]." )
          (Type.print ([], ty)) (Type.print ([], ann_ty))
  | Syntax.PAs (p, x) ->
      Assoc.update x ty (pattern_check ctx p ty)
  | Syntax.PNonbinding -> Assoc.empty
  | Syntax.PConst const ->
      let real_ty = Type.Basic (Const.infer_ty const) in
      if types_match ty real_ty then Assoc.empty else
        Error.typing ~loc 
          ("Constant pattern [%t] was checked against type [%t] but is of "
          ^^ "type [%t].")
          (Const.print const) (Type.print ([], ty))
          (Type.print ([], real_ty))
  | Syntax.PTuple ps -> (
      match ty with
      | Type.Tuple tys ->
          let rec checker ps tys binds =
            match ps, tys with
            | [], [] -> binds
            | p :: ps, ty :: tys ->
                let b = pattern_check ctx p ty in
                let unique_check k = (
                  match Assoc.lookup k binds with
                  | None -> ()
                  | Some _ ->
                      Error.typing ~loc 
                        ( "Variable [%t] is already used in the pattern." )
                        (CoreTypes.Variable.print k) )
                in
                let () = List.iter unique_check (Assoc.keys_of b) in
                let binds' = Assoc.concat binds b in
                checker ps tys binds'
            | [], tys ->
                Error.typing ~loc 
                  ( "Tuple pattern was checked against type [%t] but does not "
                  ^^ "have enough components to typecheck." )
                  (Type.print ([], ty))
            | ps, [] ->
                Error.typing ~loc 
                  ( "Tuple pattern was checked against type [%t] but has too "
                  ^^ "many components to typecheck." )
                  (Type.print ([], ty))
          in
          checker ps tys Assoc.empty
      | _ ->
          Error.typing ~loc 
            ( "A tuple was checked against the incompatible type [%t]." )
            (Type.print ([], ty))
      )
  | Syntax.PVariant (lbl, arg_p_opt) -> (
      match Tctx.infer_variant lbl with
      | None -> 
          Error.typing ~loc 
            "Constructor pattern [%t] does not belong to a known type."
            (CoreTypes.Label.print lbl)
      | Some (real_ty, arg_ty_opt) -> (
          let binds =
          match arg_p_opt, arg_ty_opt with
          | None, Some arg_ty ->
              Error.typing ~loc 
                ( "Constructor pattern [%t] requires argument of type [%t] but"
                ^^ " was used with no arguments." )
                (CoreTypes.Label.print lbl) (Type.print ([], arg_ty))
          | Some arg_p, None ->
              Error.typing ~loc 
                ( "Constructor pattern [%t] does not accept arguments." )
                (CoreTypes.Label.print lbl)
          | None, None -> Assoc.empty
          | Some arg_p, Some arg_ty -> 
              (pattern_check ctx arg_p arg_ty)
          in
          if types_match ty real_ty then binds else
            Error.typing ~loc 
              ("Constructor pattern [%t] is checked against type [%t] but "
              ^^ "belongs to type [%t].")
              (CoreTypes.Label.print lbl) (Type.print ([], ty))
              (Type.print ([], real_ty)))
      )

and value_check ctx v ty =
  let loc = v.at in
  match v.it with
  | Syntax.Var x -> 
      let real_ty = Ctx.lookup ~loc ctx x in
      if types_match ty real_ty then () else
        Error.typing ~loc 
          "Variable [%t] was checked against type [%t] but is of type [%t]."
          (CoreTypes.Variable.print x) (Type.print ([], ty))
          (Type.print ([], real_ty))
  | Syntax.Const const -> 
      let real_ty = Type.Basic (Const.infer_ty const) in
      if types_match ty real_ty then () else
        Error.typing ~loc 
          "Constant [%t] was checked against type [%t] but is of type [%t]."
          (Const.print const) (Type.print ([], ty))
          (Type.print ([], real_ty))
  | Syntax.Tuple vs -> (
      match ty with
      | Type.Tuple tys ->
          let rec checker vs tys =
            match vs, tys with
            | [], [] -> ()
            | v :: vs, ty :: tys ->
                (value_check ctx v ty; checker vs tys)
            | [], tys ->
                Error.typing ~loc 
                  ( "Tuple was checked against type [%t] but does not have "
                  ^^ "enough components to typecheck." )
                  (Type.print ([], ty))
            | vs, [] ->
                Error.typing ~loc 
                  ( "Tuple was checked against type [%t] but has too many "
                  ^^ "components to typecheck." )
                  (Type.print ([], ty))
          in
          checker vs tys
      | _ ->
          Error.typing ~loc 
            ( "A tuple was checked against the incompatible type [%t]." )
            (Type.print ([], ty))
      )
  | Syntax.VAnnotated (v, ann_ty) ->
      if types_match ty ann_ty then value_check ctx v ann_ty else
        Error.typing ~loc 
          ( "Value is checked against type [%t] but annotated with"
          ^^ " type [%t]." )
          (Type.print ([], ty)) (Type.print ([], ann_ty))
  | Syntax.Variant (lbl, arg_opt) -> (
      match Tctx.infer_variant lbl with
      | None -> 
          Error.typing ~loc 
            "Constructor [%t] does not belong to a known type."
            (CoreTypes.Label.print lbl)
      | Some (real_ty, arg_ty_opt) -> ((
          match arg_opt, arg_ty_opt with
          | None, Some arg_ty ->
              Error.typing ~loc 
                ( "Constructor [%t] requires argument of type [%t] but was "
                ^^ "used with no arguments." )
                (CoreTypes.Label.print lbl) (Type.print ([], arg_ty))
          | Some arg, None ->
              Error.typing ~loc 
                ( "Constructor [%t] does not accept arguments." )
                (CoreTypes.Label.print lbl)
          | None, None -> ()
          | Some arg, Some arg_ty -> 
              (value_check ctx arg arg_ty)
          ); if types_match ty real_ty then () else
          Error.typing ~loc 
            ("Constructor [%t] is checked against type [%t] but belongs to "
            ^^ "type [%t].")
            (CoreTypes.Label.print lbl) (Type.print ([], ty)) 
            (Type.print ([], real_ty)))
      )
  | Syntax.Lambda (p, c) -> (
      match ty with
      | Type.Arrow (ty1, ty2) ->
          let binds = pattern_check ctx p ty1 in
          computation_check (extend_ctx ctx binds) c ty2
      | _ ->
          Error.typing ~loc 
            ( "A function was checked against the incompatible type [%t]." )
            (Type.print ([], ty))
      )
  | Syntax.Effect op -> (
      match ty with
      | Type.Arrow (ty1, ty2) -> (
          match Ctx.infer_effect ctx op with
          | None ->
              Error.typing ~loc 
                ( "Effect [%t] has no known type." )
                (CoreTypes.Effect.print op)
          | Some (t1, t2) -> 
              if types_match ty1 t1 && types_match ty2 t2 then () else
                Error.typing ~loc 
                  ( "Effect [%t] has type [%t] but was checked against the "
                   ^^ "type [%t]." )
                  (CoreTypes.Effect.print op) (Type.print ([], ty))
                  (Type.print ([], ty))
          )
      | _ ->
          Error.typing ~loc 
            ( "Effect [%t] was checked against an incompatible type [%t]." )
            (CoreTypes.Effect.print op) (Type.print ([], ty))
      )
  | Syntax.Handler { Syntax.effect_clauses= ops; Syntax.value_clause= (p, c) }
    -> (
      match ty with
      | Type.Handler (ty1, ty2) -> (
          effect_clauses_check ctx ops (ty1, ty2);
          let binds = pattern_check ctx p ty1 in
          computation_check (extend_ctx ctx binds) c ty2
          )
      | _ ->
          Error.typing ~loc 
            ( "A handler was checked against an incompatible type [%t]." )
            (Type.print ([], ty))
      )


and value_synth ctx v =
  let loc = v.at in
  match v.it with
  | Syntax.Var x -> Ctx.lookup ~loc ctx x
  | Syntax.Const const -> Type.Basic (Const.infer_ty const)
  | Syntax.Tuple vs ->
      Type.Tuple (left_to_right_map (value_synth ctx) vs)
  | Syntax.VAnnotated (v, ty) -> (value_check ctx v ty; ty)
  | Syntax.Variant (lbl, arg_opt) -> (
      match Tctx.infer_variant lbl with
      | None -> 
          Error.typing ~loc 
            "Constructor [%t] does not belong to a known type."
            (CoreTypes.Label.print lbl)
      | Some (ty, arg_ty_opt) -> (
          match arg_opt, arg_ty_opt with
          | None, Some arg_ty ->
              Error.typing ~loc 
                ( "Constructor [%t] requires argument of type [%t] but was "
                ^^ "used with no arguments." )
                (CoreTypes.Label.print lbl) (Type.print ([], arg_ty))
          | Some arg, None ->
              Error.typing ~loc 
                ( "Constructor [%t] does not accept arguments." )
                (CoreTypes.Label.print lbl)
          | None, None -> ty
          | Some arg, Some arg_ty -> 
              (value_check ctx arg arg_ty; ty)
          )
      )
  | Syntax.Lambda abs ->
      Error.typing ~loc 
        ( "Cannot synthesize type of function. Please provide annotations." )
  | Syntax.Effect op -> (
      match Ctx.infer_effect ctx op with
      | None ->
          Error.typing ~loc 
            ( "Effect [%t] has no known type." )
            (CoreTypes.Effect.print op)
      | Some (t1, t2) -> 
          Type.Arrow (t1, t2)
    )
  | Syntax.Handler { Syntax.effect_clauses= ops; Syntax.value_clause= a_val }
    ->
      Error.typing ~loc 
        ( "Cannot synthesize type of handler. Please provide annotations." )

  
and computation_check ctx c ty =
  let loc = c.at in
  match c.it with
  | Syntax.CAnnotated (c, ann_ty) ->
      if types_match ty ann_ty then computation_check ctx c ann_ty else
        Error.typing ~loc 
          ( "Computation is checked against type [%t] but annotated with"
          ^^ " type [%t]." )
          (Type.print ([], ty)) (Type.print ([], ann_ty))
  | Syntax.Apply (v1, v2) ->
      let ty1 = value_synth ctx v1 in
      (match ty1 with
      | Type.Arrow(in_ty, out_ty) ->
          let () = value_check ctx v2 in_ty in
          if types_match ty out_ty then () else
          Error.typing ~loc 
            ("Function returns values of type [%t] but its return type is "
            ^^ "checked against type [%t].")
            (Type.print ([], out_ty)) (Type.print ([], ty))
      | real_ty ->
          Error.typing ~loc 
            ("Trying to apply a non-function element of type [%t].")
            (Type.print ([], real_ty)) )
  | Syntax.Value v -> value_check ctx v ty
  | Syntax.Match (v, []) -> value_check ctx v Type.empty_ty
  | Syntax.Match (v, lst) ->
      let in_ty = value_synth ctx v in
      let check_case (p, c') =
        let binds = pattern_check ctx p in_ty in
        computation_check (extend_ctx ctx binds) c' ty
      in
      List.iter check_case lst
  | Syntax.Handle (v1, c2) ->
      let ty1 = value_synth ctx v1 in
      (match ty1 with
      | Type.Handler (in_ty, out_ty) ->
          let () = computation_check ctx c in_ty in
          if types_match ty out_ty then () else
          Error.typing ~loc 
            ("Handler returns values of type [%t] but its return type is "
            ^^ "checked against type [%t].")
            (Type.print ([], out_ty)) (Type.print ([], ty))
      | real_ty ->
          Error.typing ~loc 
            ("Trying to handle with a non-handler element of type [%t].")
            (Type.print ([], real_ty)) )
  | Syntax.Let (defs, c) ->
      let def_checker binds (p, c) =
        let c_ty = computation_synth ctx c in
        let b = pattern_check ctx p c_ty in
        Assoc.concat binds b
      in
      let binds = List.fold_left def_checker Assoc.empty defs in
      computation_check (extend_ctx ctx binds) c ty
  | Syntax.LetRec (defs, c) ->
      failwith "TODO"
  | Syntax.Check c ->
      if types_match ty Type.unit_ty then
        ignore (computation_synth ctx c)
      else
        Error.typing ~loc 
          ("Command [Check] is used to display types at runtime and returns "
          ^^ "[%t]. It was instead checked against type [%t].")
          (Type.print ([], Type.unit_ty)) (Type.print ([], ty))


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
            ("Trying to apply a non-function element of type [%t].")
            (Type.print ([], real_ty)) )
  | Syntax.Value v -> value_synth ctx v
  | Syntax.Match (v, []) ->
      Error.typing ~loc 
        ("Cannot synthesize computation type when matching something of [%t] "
        ^^ "type. Please provide annotations.")
        (Type.print ([], Type.empty_ty))
  | Syntax.Match (v, (p, c') :: []) ->
      let in_ty = value_synth ctx v in
      let binds = pattern_check ctx p in_ty in
      computation_synth (extend_ctx ctx binds) c'
  | Syntax.Match (v, lst) ->
      Error.typing ~loc 
        ("Unable to synthesize type of a branching match statement. "
        ^^ "Please provide annotations.")
  | Syntax.Handle (v1, c2) ->
      let ty1 = value_synth ctx v1 in
      (match ty1 with
      | Type.Handler (in_ty, out_ty) ->
          let () = computation_check ctx c in_ty in
          out_ty
      | real_ty ->
          Error.typing ~loc 
            ("Trying to handle with a non-handler element of type [%t].")
            (Type.print ([], real_ty)) )
  | Syntax.Let (defs, c) ->
      let def_checker binds (p, c) =
        let c_ty = computation_synth ctx c in
        let b = pattern_check ctx p c_ty in
        Assoc.concat binds b
      in
      let binds = List.fold_left def_checker Assoc.empty defs in
      computation_synth (extend_ctx ctx binds) c
  | Syntax.LetRec (defs, c) ->
      failwith "TODO"
  | Syntax.Check c -> ignore (computation_synth ctx c); Type.unit_ty

and effect_clauses_check ctx ops (ty1, ty2) =
  let rec checker (op, (px, pk, c_op)) =
    match Ctx.infer_effect ctx op with
    | None ->
        Error.typing ~loc:px.at 
          ( "Effect [%t] has no known type." )
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
  let ty = computation_synth ctx c in
  Exhaust.check_comp c ;
  (ctx, Ctx.generalize ctx true ty)

let infer_top_let ~loc ctx defs =
  let def_checker binds (p, c) =
    let c_ty = computation_synth ctx c in
    let b = pattern_check ctx p c_ty in
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
  failwith "TODO"