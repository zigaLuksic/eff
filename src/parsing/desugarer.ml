(** Desugaring of syntax into the core language. *)

open CoreUtils
module T = Type
module Sugared = SugaredSyntax
module Untyped = AnnotatedSyntax


type state =
  { context: (string, CoreTypes.Variable.t) Assoc.t
  ; effect_symbols: (string, CoreTypes.Effect.t) Assoc.t
  ; theory_symbols: (string, CoreTypes.Theory.t) Assoc.t
  ; tyname_symbols: (string, CoreTypes.TyName.t) Assoc.t
  ; constructors: (string, CoreTypes.Label.t) Assoc.t }

let initial_state =
  let list_cons = (CoreTypes.cons_annot, CoreTypes.cons) in
  let list_nil = (CoreTypes.nil_annot, CoreTypes.nil) in
  let initial_types =
    Assoc.of_list
      [ ("bool", CoreTypes.bool_tyname)
      ; ("int", CoreTypes.int_tyname)
      ; ("unit", CoreTypes.unit_tyname)
      ; ("string", CoreTypes.string_tyname)
      ; ("float", CoreTypes.float_tyname)
      ; ("list", CoreTypes.list_tyname)
      ; ("empty", CoreTypes.empty_tyname) ]
  in
  { context= Assoc.empty
  ; effect_symbols= Assoc.empty
  ; theory_symbols= Assoc.empty
  ; tyname_symbols= initial_types
  ; constructors= Assoc.of_list [list_cons; list_nil] }

let add_loc t loc = {it= t; at= loc}

let effect_to_symbol state name =
  match Assoc.lookup name state.effect_symbols with
  | Some sym -> (state, sym)
  | None ->
      let sym = CoreTypes.Effect.fresh name in
      let effect_symbols' = Assoc.update name sym state.effect_symbols in
      ({state with effect_symbols= effect_symbols'}, sym)

let theory_to_symbol state name =
  match Assoc.lookup name state.theory_symbols with
  | Some sym -> (state, sym)
  | None ->
      let sym = CoreTypes.Theory.fresh name in
      let theory_symbols' = Assoc.update name sym state.theory_symbols in
      ({state with theory_symbols= theory_symbols'}, sym)

let tyname_to_symbol state name =
  match Assoc.lookup name state.tyname_symbols with
  | Some sym -> (state, sym)
  | None ->
      let sym = CoreTypes.TyName.fresh name in
      let tyname_symbols' = Assoc.update name sym state.tyname_symbols in
      ({state with tyname_symbols= tyname_symbols'}, sym)

(* ==================== Desugaring of types. ==================== *)

let rec desugar_vtype type_sbst state =
  let rec desugar_vty state {it= t; at= loc} =
    match t with
    | Sugared.TyApply (t, tys) ->
        let state', t' = tyname_to_symbol state t in
        let state'', tys' = fold_map desugar_vty state' tys in
        (state'', T.Apply (t', tys'))
    | Sugared.TyParam t -> (
        match Assoc.lookup t type_sbst with
        | None -> Error.syntax ~loc "Unbound type parameter '%s." t
        | Some p -> (state, T.TyParam p) )
    | Sugared.TyArrow (t1, t2) ->
        let state', t1' = desugar_vty state t1 in
        let state'', t2' = desugar_ctype type_sbst state' t2 in
        (state'', T.Arrow (t1',t2'))
    | Sugared.TyTuple lst ->
        let state', lst' = fold_map desugar_vty state lst in
        (state', T.Tuple lst')
    | Sugared.TyHandler (t1, t2) ->
        let state', t1' = desugar_ctype type_sbst state t1 in
        let state'', t2' = desugar_ctype type_sbst state' t2 in
        (state'', T.Handler (t1', t2'))
    | Sugared.TyCTySig _ | Sugared.TyCTyTheory _ ->
        Error.typing ~loc
          "Expected a value type, but a computation type was given."
  in
  desugar_vty state

and desugar_ctype type_sbst state ty =
  match ty.it with
  | Sugared.TyCTySig (vty, effs) ->
      let state', vty' = desugar_vtype type_sbst state vty in
      let state'', effs' = fold_map effect_to_symbol state' effs in
      (state'', T.CTySig (vty', effs'))
  | Sugared.TyCTyTheory (vty, theory) ->
      let state', vty' = desugar_vtype type_sbst state vty in
      let state'', theory' = theory_to_symbol state' theory in
      (state'', T.CTyTheory (vty', theory'))
  | Sugared.TyParam _ | Sugared.TyArrow _ | Sugared.TyTuple _ 
  | Sugared.TyHandler _ | Sugared.TyApply _ ->
      (* Auto-transform to pure computation type *)
      let state', vty' = desugar_vtype type_sbst state ty in
      (state', T.CTySig(vty', []))

(** [free_type_params t] returns all free type params in [t]. *)
let free_type_params t =
  let rec ty_params {it= t; at= loc} =
    match t with
    | Sugared.TyApply (_, tys) -> List.map ty_params tys |> List.flatten
    | Sugared.TyParam s -> [s]
    | Sugared.TyArrow (t1, t2) -> ty_params t1 @ ty_params t2
    | Sugared.TyTuple lst -> List.map ty_params lst |> List.flatten
    | Sugared.TyHandler (t1, t2) -> ty_params t1 @ ty_params t2
    | Sugared.TyCTySig (vty, _) -> ty_params vty
    | Sugared.TyCTyTheory (vty, _) -> ty_params vty
  in
  unique_elements (ty_params t)

let syntax_to_core_params ts =
  Assoc.map_of_list (fun p -> (p, Type.fresh_ty_param ())) ts

(** [desugar_tydef state params def] desugars the type definition with parameters
    [params] and definition [def]. *)
let desugar_tydef state params def =
  let ty_sbst = syntax_to_core_params params in
  let state', def' =
    match def with
    | Sugared.TySum assoc ->
        let aux_desug st (lbl, cons) =
          let unsugared_lbl =
            match Assoc.lookup lbl st.constructors with
            | None -> failwith "unreachable"
            | Some lbl' -> lbl'
          in
          match cons with
          | None -> (st, (unsugared_lbl, None))
          | Some t ->
              let st', t' = desugar_vtype ty_sbst st t in
              (st', (unsugared_lbl, Some t'))
        in
        let constructors =
          (* desugar constructor names to Symbol and add to state *)
          let aux (lbl, cons) =
            let unsugared_lbl =
              match Assoc.lookup lbl state.constructors with
              | None -> CoreTypes.Label.fresh lbl
              | Some lbl -> lbl
              (* Caught by inference for better error *)
            in
            (lbl, unsugared_lbl)
          in
          let new_cons = Assoc.kmap aux assoc in
          Assoc.concat new_cons state.constructors
        in
        (* desugar and rename constructors in type *)
        let state', assoc' =
          Assoc.kfold_map aux_desug {state with constructors} assoc
        in
        (state', Tctx.Sum assoc')
    | Sugared.TyInline t ->
        let state', t' = desugar_vtype ty_sbst state t in
        (state', Tctx.Inline t')
  in
  (state', (Assoc.values_of ty_sbst, def'))

(** [desugar_tydefs defs] desugars the simultaneous type definitions [defs]. *)
let desugar_tydefs state sugared_defs =
  let desugar_fold st (name, (params, def)) =
    (* First desugar the type names *)
    let st', sym = tyname_to_symbol st name in
    (* Then the types themselves *)
    let st'', (params', def') = desugar_tydef st' params def in
    (st'', (sym, (params', def')))
  in
  Assoc.kfold_map desugar_fold state sugared_defs

(* ========== Desugaring of expressions and computations. ========== *)

(** [fresh_var opt] creates a fresh variable on each call *)
let fresh_var = function
  | None -> CoreTypes.Variable.fresh "$anon"
  | Some x -> CoreTypes.Variable.fresh x

let id_abstraction loc =
  let x = fresh_var (Some "$id_par") in
  ( add_loc (Untyped.PVar x) loc
  , add_loc (Untyped.Value (add_loc (Untyped.Var x) loc)) loc )

let desugar_pattern state ?(initial_forbidden = []) p =
  let vars = ref Assoc.empty in
  let forbidden = ref initial_forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~loc:p.at
        "Variable `%s` occurs multiple times in a single pattern" x
    else
      let var = fresh_var (Some x) in
      vars := Assoc.update x var !vars ;
      forbidden := x :: !forbidden ;
      var
  in
  let rec desugar_pattern state {it= p; at= loc} =
    let state', p' =
      match p with
      | Sugared.PVar x ->
          let x = new_var x in
          (state, Untyped.PVar x)
      | Sugared.PTuple ps ->
          let state', ps' = fold_map desugar_pattern state ps in
          (state', Untyped.PTuple ps')
      | Sugared.PVariant (lbl, p) -> (
        match Assoc.lookup lbl state.constructors with
        | None -> Error.typing ~loc "Unbound constructor `%s`." lbl
        | Some cons_lbl -> (
          match p with
          | Some p ->
              let state', p' = desugar_pattern state p in
              (state', Untyped.PVariant (cons_lbl, Some p'))
          | None -> (state, Untyped.PVariant (cons_lbl, None)) ) )
      | Sugared.PConst c -> (state, Untyped.PConst c)
      | Sugared.PNonbinding -> (state, Untyped.PNonbinding)
    in
    (state', add_loc p' loc)
  in
  let state', p' = desugar_pattern state p in
  (state', !vars, p')

(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec desugar_expression state {it= t; at= loc} =
  let state', w, e =
    match t with
    | Sugared.Var x -> (
      match Assoc.lookup x state.context with
      | Some n -> (state, [], Untyped.Var n)
      | None -> Error.typing ~loc "Variable `%s` is unknown." x )
    | Sugared.Const k -> (state, [], Untyped.Const k)
    | Sugared.Annotated (t, ty) -> (
        match free_type_params ty with 
        | _ :: _ -> 
            Error.syntax ~loc 
              "EEFF currently does not support type parameters outside type definitions."
        | [] ->
            let state', w, e = desugar_expression state t in
            let state'', ty' = desugar_vtype Assoc.empty state' ty in
            (state'', w, Untyped.VAnnotated (e, ty')) )
    | Sugared.Lambda a ->
        let state', a' = desugar_abstraction state a in
        (state', [], Untyped.Lambda a')
    | Sugared.Function cs ->
        let x = fresh_var (Some "$function") in
        let state', cs' = fold_map desugar_abstraction state cs in
        ( state'
        , []
        , Untyped.Lambda
            ( add_loc (Untyped.PVar x) loc
            , add_loc (Untyped.Match (add_loc (Untyped.Var x) loc, cs')) loc )
        )
    | Sugared.Handler cs ->
        let state', h' = desugar_handler loc state cs in
        (state', [], Untyped.Handler h')
    | Sugared.Tuple ts ->
        let state', w, es = desugar_expressions state ts in
        (state', w, Untyped.Tuple es)
    | Sugared.Variant (lbl, t) -> (
      match Assoc.lookup lbl state.constructors with
      | None -> Error.typing ~loc "Unknown constructor `%s`." lbl
      | Some cons_lbl -> (
        match t with
        | Some t ->
            let state', w, e = desugar_expression state t in
            (state', w, Untyped.Variant (cons_lbl, Some e))
        | None -> (state, [], Untyped.Variant (cons_lbl, None)) ) )
    (* Terms that are desugared into computations. We list them explicitly in
       order to catch any future constructs. *)
    | Sugared.Apply _ | Sugared.Match _ | Sugared.Let _ | Sugared.LetRec _
     |Sugared.Handle _ | Sugared.Conditional _ | Sugared.Check _
     |Sugared.Effect _ ->
        let x = fresh_var (Some "$bind") in
        let state', c = desugar_computation state {it= t; at= loc} in
        let w = [(add_loc (Untyped.PVar x) loc, c)] in
        (state', w, Untyped.Var x)
  in
  (state', w, add_loc e loc)

and desugar_computation state {it= t; at= loc} =
  let if_then_else e c1 c2 =
    let true_p = add_loc (Untyped.PConst Const.of_true) c1.at in
    let false_p = add_loc (Untyped.PConst Const.of_false) c2.at in
    Untyped.Match (e, [(true_p, c1); (false_p, c2)])
  in
  let state', w, c =
    match t with
    | Sugared.Apply
        ( {it= Sugared.Apply ({it= Sugared.Var "&&"; at= loc1}, t1); at= loc2}
        , t2 ) ->
        let state', w1, e1 = desugar_expression state t1 in
        let untyped_false loc = add_loc (Untyped.Const Const.of_false) loc in
        let state'', c1 = desugar_computation state' t2 in
        let c2 = add_loc (Untyped.Value (untyped_false loc2)) loc2 in
        (state'', w1, if_then_else e1 c1 c2)
    | Sugared.Apply
        ( {it= Sugared.Apply ({it= Sugared.Var "||"; at= loc1}, t1); at= loc2}
        , t2 ) ->
        let state', w1, e1 = desugar_expression state t1 in
        let untyped_true loc = add_loc (Untyped.Const Const.of_true) loc in
        let c1 = add_loc (Untyped.Value (untyped_true loc2)) loc2 in
        let state'', c2 = desugar_computation state' t2 in
        (state'', w1, if_then_else e1 c1 c2)
    | Sugared.Apply (t1, t2) ->
        let state', w1, e1 = desugar_expression state t1 in
        let state'', w2, e2 = desugar_expression state' t2 in
        (state'', w1 @ w2, Untyped.Apply (e1, e2))
    | Sugared.Annotated (t, ty) -> (
        match free_type_params ty with 
        | _ :: _ -> 
            Error.syntax ~loc 
              "EEFF currently does not support type parameters outside type definitions."
        | [] ->
            let state', c = desugar_computation state t in
            let state'', ty' = desugar_ctype Assoc.empty state' ty in
            (state'', [], Untyped.CAnnotated (c, ty')) )
    | Sugared.Effect (eff, t) -> 
        let state', eff' = effect_to_symbol state eff in
        let state'', w, e = desugar_expression state' t in
        (state'', w, Untyped.Effect (eff', e))
    | Sugared.Match (t, cs) -> 
        let state', w, e = desugar_expression state t in
        let state'', val_cs' = fold_map desugar_abstraction state' cs in
        (state'', w, Untyped.Match (e, val_cs'))
    | Sugared.Handle (t1, t2) ->
        let state', w1, e1 = desugar_expression state t1 in
        let state'', c2 = desugar_computation state' t2 in
        (state'', w1, Untyped.Handle (e1, c2))
    | Sugared.Conditional (t, t1, t2) ->
        let state', w, e = desugar_expression state t in
        let state'', c1 = desugar_computation state' t1 in
        let state''', c2 = desugar_computation state'' t2 in
        (state''', w, if_then_else e c1 c2)
    | Sugared.Check t ->
        let state', c = desugar_computation state t in
        (state', [], Untyped.Check c)
    | Sugared.Let (defs, t) ->
        let aux_desugar (p, c) (fold_state, defs, forbidden) =
          let check_forbidden (x, _) =
            if List.mem x forbidden then
              Error.syntax ~loc:p.at "Several definitions of value `%s`." x
          in
          let state', p_vars, p' = desugar_pattern state p in
          Assoc.iter check_forbidden p_vars ;
          let state'', c' = desugar_computation state' c in
          ( {state'' with context= Assoc.concat p_vars fold_state.context}
          , (p', c') :: defs
          , Assoc.keys_of p_vars @ forbidden )
        in
        let state', defs', _ =
          List.fold_right aux_desugar defs (state, [], [])
        in
        let state'', c = desugar_computation state' t in
        ({state'' with context=state.context}, [], Untyped.Let (defs', c))
    | Sugared.LetRec (defs, t) ->
        let aux_desugar (x, ty, abs) (fold_state, ns, forbidden) =
          if List.mem x forbidden then
            Error.syntax ~loc:abs.at 
            "Several definitions of recursive function `%s`." x ;
          let n = fresh_var (Some x) in
          ( {state with context= Assoc.update x n fold_state.context}
          , n :: ns
          , x :: forbidden )
        in
        let state', ns, _ = List.fold_right aux_desugar defs (state, [], []) in
        let desugar_defs (n, (_, ty, c)) (st, defs) =
          let st', c = desugar_let_rec st c in
          let st'', ty = desugar_vtype Assoc.empty st' ty in
          (st'', (n, ty, c) :: defs)
        in
        let state'', defs' = 
          List.fold_right desugar_defs (List.combine ns defs) (state', [])
        in
        let state''', c = desugar_computation state'' t in
        ({state''' with context=state.context}, [], Untyped.LetRec (defs', c))
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | Sugared.Var _ | Sugared.Const _ | Sugared.Tuple _
    | Sugared.Variant _ | Sugared.Lambda _
    | Sugared.Function _ | Sugared.Handler _ ->
        let state', w, e = desugar_expression state {it= t; at= loc} in
        (state', w, Untyped.Value e)
  in
  match w with
  | [] -> (state', add_loc c loc)
  | _ :: _ -> (state', add_loc (Untyped.Let (w, add_loc c loc)) loc)

and desugar_abstraction state (p, t) =
  let state', p_vars, p' = desugar_pattern state p in
  let new_context = Assoc.concat p_vars state'.context in
  let state'', c = desugar_computation {state' with context= new_context} t in
  ({state'' with context= state.context}, (p', c))

and desugar_abstraction2 state (p1, p2, t) =
  let state', p_vars1, p1' = desugar_pattern state p1 in
  let state'', p_vars2, p2' = desugar_pattern state' p2 in
  let new_context =
    Assoc.concat (Assoc.concat p_vars1 p_vars2) state''.context
  in
  let state''', t' =
    desugar_computation {state'' with context= new_context} t
  in
  ({state''' with context= state.context}, (p1', p2', t'))

and desugar_let_rec state {it= exp; at= loc} =
  match exp with
  | Sugared.Lambda a -> desugar_abstraction state a
  | Sugared.Function cs ->
      let x = fresh_var (Some "$let_rec_function") in
      let state', cs = fold_map desugar_abstraction state cs in
      let new_match = Untyped.Match (add_loc (Untyped.Var x) loc, cs) in
      (state', (add_loc (Untyped.PVar x) loc, add_loc new_match loc))
  | _ ->
      Error.syntax ~loc
        "This kind of expression is not allowed in a recursive definition."

and desugar_expressions state = function
  | [] -> (state, [], [])
  | t :: ts ->
      let state', w, e = desugar_expression state t in
      let state'', ws, es = desugar_expressions state' ts in
      (state'', w @ ws, e :: es)

and desugar_handler loc state
    { Sugared.effect_clauses= eff_cs
    ; Sugared.value_clause= val_cs } =
  (* Construct a desugared handler with match statements. *)
  let rec group_eff_cs (eff, a2) assoc =
    match Assoc.lookup eff assoc with
    | None -> Assoc.update eff [a2] assoc
    | Some a2s -> Assoc.replace eff (a2 :: a2s) assoc
  in
  let rec construct_eff_clause state (eff, eff_cs_lst) =
    (* transform string name to CoreTypes.Effect.t *)
    let state', eff' = effect_to_symbol state eff in
    match eff_cs_lst with
    | [] -> assert false
    | [a2] ->
        let state'', a2' = desugar_abstraction2 state' a2 in
        (state'', (eff', a2'))
    | a2::a2s ->
        Error.syntax ~loc:loc
          ("Handler contains several clauses for the effect `%s`."
          ^^ "You should use a match statement inside a single clause if needed.")
           eff
  in
  (* group eff cases by effects into lumps to transform into matches *)
  let collected_eff_cs = Assoc.fold_right group_eff_cs eff_cs Assoc.empty in
  (* construct match cases for effects with more than one pattern *)
  let state', untyped_eff_cs =
    Assoc.kfold_map construct_eff_clause state collected_eff_cs
  in
  (* construct match case for value *)
  let state'', untyped_val_a =
    match val_cs with
    | None -> (state', id_abstraction loc)
    | Some c -> desugar_abstraction state' c
  in
  ( state''
  , { Untyped.effect_clauses= untyped_eff_cs
    ; Untyped.value_clause= untyped_val_a } )

(* ========== Desugaring of templates. ========== *)

let rec desugar_template state {it= tmpl; at= loc} =
  (* Fix the first two arguments as they do not change *)
  let if_then_else e c1 c2 =
    let true_p = add_loc (Untyped.PConst Const.of_true) c1.at in
    let false_p = add_loc (Untyped.PConst Const.of_false) c2.at in
    Template.Match (e, [(true_p, c1); (false_p, c2)])
  in
  let state', w, tmpl' =
    match tmpl with 
    | Sugared.TLet (defs, tmpl) ->
        let aux_desugar (p, c) (fold_state, defs, forbidden) =
          let check_forbidden (x, _) =
            if List.mem x forbidden then
              Error.syntax ~loc:p.at "Several definitions of value `%s`." x
          in
          let state', p_vars, p' = desugar_pattern state p in
          Assoc.iter check_forbidden p_vars ;
          let _, c' = desugar_computation state' c in
          ( {state with context= Assoc.concat p_vars fold_state.context}
          , (p', c') :: defs
          , Assoc.keys_of p_vars @ forbidden )
        in
        let state', defs', _ =
          List.fold_right aux_desugar defs (state, [], [])
        in
        let state'', tmpl' = desugar_template state' tmpl in
        ({state'' with context=state.context}, [], Template.Let (defs', tmpl'))
    | Sugared.TLetRec (defs, tmpl) ->
        Error.syntax ~loc 
          ("Templates currently do not support a `let rec` constructor. "
          ^^ "To use recursion, nest a `let rec` construct as a computation "
          ^^ "term of a `let` template.")
    | Sugared.TMatch (t, tmpls) ->
        let desugar_case st (p, tmpl) =
          let st', p_vars, p' = desugar_pattern st p in
          let new_context = Assoc.concat p_vars st'.context in
          let st'', tmpl' = 
            desugar_template {st' with context= new_context} tmpl 
          in
          ({st'' with context= st.context}, (p', tmpl'))
        in
        let state', w, e = desugar_expression state t in
        let (state'', tmpls') = fold_map desugar_case state' tmpls in
        (state'', w, Template.Match (e, tmpls'))
    | Sugared.TConditional (t, tmpl1, tmpl2) ->
        let state', w, e = desugar_expression state t in
        let state'', tmpl1' = desugar_template state' tmpl1 in
        let state''', tmpl2' = desugar_template state' tmpl2 in
        (state''', w, if_then_else e tmpl1' tmpl2')
    | Sugared.TApply (var, t) -> (
        match Assoc.lookup var state.context with
        | None ->
            Error.typing ~loc
            ("Variable `%s` is not declared in the context of the equation.")
            var
        | Some symb ->
        let state', w, e = desugar_expression state t in
        (state', w, Template.Apply (symb, e)) )
    | Sugared.TEffect (eff, t, var, tmpl) ->
        let state', w, e = desugar_expression state t in
        let state'', eff' = effect_to_symbol state' eff in
        let x = fresh_var (Some var) in
        let new_ctx = Assoc.update var x state.context in
        let state''', tmpl' = 
          desugar_template {state'' with context= new_ctx} tmpl 
        in
        ({state''' with context=state.context}, w, Template.Effect (eff', e, x, tmpl'))
  in
  match w with
  | [] -> (state', add_loc tmpl' loc)
  | _ :: _ -> (state', add_loc (Template.Let (w, add_loc tmpl' loc)) loc)

let desugar_equation_ctxs state ctx ~loc =
  let desugar_var st (var, ty) = 
    let symb = 
      match Assoc.lookup var st.context with
      | None -> fresh_var (Some var)
      | Some _ ->
          Error.typing ~loc
            ("Variable `%s` appears multiple times in the context of the "
            ^^ "equation.") var
    in
    let st', ty' = desugar_vtype Assoc.empty st ty in
    let ctx' = Assoc.update var symb st.context in
    ({st' with context=ctx'}, (symb, ty'))
  in
  let (state', ctx') = 
    fold_map desugar_var state ctx 
  in
  (state', Assoc.of_list ctx')


(* ========== Desugaring of top level. ========== *)

let desugar_top_let state defs =
  let aux_desugar (p, c) (fold_state, defs, forbidden) =
    let check_forbidden (x, _) =
      if List.mem x forbidden then
        Error.syntax ~loc:p.at "Several definitions of value `%s`." x
    in
    let state', p_vars, p' = desugar_pattern state p in
    Assoc.iter check_forbidden p_vars ;
    let state'', c' = desugar_computation state' c in
    ( {state'' with context= Assoc.concat p_vars fold_state.context}
    , (p', c') :: defs
    , Assoc.keys_of p_vars @ forbidden )
  in
  let state', defs', _ =
    List.fold_right aux_desugar defs (state, [], [])
  in
  (state', defs')

let desugar_top_let_rec state defs =
  let aux_desugar (x, ty, abs) (fold_state, ns, forbidden) =
    if List.mem x forbidden then
      Error.syntax ~loc:abs.at
        "Several definitions of recursive function `%s`." x ;
    let n = fresh_var (Some x) in
    ( {state with context= Assoc.update x n fold_state.context}
    , n :: ns
    , x :: forbidden )
  in
  let state', ns, _ = List.fold_right aux_desugar defs (state, [], []) in
  let desugar_defs (n, (_, ty, c)) (st, defs) =
    let st', c = desugar_let_rec st c in
    let st'', ty = desugar_vtype Assoc.empty st' ty in
    (st'', (n, ty, c) :: defs)
  in
  let state'', defs' = 
    List.fold_right desugar_defs (List.combine ns defs) (state', [])
  in
  ({state'' with context=state'.context}, defs')

let desugar_external state (x, t, f) =
  let n = fresh_var (Some x) in
  let ts = syntax_to_core_params (free_type_params t) in
  let state', t' = desugar_vtype ts state t in
  ({state with context= Assoc.update x n state.context}, (n, t', f))

let desugar_def_effect state (eff, (ty1, ty2)) =
  let state', eff' = effect_to_symbol state eff in
  let state'', ty1' = desugar_vtype Assoc.empty state' ty1 in
  let state''', ty2' = desugar_vtype Assoc.empty state'' ty2 in
  (state''', (eff', (ty1', ty2')))

let desugar_def_theory state (theory, th_defs, effs) =
  let state', th_symb = theory_to_symbol state theory in
  let defs_desugarer st = function
    | Sugared.Equation {it=eqn; at=loc} ->
        (* Each equation defines its own context *)
        let st0 = {st with context=Assoc.empty} in
        let st1, ctx' = desugar_equation_ctxs ~loc st0 eqn.Sugared.ctx in
        let st2, tctx' = desugar_equation_ctxs ~loc st1 eqn.Sugared.tctx in
        let st3, tmpl1' = desugar_template st2 eqn.Sugared.left_tmpl in
        let st4, tmpl2' = 
          desugar_template {st3 with context=st2.context} eqn.Sugared.right_tmpl 
        in
        let eqn' =
          { Template.ctx = ctx'; Template.tctx = tctx'
          ; Template.left_tmpl = tmpl1'; Template.right_tmpl = tmpl2' }
        in
        (st4, Template.Equation (add_loc eqn' loc))
    | Sugared.Theory theory ->
        let st', theory' = theory_to_symbol st theory in
        (st', Template.Theory theory')
  in
  let state'', effs' = fold_map effect_to_symbol state' effs in
  let state''', eqs' = fold_map defs_desugarer state'' th_defs in
  (* Dont forget to restore the context of the program. *)
  ({state''' with context=state.context}, (th_symb, eqs', effs'))
