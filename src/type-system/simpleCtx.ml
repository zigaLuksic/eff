module EffectMap = Map.Make (CoreTypes.Effect)
module TheoryMap = Map.Make (CoreTypes.Effect)

type ty_scheme = CoreTypes.TyParam.t list * Type.vty

type t =
  { variables: (CoreTypes.Variable.t, ty_scheme) Assoc.t
  ; effects: (Type.vty * Type.vty) EffectMap.t
  ; theories: (Template.equation list * Type.eff_sig) TheoryMap.t }

let empty = {variables= Assoc.empty; effects= EffectMap.empty; theories= TheoryMap.empty}

let lookup ~loc ctx x =
  match Assoc.lookup x ctx.variables with
  | Some (ps, t) -> snd (Type.refresh ps t)
  | None -> Error.typing ~loc "Unknown variable name `%t`." (CoreTypes.Variable.print x)

let extend ctx x ty_scheme =
  {ctx with variables= Assoc.update x ty_scheme ctx.variables}

let extend_ty ctx x ty = extend ctx x ([], ty)

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty) =
    assert (List.for_all (fun p -> not (List.mem p ps)) (Assoc.keys_of sbst)) ;
    (ps, Type.subst_ty sbst ty)
  in
  {ctx with variables= Assoc.map subst_ty_scheme ctx.variables}

(** [free_params ctx] returns list of all free type parameters in [ctx]. *)
let free_params ctx =
  let binding_params (_, (ps, ty)) =
    CoreUtils.list_diff (Type.free_params ty) ps
  in
  let xs = List.map binding_params (Assoc.to_list ctx) |> List.flatten in
  CoreUtils.unique_elements xs

let generalize ctx poly ty =
  if poly then
    let ps =
      CoreUtils.list_diff (Type.free_params ty) (free_params ctx.variables)
    in
    (ps, ty)
  else ([], ty)

let infer_effect env eff =
  try Some (EffectMap.find eff env.effects) with Not_found -> None

let add_effect env eff (ty1, ty2) =
  match infer_effect env eff with
  | None -> {env with effects= EffectMap.add eff (ty1, ty2) env.effects}
  | Some _ ->
      Error.typing ~loc:Location.unknown "Effect `%t` is already defined."
        (CoreTypes.Effect.print eff)

let infer_theory env theory =
  try Some (EffectMap.find theory env.theories) with Not_found -> None

let add_theory env theory theory_deff =
  match infer_theory env theory with
  | None -> {env with theories= TheoryMap.add theory theory_deff env.theories}
  | Some _ ->
      Error.typing ~loc:Location.unknown "Theory `%t` is already defined."
        (CoreTypes.Theory.print theory)