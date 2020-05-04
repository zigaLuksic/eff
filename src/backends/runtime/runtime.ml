(* Evaluation of the intermediate language, big step. *)
open CoreUtils
module V = Value

exception PatternMatch of Location.t

module Backend : BackendSignature.T = struct
  module RuntimeEnv = Map.Make (CoreTypes.Variable)

  (* prints tells us wheter or not to print, while mute depth makes sure that
  printing is muted in the case of nested #use *)
  type state = Eval.state

  let initial_state = Eval.initial_state

  (* Processing functions *)
  let process_computation state c (params, cty) =
    let vty = match cty with
      | Type.CTySig (vty, _) -> vty
      | Type.CTyTheory (vty, _) -> vty
    in
    let erased_c = CoreSyntax.computation_remove_annotations c in
    let v = Eval.run state erased_c in
    Format.fprintf !Config.output_formatter "@[- : %t = %t@]@."
      (Type.print_vty (params, vty)) (Value.print_value v) ;
    state

  let process_type_of state c ty =
    Format.fprintf !Config.output_formatter "@[- : %t@]@."
      (Type.print_cty ty) ;
    state

  let process_def_effect state (eff, (ty1, ty2)) = state

  let process_def_theory state (theory, eqs, effs) = state

  let process_top_let state defs vars =
    let state' =
      List.fold_right
        (fun (p, c) st ->
          let erased_p = CoreSyntax.pattern_remove_annotations p in
          let erased_c = CoreSyntax.computation_remove_annotations c in
          let v = Eval.run st erased_c in
          Eval.extend erased_p v st )
        defs state
    in
    List.iter
      (fun (x, tysch) ->
        match Eval.lookup x state' with
        | None -> assert false
        | Some v ->
            Format.fprintf !Config.output_formatter "@[val %t : %t = %t@]@."
              (CoreTypes.Variable.print x)
              (Type.print_vty tysch)
              (Value.print_value v) )
      vars ;
    state'

  let process_top_let_rec state defs vars =
    let erase_def (ty, (p, c)) =
      let erased_p = CoreSyntax.pattern_remove_annotations p in
      let erased_c = CoreSyntax.computation_remove_annotations c in
      (erased_p, erased_c)
    in
    let state' = Eval.extend_let_rec state (Assoc.map erase_def defs) in
    List.iter
      (fun (x, tysch) ->
        Format.fprintf !Config.output_formatter "@[val %t : %t = <fun>@]@."
          (CoreTypes.Variable.print x)
          (Type.print_vty tysch) )
      vars ;
    state'

  let process_external state (x, ty, f) =
    match Assoc.lookup f External.values with
    | Some v -> Eval.update x v state
    | None -> Error.runtime "unknown external symbol %s." f

  let process_tydef state tydefs = state

  let finalize state = ()
end
