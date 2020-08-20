(** Type inference contexts *)
module Ty = Type

type tydef =
  | Sum of (CoreTypes.Label.t, Type.vty option) Assoc.t
  | Inline of Type.vty

type typar_polarity = Co | Contra | Fixed

type polar_params = (CoreTypes.TyParam.t, typar_polarity) Assoc.t

type tyctx = (CoreTypes.TyName.t, polar_params * tydef) Assoc.t

let initial : tyctx =
  Assoc.of_list
    [ (CoreTypes.bool_tyname, (Assoc.empty, Inline Ty.bool_ty))
    ; (CoreTypes.unit_tyname, (Assoc.empty, Inline Ty.unit_ty))
    ; (CoreTypes.int_tyname, (Assoc.empty, Inline Ty.int_ty))
    ; (CoreTypes.string_tyname, (Assoc.empty, Inline Ty.string_ty))
    ; (CoreTypes.float_tyname, (Assoc.empty, Inline Ty.float_ty))
    ; ( CoreTypes.list_tyname
      , let a = Type.fresh_ty_param () in
        let list_nil = (CoreTypes.nil, None) in
        let list_cons =
          ( CoreTypes.cons
          , Some
              (Ty.Tuple
                 [Ty.TyParam a; Ty.Apply (CoreTypes.list_tyname, [Ty.TyParam a])])
          )
        in
        (Assoc.of_list [(a, Co)], Sum (Assoc.of_list [list_nil; list_cons])) )
    ; (CoreTypes.empty_tyname, (Assoc.empty, Sum Assoc.empty)) ]

let global = ref initial

let subst_tydef sbst =
  let subst = Type.subst_ty sbst in
  function
  | Sum tys ->
      Sum (Assoc.map (function None -> None | Some x -> Some (subst x)) tys)
  | Inline ty -> Inline (subst ty)

let lookup_tydef ~loc ty_name =
  match Assoc.lookup ty_name !global with
  | None ->
      Error.typing ~loc "Unknown type %t" (CoreTypes.TyName.print ty_name)
  | Some (params, tydef) -> (params, tydef)

(** [find_variant lbl] returns the information about the variant type that defines the
    label [lbl]. *)
let find_variant lbl =
  let construct = function
    | ty_name, (ps, Sum vs) -> (
      match Assoc.lookup lbl vs with
      | Some us -> Some (ty_name, ps, vs, us)
      | None -> None )
    | _ -> None
  in
  match Assoc.find_if (fun x -> construct x <> None) !global with
  | Some x -> construct x
  | None -> None

let apply_to_params t ps = Type.Apply (t, List.map (fun p -> Type.TyParam p) ps)

let transparent ~loc ty_name =
  let _, ty = lookup_tydef ~loc ty_name in
  match ty with Sum _ -> false | Inline _ -> true

(* [ty_apply pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~loc ty_name lst =
  let params, ty = lookup_tydef ~loc ty_name in
  if Assoc.length params <> List.length lst then
    Error.typing ~loc "Type constructors `%t` should be applied to %d arguments."
      (CoreTypes.TyName.print ty_name)
      (Assoc.length params)
  else
    let pars = Assoc.keys_of params in
    let combined = Assoc.of_list (List.combine pars lst) in
    subst_tydef combined ty

(** [check_well_formed ~loc ty] checks that type [ty] is well-formed. *)
let check_well_formed ~loc tydef =
  let rec vcheck = function
    | Ty.Basic _ | Ty.TyParam _ -> ()
    | Ty.Apply (ty_name, tys) ->
        let params, _ = lookup_tydef ~loc ty_name in
        let n = Assoc.length params in
        if List.length tys <> n then
          Error.typing ~loc "The type constructor `%t` expects %d arguments."
            (CoreTypes.TyName.print ty_name)
            n
    | Ty.Arrow (ty1, cty2) -> vcheck ty1 ; ccheck cty2
    | Ty.Tuple tys -> List.iter vcheck tys
    | Ty.Handler (cty1, cty2) -> ccheck cty1 ; ccheck cty2
  and ccheck = function
    (* Signatures and equations are checked to be well formed when defined *)
    | CTySig (vty, _) | CTyTheory (vty, _) -> vcheck vty 
  in
  match tydef with
  | Sum constructors ->
      if not (CoreUtils.no_duplicates (Assoc.keys_of constructors)) then
        Error.typing ~loc "Constructors of a sum type must be distinct." ;
      let checker = function _, None -> () | _, Some ty -> vcheck ty in
      Assoc.iter checker constructors
  | Inline ty -> vcheck ty

(** [check_well_formed ~loc ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~loc =
  let rec vcheck forbidden = function
    | Ty.Basic _ | Ty.TyParam _ -> ()
    | Ty.Apply (t, lst) ->
        if List.mem t forbidden then
          Error.typing ~loc "Type definition %t is cyclic."
            (CoreTypes.TyName.print t)
        else check_tydef (t :: forbidden) (ty_apply ~loc t lst)
    | Ty.Arrow (ty1, ty2) -> vcheck forbidden ty1 ; ccheck forbidden ty2
    | Ty.Tuple tys -> List.iter (vcheck forbidden) tys
    | Ty.Handler (ty1, ty2) -> ccheck forbidden ty1 ; ccheck forbidden ty2
  and ccheck forbidden = function
    (* Signatures and equations are checked to be well formed when defined *)
    | CTySig (vty, _) | CTyTheory (vty, _) -> vcheck forbidden vty 
  and check_tydef forbidden = function
    | Sum _ -> ()
    | Inline ty -> vcheck forbidden ty
  in
  check_tydef []

(** [check_shadowing ~loc ty] checks that the definition of type [ty] does
    not shadow any field labels, constructors, or operations.

    NB: In eff we _cannot_ allow shadowing because the interpreter uses the original
    field names and label, hence shadowing breaks type safety!
*)
let check_shadowing ~loc = function
  | Sum lst ->
      let shadow_check_sum (lbl, _) =
        match find_variant lbl with
        | Some (u, _, _, _) ->
            Error.typing ~loc "Constructor `%t` is already used in type `%t`"
              (CoreTypes.Label.print lbl)
              (CoreTypes.TyName.print u)
        | None -> ()
      in
      Assoc.iter shadow_check_sum lst
  | Inline _ -> ()

(* Functions for calculating the subtyping polarity of type parameters *)
let flip_pol = function
  | Co -> Contra
  | Contra -> Co
  | Fixed -> Fixed


let rec check_pol_vty par pol = function
  | Type.Apply (name, args) ->
      let params, tydef = lookup_tydef ~loc:Location.unknown name in
      let pols = Assoc.values_of params in
      let checker p ty =
        match p with
        | Co -> check_pol_vty par pol ty
        | Fixed -> pol = Fixed || not (List.mem par (Type.free_params ty))
        | Contra -> check_pol_vty par (flip_pol pol) ty
      in
      List.for_all2 checker pols args
  | Type.TyParam par' -> if par = par' then pol = Co || pol = Fixed else true
  | Type.Basic _ -> true
  | Type.Tuple tys -> List.for_all (check_pol_vty par pol) tys
  | Type.Arrow (ty1, ty2) -> 
      check_pol_vty par (flip_pol pol) ty1 && check_pol_cty par pol ty2
  | Type.Handler (ty1, ty2) -> 
      check_pol_cty par (flip_pol pol) ty1 && check_pol_cty par pol ty2

and check_pol_cty par pol = function
  | Type.CTySig (vty, effs) ->
      check_pol_vty par pol vty && List.for_all (check_pol_eff par pol) effs
  | Type.CTyTheory (vty, theory) -> check_pol_vty par pol vty

and check_pol_eff par pol = function
  | Type.LocEff (eff, ty1, ty2) -> 
      check_pol_vty par pol ty1 && check_pol_vty par (flip_pol pol) ty2
  | Type.GlobEff eff -> true

let print_pol pol ppf =
  match pol with
  | Co -> Print.print ppf "covariant"
  | Contra -> Print.print ppf "contravariant"
  | Fixed -> Print.print ppf "fixed"

let check_pol_tydef ~loc name all_pars par pol = function
  | Sum tydefs ->
      let checker (lbl, vty_opt) =
        match vty_opt with
        | None -> ()
        | Some ty -> 
            if check_pol_vty par pol ty then ()
            else
              Error.typing ~loc 
                ( "In the definition of `%t %t` the parameter `%t` was specified "
                ^^ "to be `%t`, but the check failed for constructor `%t`." )
                (Print.tuple CoreTypes.TyParam.print_old all_pars)
                (CoreTypes.TyName.print name) (CoreTypes.TyParam.print_old par)
                (print_pol pol) (CoreTypes.Label.print lbl)
      in
      Assoc.iter checker tydefs
  | Inline ty ->
      if check_pol_vty par pol ty then ()
      else
        Error.typing ~loc 
          ( "In the definition of `%t %t` the parameter `%t` was specified "
          ^^ "to be `%t`, but the check failed." )
          (Print.tuple CoreTypes.TyParam.print_old all_pars)
          (CoreTypes.TyName.print name) (CoreTypes.TyParam.print_old par)
          (print_pol pol)


(** [extend_tydefs ~loc tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended context. *)
let extend_tydefs ~loc tydefs =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let global_orig = !global in
  let extend_tydef (name, (pol_params, ty)) =
    check_shadowing ~loc ty ;
    match Assoc.lookup name !global with
    | Some _ ->
        Error.typing ~loc "Type `%t` already defined."
          (CoreTypes.TyName.print name)
    | None -> 
      let checker (par, pol) = 
        check_pol_tydef ~loc name (Assoc.keys_of pol_params) par pol ty
      in
      global := Assoc.update name (pol_params, ty) !global;
      (* We need to add first and check later, so it works with recursion. *)
      Assoc.iter checker pol_params
  in
  try
    Assoc.iter extend_tydef tydefs ;
    Assoc.iter (fun (_, (_, ty)) -> check_well_formed ~loc ty) tydefs ;
    Assoc.iter (fun (_, (_, ty)) -> check_noncyclic ~loc ty) tydefs
  with e ->
    global := global_orig ;
    raise e

(* reinstate the context on error *)
