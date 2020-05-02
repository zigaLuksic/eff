(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)

let fresh_ty_param = CoreTypes.TyParam.fresh

type vty =
  | Apply of CoreTypes.TyName.t * vty list
  | TyParam of CoreTypes.TyParam.t
  | Basic of Const.ty
  | Tuple of vty list
  | Arrow of vty * cty
  | Handler of cty * cty

and cty =
  | CTySig of vty * eff_sig
  | CTyTheory of vty * CoreTypes.Theory.t

and eff_sig = CoreTypes.Effect.t list


let int_ty = Basic Const.IntegerTy

let string_ty = Basic Const.StringTy

let bool_ty = Basic Const.BooleanTy

let float_ty = Basic Const.FloatTy

let unit_ty = Tuple []

let empty_ty = Apply (CoreTypes.empty_tyname, [])


type substitution = (CoreTypes.TyParam.t, vty) Assoc.t

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
(* WARNING: This relies heavliy on parameters not being in effects *)
let rec subst_ty sbst ty =
  let rec vsubst = function
    | Apply (ty_name, tys) -> Apply (ty_name, List.map vsubst tys)
    | TyParam p as ty -> (
      match Assoc.lookup p sbst with Some ty -> ty | None -> ty )
    | Basic _ as ty -> ty
    | Tuple tys -> Tuple (List.map vsubst tys)
    | Arrow (ty, cty) -> 
        Arrow (vsubst ty, csubst cty)
    | Handler (cty1, cty2) ->
        Handler (csubst cty1, csubst cty2)
  and csubst = function
    | CTySig (vty, eff_sig) -> CTySig (vsubst vty, eff_sig)
    | CTyTheory (vty, eff_theory) -> CTyTheory (vsubst vty, eff_theory)
  in
  vsubst ty


(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
(* WARNING: This relies heavliy on parameters not being in effects *)
let free_params ty =
  let flatten_map f lst = List.fold_left ( @ ) [] (List.map f lst) in
  let rec free_vty = function
    | Apply (_, tys) -> flatten_map free_vty tys
    | TyParam p -> [p]
    | Basic _ -> []
    | Tuple tys -> flatten_map free_vty tys
    | Arrow (ty, cty) -> free_vty ty @ free_cty cty
    | Handler (cty1, cty2) -> free_cty cty1 @ free_cty cty2
  and free_cty = function
    | CTySig (vty, eff_sig) -> free_vty vty
    | CTyTheory (vty, eff_theory) -> free_vty vty
  in
  CoreUtils.unique_elements (free_vty ty)


(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())

let refreshing_subst ps =
  let ps' = Assoc.map_of_list (fun p -> (p, fresh_ty_param ())) ps in
  let sbst = Assoc.map (fun p' -> TyParam p') ps' in
  (Assoc.values_of ps', sbst)

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh params ty =
  let params', sbst = refreshing_subst params in
  (params', subst_ty sbst ty)


let rec print_vty (ps, vty) ppf =
  let rec print_vty ?max_level vty ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match vty with
    | Arrow (t1, t2) ->
        print ~at_level:5 "@[<h>%t ->@ %t@]" 
        (print_vty ~max_level:4 t1) (print_cty (ps, t2))
    | Basic b -> print "%t" (Const.print_ty b)
    | Apply (t, []) -> print "%t" (CoreTypes.TyName.print t)
    | Apply (t, [s]) ->
        print ~at_level:1 "%t %t" (print_vty ~max_level:1 s)
          (CoreTypes.TyName.print t)
    | Apply (t, ts) ->
        print ~at_level:1 "(%t) %t"
          (Print.sequence ", " print_vty ts)
          (CoreTypes.TyName.print t)
    | TyParam p -> print "%t" (CoreTypes.TyParam.print_old ~poly:ps p)
    | Tuple [] -> print "unit"
    | Tuple ts ->
        print ~at_level:2 "@[<hov>%t@]"
          (Print.sequence " * " (print_vty ~max_level:1) ts)
    | Handler (ty1, ty2) ->
        print ~at_level:4 "%t =>@ %t" 
        (print_cty (ps, ty1)) (print_cty (ps, ty2))
  in
  print_vty vty ppf

and print_cty (ps, cty) ppf =
  match cty with
  | CTySig (vty, effs) ->
      begin match effs with
      | [] -> (* Remove printing sig from pure computations *)
          Print.print ppf "@[<hov>%t@]"
            (print_vty (ps, vty))
      | _ ->
          Print.print ppf "@[<hov>(%t!%t)@]"
            (print_vty (ps, vty)) (print_sig (effs))
      end
  | CTyTheory (vty, theory) ->
      Print.print ppf "@[<hov>(%t!{%t})@]"
        (print_vty (ps, vty)) (CoreTypes.Theory.print theory)

and print_sig (effs) ppf =
  let print_effty eff ppf = CoreTypes.Effect.print eff ppf in
  Print.print ppf "@[<hov>{%t}@]"
    (Print.sequence ", " (print_effty) (effs))

