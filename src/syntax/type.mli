val fresh_ty_param : unit -> CoreTypes.TyParam.t

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

val int_ty : vty

val string_ty : vty

val bool_ty : vty

val float_ty : vty

val unit_ty : vty

val empty_ty : vty


type substitution = (CoreTypes.TyParam.t, vty) Assoc.t

val subst_ty : substitution -> vty -> vty
(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)

val free_params : vty -> CoreTypes.TyParam.t list
(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)

val fresh_ty : unit -> vty
(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)

val refreshing_subst :
  CoreTypes.TyParam.t list -> CoreTypes.TyParam.t list * substitution

val refresh : CoreTypes.TyParam.t list -> vty -> CoreTypes.TyParam.t list * vty
(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)

val print_vty : CoreTypes.TyParam.t list * vty -> Format.formatter -> unit

val print_cty : CoreTypes.TyParam.t list * cty -> Format.formatter -> unit

val print_sig : eff_sig -> Format.formatter -> unit
