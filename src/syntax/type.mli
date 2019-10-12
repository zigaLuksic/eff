val fresh_ty_param : unit -> CoreTypes.TyParam.t

type vty =
  | Apply of CoreTypes.TyName.t * vty list
  | TyParam of CoreTypes.TyParam.t
  | Basic of Const.ty
  | Tuple of vty list
  | Arrow of vty * cty
  | Handler of cty * cty

and cty =
  | Cty of vty * eff_sig 

and eff_sig = CoreTypes.Effect.t list (* (CoreTypes.Effect.t, vty * vty) Assoc.t *)

val int_ty : vty

val string_ty : vty

val bool_ty : vty

val float_ty : vty

val unit_ty : vty

val empty_ty : vty


type substitution = (CoreTypes.TyParam.t, vty) Assoc.t

val subst_ty : substitution -> vty -> vty
(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)

val identity_subst : substitution
(** [identity_subst] is a substitution that makes no changes. *)

val compose_subst : substitution -> substitution -> substitution
(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)

(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)

val free_params : vty -> CoreTypes.TyParam.t list

val occurs_in_ty : CoreTypes.TyParam.t -> vty -> bool
(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)

val fresh_ty : unit -> vty
(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)

val refreshing_subst :
  CoreTypes.TyParam.t list -> CoreTypes.TyParam.t list * substitution

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)

val refresh : CoreTypes.TyParam.t list -> vty -> CoreTypes.TyParam.t list * vty

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
(*
val beautify : CoreTypes.TyParam.t list * vty -> CoreTypes.TyParam.t list * vty

val beautify2 :
  ty -> ty -> (CoreTypes.TyParam.t list * ty) * (CoreTypes.TyParam.t list * ty) 
*)

val print_vty : CoreTypes.TyParam.t list * vty -> Format.formatter -> unit

val print_cty : CoreTypes.TyParam.t list * cty -> Format.formatter -> unit

(* val print_beautiful : CoreTypes.TyParam.t list * ty -> Format.formatter -> unit *)
