open CoreUtils

module Ann = AnnotatedSyntax 

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type var =
  | ValueVar of Type.vty
  | TemplateVar of Type.vty

type ctx = (CoreTypes.TyName.t, var) Assoc.t

(** Templates *)
type t = plain_t located

and plain_t =
  | TPlaceholder
  | TLet of (Ann.pattern * Ann.computation) list * t
  | TMatch of Ann.value * tabstraction list
  | TApply of variable * Ann.value
  | TEffect of effect * Ann.value

(** Abstractions that take one argument. *)
and tabstraction = Ann.pattern * t

(** Equations *)
type equation = ctx * t * t