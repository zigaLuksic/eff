(** Type contexts

    Type contexts assign type schemes to variables, and are used for type
    inference. A type scheme consists of a type and a list of universally
    quantified type parameters.
*)

(** The types of contexts and type schemes. *)
type ty_scheme = CoreTypes.TyParam.t list * Type.vty

type t

val empty : t
(** [empty] is the empty context. *)

val lookup : loc:Location.t -> t -> CoreSyntax.variable -> Type.vty
(** [lookup ~pos ctx x] returns a fresh instance of the type scheme assigned
    to the variable [x] in the context [ctx]. The optional position is used in
    error reporting when the variable is not bound in the context. *)

val extend : t -> CoreSyntax.variable -> ty_scheme -> t
(** [extend x ty_scheme ctx] returns the context [ctx] extended with
    a variable [x] bound to the type scheme [ty_scheme]. *)

val extend_ty : t -> CoreSyntax.variable -> Type.vty -> t
(** [extend_ty x ty ctx] returns the context [ctx] extended with a variable [x]
    bound to the type [ty]. The type is promoted to a type scheme with no
    generalized type parameters. *)

val subst_ctx : t -> Type.substitution -> t
(** [subst_ctx sbst ctx] returns a substitution of [ctx] under [sbst]. *)

val generalize : t -> bool -> Type.vty -> ty_scheme
(** [generalize ctx poly ty] generalizes the type [ty] in context [ctx] to a
    type scheme. If [poly] is [true], all free type parameters in [ty] that do
    not appear in [ctx] are universally quantified. *)

val infer_effect : t -> CoreSyntax.effect -> (Type.vty * Type.vty) option

val add_effect : t -> CoreSyntax.effect -> Type.vty * Type.vty -> t

val infer_theory : t -> CoreTypes.Theory.t -> (Template.equation list * Type.eff_sig) option

val add_theory : t -> CoreTypes.Theory.t -> (Template.equation list * Type.eff_sig) -> t

val switch_variables : t -> (CoreTypes.Variable.t, ty_scheme) Assoc.t -> t