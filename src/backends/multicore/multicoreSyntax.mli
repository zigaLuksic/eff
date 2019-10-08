module CoreSyntax = UntypedSyntax

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

(** Types used by MulticoreOcaml. *)
type ty =
  | TyApply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | TyBasic of Const.ty
  | TyTuple of ty list
  | TyArrow of ty * ty

type tydef =
  | TyDefSum of (CoreTypes.Label.t, ty option) Assoc.t
  | TyDefInline of ty

(** Patterns *)
type pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure expressions *)
type term =
  | Var of variable
  | Const of Const.t
  | Annotated of term * ty
  | Tuple of term list
  | Variant of label * term option
  | Lambda of abstraction
  | Function of match_case list
  | Effect of effect
  | Let of (pattern * term) list * term
  | LetRec of (variable * abstraction) list * term
  | Match of term * match_case list
  | Apply of term * term
  | Check of term

and match_case =
  | ValueClause of abstraction
  | EffectClause of effect * abstraction2

(** Abstractions that take one argument. *)
and abstraction = pattern * term

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * term

val of_computation : CoreSyntax.computation -> term

val of_pattern : CoreSyntax.pattern -> pattern

val of_type : Type.ty -> ty

val of_tydef : Tctx.tydef -> tydef
