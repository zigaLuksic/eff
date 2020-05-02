open CoreUtils

module Ann = AnnotatedSyntax 

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type varty =
  | ValueTy of Type.vty
  | TemplateTy of Type.vty

type ctx = (CoreTypes.Variable.t, varty) Assoc.t located

(** Templates *)
type t = plain_t located

and plain_t =
  | Let of (Ann.pattern * Ann.computation) list * t
  | LetRec of (variable * Type.vty * (Ann.pattern * Ann.computation)) list * t
  | Match of Ann.value * (Ann.pattern * t) list
  | Apply of variable * Ann.value
  | Effect of effect * Ann.value * variable * t

(** Equations *)
type equation = ctx * t * t