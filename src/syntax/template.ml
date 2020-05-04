open CoreUtils

module Ann = AnnotatedSyntax 

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type ctx = (CoreTypes.Variable.t, Type.vty) Assoc.t

(** Templates *)
type t = plain_t located

and plain_t =
  | Let of (Ann.pattern * Ann.computation) list * t
  | Match of Ann.value * (Ann.pattern * t) list
  | Apply of variable * Ann.value
  | Effect of effect * Ann.value * variable * t

(** Equations *)

type equation = plain_equation located

and plain_equation = {ctx: ctx; tctx: ctx; left_tmpl: t; right_tmpl: t}