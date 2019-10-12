(** Syntax of the core language. *)

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure values *)
type value =
  | Var of variable
  | Const of Const.t
  | Tuple of value list
  | Variant of label * value option
  | Lambda of abstraction
  | Handler of handler

(** Impure computations *)
and computation =
  | Value of value
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of value * abstraction list
  | Apply of value * value
  | Handle of value * computation
  | Effect of effect * value
  | Check of computation

(** Handler definitions *)
and handler =
  { effect_clauses: (effect, abstraction2) Assoc.t
  ; value_clause: abstraction }

(** Abstractions that take one argument. *)
and abstraction = pattern * computation

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * computation

val value_remove_annotations : AnnotatedSyntax.value -> value

val computation_remove_annotations : AnnotatedSyntax.computation -> computation

val pattern_remove_annotations : AnnotatedSyntax.pattern -> pattern

val print_pattern : ?max_level:int -> pattern -> Format.formatter -> unit

val print_computation :
  ?max_level:int -> computation -> Format.formatter -> unit

val print_value : ?max_level:int -> value -> Format.formatter -> unit
