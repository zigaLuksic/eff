type state

val initial_state : state

val extend : CoreSyntax.pattern -> Value.value -> state -> state

val extend_let_rec :
  state -> (CoreSyntax.variable, CoreSyntax.abstraction) Assoc.t -> state

val run : state -> CoreSyntax.computation -> Value.value

val update : CoreSyntax.variable -> Value.value -> state -> state

val lookup : CoreSyntax.variable -> state -> Value.value option
