(** Pattern matching exhaustiveness checking as described by Maranget [1]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred.

   [1] http://pauillac.inria.fr/~maranget/papers/warn/index.html
*)

val is_irrefutable : AnnotatedSyntax.pattern -> unit
(** Check that a pattern is irrefutable. *)

val check_comp : AnnotatedSyntax.computation -> unit
(** Check for refutable patterns in let statements and non-exhaustive match statements. *)
