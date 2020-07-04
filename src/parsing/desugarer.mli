type state

val initial_state : state

val desugar_computation :
  state -> SugaredSyntax.term -> state * AnnotatedSyntax.computation

val desugar_def_effect :
     state
  -> SugaredSyntax.effect * (SugaredSyntax.ty * SugaredSyntax.ty)
  -> state * (CoreTypes.Effect.t * (Type.vty * Type.vty))

val desugar_external :
     state
  -> SugaredSyntax.variable * SugaredSyntax.ty * string
  -> state * (CoreTypes.Variable.t * Type.vty * string)

val desugar_top_let :
     state
  -> (SugaredSyntax.pattern * SugaredSyntax.term) list
  -> state * (AnnotatedSyntax.pattern * AnnotatedSyntax.computation) list

val desugar_top_let_rec :
     state
  -> (SugaredSyntax.variable * SugaredSyntax.ty * SugaredSyntax.term) list
  -> state * (CoreTypes.Variable.t * Type.vty * AnnotatedSyntax.abstraction) list

val desugar_tydefs :
     state
  -> (string, SugaredSyntax.typaram list * SugaredSyntax.tydef) Assoc.t
  -> state
     * (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Tctx.tydef) Assoc.t

val desugar_def_theory :
     state
  -> (SugaredSyntax.theory * SugaredSyntax.theory_def list * SugaredSyntax.eff_ty list)
  -> state
     * (CoreTypes.Theory.t * Template.theory_def list * Type.eff list)
