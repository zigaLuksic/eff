module CoreSyntax = AnnotatedSyntax
module TypeSystem = Bidirectional

module type T = sig
  type state

  val initial_state : state

  val process_computation :
       state
    -> CoreSyntax.computation
    -> CoreTypes.TyParam.t list * Type.cty
    -> state

  val process_type_of :
       state
    -> CoreSyntax.computation
    -> CoreTypes.TyParam.t list * Type.cty
    -> state

  val process_def_effect :
    state -> CoreTypes.Effect.t * (Type.vty * Type.vty) -> state

  val process_def_theory :
       state 
    -> CoreTypes.Theory.t * Template.theory_def list * Type.eff_sig
    -> state

  val process_top_let :
       state
    -> (CoreSyntax.pattern * CoreSyntax.computation) list
    -> (TypeSystem.Syntax.variable * TypeSystem.Ctx.ty_scheme) list
    -> state

  val process_top_let_rec :
       state
    -> (CoreSyntax.variable, Type.vty * CoreSyntax.abstraction) Assoc.t
    -> (TypeSystem.Syntax.variable * TypeSystem.Ctx.ty_scheme) list
    -> state

  val process_external :
    state -> CoreTypes.Variable.t * Type.vty * string -> state

  val process_tydef :
       state
    -> (CoreTypes.TyName.t, Tctx.polar_params * Tctx.tydef) Assoc.t
    -> state

  val finalize : state -> unit
end
