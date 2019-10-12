(** Syntax of the core language. *)
open CoreUtils

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type pattern = plain_pattern located

and plain_pattern =
  | PVar of variable
  | PAnnotated of pattern * Type.vty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure values *)
type value = plain_value located

and plain_value =
  | Var of variable
  | Const of Const.t
  | VAnnotated of value * Type.vty
  | Tuple of value list
  | Variant of label * value option
  | Lambda of abstraction
  | Handler of handler

(** Impure computations *)
and computation = plain_computation located

and plain_computation =
  | Value of value
  | CAnnotated of computation * Type.cty
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * Type.vty * abstraction) list * computation
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

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.it with
  | PVar x -> print "%t" (CoreTypes.Variable.print x)
  | PAs (p, x) ->
      print "%t as %t" (print_pattern p) (CoreTypes.Variable.print x)
  | PAnnotated (p, ty) -> print_pattern ?max_level p ppf
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PVariant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | PVariant (lbl, None) -> print "%t" (CoreTypes.Label.print lbl)
  | PVariant (lbl, Some {it= PTuple [v1; v2]}) when lbl = CoreTypes.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_pattern v1) (pattern_list v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%t @[<hov>%t@]"
        (CoreTypes.Label.print lbl)
        (print_pattern p)
  | PNonbinding -> print "_"

and pattern_list ?(max_length = 299) p ppf =
  if max_length > 1 then
    match p.it with
    | PVariant (lbl, Some {it= PTuple [v1; v2]}) when lbl = CoreTypes.cons ->
        Format.fprintf ppf ",@ %t%t" (print_pattern v1)
          (pattern_list ~max_length:(max_length - 1) v2)
    | PVariant (lbl, None) when lbl = CoreTypes.nil -> ()
    | _ -> Format.fprintf ppf "(??? %t ???)" (print_pattern p)
  else Format.fprintf ppf ",@ ..."

let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.it with
  | Apply (e1, e2) ->
      print ~at_level:1 "%t %t" (print_value e1)
        (print_value ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value %t" (print_value ~max_level:0 e)
  | CAnnotated (c, ty) -> 
      print ~at_level:1 "(%t : %t)"
        (print_computation ~max_level:0 c) (Type.print_cty ([], ty))
  | Match (e, lst) ->
      print "match %t with (@[<hov>%t@])" (print_value e)
        (Print.sequence " | " case lst)
  | Handle (e, c) ->
      print "handle %t with %t" (print_value e) (print_computation c)
  | Let (lst, c) ->
      print "let @[<hov>%t@] in %t"
        (Print.sequence " | " let_abstraction lst)
        (print_computation c)
  | LetRec (lst, c) -> print "let rec ... in %t" (print_computation c)
  | Check c -> print "check %t" (print_computation c)  
  | Effect (eff, arg) -> 
      print ~at_level:1 "%t @[<hov>%t@]"
        (CoreTypes.Effect.print eff)
        (print_value arg)

and print_value ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.it with
  | Var x -> print "%t" (CoreTypes.Variable.print x)
  | Const c -> print "%t" (Const.print c)
  | VAnnotated (v, ty) ->
      print ~at_level:1 "(%t : %t)"
        (print_value ~max_level:0 v) (Type.print_vty ([], ty))
  | Tuple lst -> Print.tuple print_value lst ppf
  | Variant (lbl, None) -> print "%t" (CoreTypes.Label.print lbl)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%t @[<hov>%t@]"
        (CoreTypes.Label.print lbl)
        (print_value e)
  | Lambda a -> print "fun %t" (abstraction a)
  | Handler h ->
      print "{effect_clauses = %t; value_clause = (%t)}"
        (Print.sequence " | " effect_clause (Assoc.to_list h.effect_clauses))
        (abstraction h.value_clause)

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf = Format.fprintf ppf "%t" (abstraction a)

and effect_clause (eff, a2) ppf =
  Format.fprintf ppf "| %t -> %t"
    (CoreTypes.Effect.print eff)
    (abstraction2 a2)

and abstraction2 (p1, p2, c) ppf =
  Format.fprintf ppf "%t %t -> %t" (print_pattern p1) (print_pattern p2)
    (print_computation c)
