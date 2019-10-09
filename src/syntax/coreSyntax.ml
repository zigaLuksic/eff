(** Syntax of the core language. *)
open CoreUtils
module Ann = AnnotatedSyntax

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
  | Effect of effect
  | Handler of handler

(** Impure computations *)
and computation =
  | Value of value
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of value * abstraction list
  | Apply of value * value
  | Handle of value * computation
  | Check of computation

(** Handler definitions *)
and handler =
  { effect_clauses: (effect, abstraction2) Assoc.t
  ; value_clause: abstraction }

(** Abstractions that take one argument. *)
and abstraction = pattern * computation

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * computation

let rec value_remove_annotations v =
  match v.it with
  | Ann.Var x -> Var x
  | Ann.Const const -> Const const
  | Ann.VAnnotated (v, ty) -> value_remove_annotations v
  | Ann.Tuple vs -> Tuple (left_to_right_map value_remove_annotations vs)
  | Ann.Variant (lbl, None) -> Variant (lbl, None) 
  | Ann.Variant (lbl, Some v) -> 
      Variant (lbl, Some (value_remove_annotations v)) 
  | Ann.Lambda abs -> Lambda (abstraction_remove_annotations abs)
  | Ann.Effect eff -> Effect eff
  | Ann.Handler {effect_clauses=eff_cs; value_clause=v_cs} ->
      Handler {
        effect_clauses=Assoc.map abstraction2_remove_annotations eff_cs;
        value_clause= abstraction_remove_annotations v_cs}

and computation_remove_annotations c =
  match c.it with
  | Ann.Value v -> Value (value_remove_annotations v)
  | Ann.CAnnotated (c, ty) -> computation_remove_annotations c
  | Ann.Let (defs, c) ->
      Let 
        (left_to_right_map abstraction_remove_annotations defs,
        computation_remove_annotations c)
  | Ann.LetRec (defs, c) ->
      LetRec
        (left_to_right_map 
          (fun (f, abs) -> (f, abstraction_remove_annotations abs)) defs,
        computation_remove_annotations c)
  | Ann.Match (v, defs) ->
      Match (value_remove_annotations v,
        left_to_right_map abstraction_remove_annotations defs)
  | Ann.Apply (v1, v2) ->
      Apply (value_remove_annotations v1, value_remove_annotations v2)
  | Ann.Handle (v, c) ->
      Handle (value_remove_annotations v, computation_remove_annotations c)
  | Ann.Check c -> Check (computation_remove_annotations c)

and pattern_remove_annotations p =
  match p.it with
  | Ann.PVar var -> PVar var
  | Ann.PAnnotated (p, ty) -> pattern_remove_annotations p
  | Ann.PAs (p, var) -> PAs (pattern_remove_annotations p, var)
  | Ann.PTuple ps -> PTuple (left_to_right_map pattern_remove_annotations ps)
  | Ann.PVariant (lbl, None) -> PVariant (lbl, None)
  | Ann.PVariant (lbl, Some p) -> 
      PVariant (lbl, Some (pattern_remove_annotations p))
  | Ann.PConst const -> PConst const
  | Ann.PNonbinding -> PNonbinding

and abstraction_remove_annotations (p, c) =
  (pattern_remove_annotations p, computation_remove_annotations c)

and abstraction2_remove_annotations (p1, p2, c) =
  (pattern_remove_annotations p1,
   pattern_remove_annotations p2,
   computation_remove_annotations c)


let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | PVar x -> print "%t" (CoreTypes.Variable.print x)
  | PAs (p, x) ->
      print "%t as %t" (print_pattern p) (CoreTypes.Variable.print x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PVariant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | PVariant (lbl, None) -> print "%t" (CoreTypes.Label.print lbl)
  | PVariant (lbl, Some PTuple [v1; v2]) when lbl = CoreTypes.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_pattern v1) (pattern_list v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%t @[<hov>%t@]"
        (CoreTypes.Label.print lbl)
        (print_pattern p)
  | PNonbinding -> print "_"

and pattern_list ?(max_length = 299) p ppf =
  if max_length > 1 then
    match p with
    | PVariant (lbl, Some PTuple [v1; v2]) when lbl = CoreTypes.cons ->
        Format.fprintf ppf ",@ %t%t" (print_pattern v1)
          (pattern_list ~max_length:(max_length - 1) v2)
    | PVariant (lbl, None) when lbl = CoreTypes.nil -> ()
    | _ -> Format.fprintf ppf "(??? %t ???)" (print_pattern p)
  else Format.fprintf ppf ",@ ..."

let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | Apply (e1, e2) ->
      print ~at_level:1 "%t %t" (print_value e1)
        (print_value ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value %t" (print_value ~max_level:0 e)
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

and print_value ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (CoreTypes.Variable.print x)
  | Const c -> print "%t" (Const.print c)
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
  | Effect eff -> print "%t" (CoreTypes.Effect.print eff)

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
