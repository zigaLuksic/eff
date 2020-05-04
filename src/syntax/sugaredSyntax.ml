(** Abstract syntax of eff terms, types, and toplevel commands. *)
open CoreUtils

(** Terms *)
type variable = string

type effect = string

type theory = string

type label = string

type tyname = string

type typaram = string

type ty = plain_ty located

and plain_ty =
  | TyApply of tyname * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of typaram  (** ['a] *)
  | TyArrow of ty * ty  (** [ty1 -> ty2] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)
  | TyHandler of ty * ty  (** [ty1 => ty2] *)
  | TyCTySig of ty * effect list (** [ty!{eff1, eff2, ...}] *)
  | TyCTyTheory of ty * theory (** [ty!{theory}] *)

type tydef =
  | TySum of (label, ty option) Assoc.t
      (** [Label1 of ty1 | Label2 of ty2 | ... | Labeln of tyn | Label' | Label''] *)
  | TyInline of ty  (** [ty] *)

type pattern = plain_pattern located

and plain_pattern =
  | PVar of variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(* Changing the datatype [plain_pattern] will break [specialize_vector] in [exhaust.ml] because
   of wildcard matches there. *)

type term = plain_term located

and plain_term =
  | Var of variable  (** variables *)
  | Const of Const.t  (** integers, strings, booleans, and floats *)
  | Annotated of term * ty
  | Tuple of term list  (** [(t1, t2, ..., tn)] *)
  | Variant of label * term option  (** [Label] or [Label t] *)
  | Lambda of abstraction  (** [fun p1 p2 ... pn -> t] *)
  | Function of abstraction list  (** [function p1 -> t1 | ... | pn -> tn] *)
  | Effect of effect * term  (** [!eff arg], where [eff] is an effect symbol. *)
  | Handler of handler
      (** [handler clauses], where [clauses] are described below. *)
  | Let of (pattern * term) list * term
      (** [let p1 = t1 and ... and pn = tn in t] *)
  | LetRec of (variable * ty * term) list * term
      (** [let rec f1 p1 = t1 and ... and fn pn = tn in t] *)
  | Match of term * abstraction list
      (** [match t with p1 -> t1 | ... | pn -> tn] *)
  | Conditional of term * term * term  (** [if t then t1 else t2] *)
  | Apply of term * term  (** [t1 t2] *)
  | Handle of term * term  (** [with t1 handle t2] *)
  | Check of term  (** [check t] *)

and handler =
  { effect_clauses: (effect, abstraction2) Assoc.t
        (** [t1#op1 p1 k1 -> t1' | ... | tn#opn pn kn -> tn'] *)
  ; value_clause: abstraction option (** [val p -> t] *) }

and abstraction = pattern * term

and abstraction2 = pattern * pattern * term

(** Templates *)

type tctx = (string * ty) list

type template = plain_template located

and plain_template =
  | TLet of (pattern * term) list * template
  | TLetRec of (variable * ty * term) list * template
  | TMatch of term * (pattern * template) list
  | TConditional of term * template * template
  | TApply of variable * term
  | TEffect of effect * term * variable * template

(** Equations *)

type equation = plain_equation located

and plain_equation = {ctx: tctx; tctx: tctx; left_tmpl: template; right_tmpl: template}

let tplacebo = 
  { it= TApply ("Todo", {it= (Var "Todo"); at=Location.unknown})
  ; at= Location.unknown }


type theory_def =
  | Equation of equation
  | Theory of theory
