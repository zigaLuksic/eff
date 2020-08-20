%{
  open SugaredSyntax
  open CoreUtils

  type handler_clause =
    | EffectClause of effect * abstraction2
    | ReturnClause of abstraction

  let collect_handler_clauses clauses =
    let (eff_cs, val_cs) =
      List.fold_left
        (fun (eff_cs, val_cs) clause ->
          match clause.it with
          | EffectClause (eff, a2) ->  ((eff, a2) :: eff_cs, val_cs)
          | ReturnClause a -> (eff_cs, Some a))
        ([], None) clauses
    in
    { effect_clauses = Assoc.of_list (List.rev eff_cs);
      value_clause = val_cs }

%}

%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COLON COMMA SEMI SEMISEMI EQUAL CONS EXCLAMATION
%token BEGIN END
%token <string> LNAME
%token UNDERSCORE
%token <int> INT
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token <SugaredSyntax.label> UNAME EFFNAME
%token <SugaredSyntax.typaram> PARAM
%token TYPE ARROW HARROW OF 
%token EFFECT VAL
%token THEORY FOR IS VDASH DOT REL
%token EXTERNAL
%token MATCH WITH FUNCTION HASH
%token LET REC AND IN
%token FUN BAR BARBAR
%token IF THEN ELSE
%token HANDLER AT HANDLE
%token PLUS STAR MINUS MINUSDOT
%token MOD OR
%token AMPER AMPERAMPER
%token <string> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4
%token CHECK
%token QUIT USE HELP
%token EOF

%nonassoc HANDLE ARROW IN
%right SEMI
%nonassoc ELSE
%right OR BARBAR
%right AMPER AMPERAMPER
%left  INFIXOP0 EQUAL
%right INFIXOP1 AT
%right CONS
%left  INFIXOP2 PLUS MINUS MINUSDOT
%left  INFIXOP3 STAR MOD
%right INFIXOP4

%start <Commands.t list> commands

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
commands:
  | lst = topdef_list
    { lst }
  | t = topterm EOF
     { [t] }
  | t = topterm SEMISEMI lst = commands
     { t :: lst }
  | dir = topdirective EOF
     { [dir] }
  | dir = topdirective SEMISEMI lst = commands
     { dir :: lst }

topdef_list:
  | EOF
     { [] }
  | def = topdef SEMISEMI lst = commands
     { def :: lst }
  | def = topdef lst = topdef_list
     { def :: lst }

topterm: mark_position(plain_topterm) { $1 }
plain_topterm:
  | t = term
    { Commands.Term t }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | TYPE defs = separated_nonempty_list(AND, ty_def)
    { Commands.Tydef (Assoc.of_list defs) }
  | LET defs = separated_nonempty_list(AND, let_def)
    { Commands.TopLet defs }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def)
    { Commands.TopLetRec defs }
  | EXTERNAL x = ident COLON t = ty EQUAL n = STRING
    { Commands.External (x, t, n) }
  | EFFECT eff = effect COLON t1 = ty_apply ARROW t2 = ty
    { Commands.DefEffect (eff, (t1, t2))}
  | THEORY theory = theory FOR LBRACE effs = separated_list(COMMA, effect_in_sig) RBRACE IS th_defs = theory_defs
    { Commands.DefTheory (theory, th_defs, effs) }


(* Toplevel directive If you change these, make sure to update lname as well,
   or a directive might become a reserved word. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | HASH QUIT
    { Commands.Quit }
  | HASH HELP
    { Commands.Help }
  | HASH TYPE t = term
    { Commands.TypeOf t }
  | HASH USE fn = STRING
    { Commands.Use fn }

(* Main syntax tree *)

term: mark_position(plain_term) { $1 }
plain_term:
  | MATCH t = term WITH cases = cases0(match_case) (* END *)
    { Match (t, cases) }
  | FUNCTION cases = cases(function_case) (* END *)
    { Function cases }
  | HANDLER h = handler (* END *)
    { h.it }
  | HANDLE t = term WITH h = handler (* END *)
    { Handle (h, t) }
  | FUN t = lambdas1(ARROW)
    { t.it }
  | LET defs = separated_nonempty_list(AND, let_def) IN t = term
    { Let (defs, t) }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def) IN t = term
    { LetRec (defs, t) }
  | WITH h = term HANDLE t = term
    { Handle (h, t) }
  | t1 = term SEMI t2 = term
    { Let ([{it= PNonbinding; at= t1.at}, t1], t2) }
  | IF t_cond = comma_term THEN t_true = term ELSE t_false = term
    { Conditional (t_cond, t_true, t_false) }
  | t = plain_comma_term
    { t }

comma_term: mark_position(plain_comma_term) { $1 }
plain_comma_term:
  | t = binop_term COMMA ts = separated_list(COMMA, binop_term)
    { Tuple (t :: ts) }
  | t = plain_binop_term
    { t }

binop_term: mark_position(plain_binop_term) { $1 }
plain_binop_term:
  | t1 = binop_term op = binop t2 = binop_term
    {
      let op_loc = Location.make $startpos(op) $endpos(op) in
      let partial = Apply ({it= Var op; at= op_loc}, t1) in
      let partial_pos = Location.make $startpos(t1) $endpos(op) in
      Apply ({it= partial; at= partial_pos}, t2)
    }
  | t1 = binop_term CONS t2 = binop_term
    { let tuple = {it= Tuple [t1; t2]; at= Location.make $startpos $endpos} in
      Variant (CoreTypes.cons_annot, Some tuple) }
  | t = plain_uminus_term
    { t }

uminus_term: mark_position(plain_uminus_term) { $1 }
plain_uminus_term:
  | MINUS t = uminus_term
    { let op_loc = Location.make $startpos($1) $endpos($1) in
      Apply ({it= Var "~-"; at= op_loc}, t) }
  | MINUSDOT t = uminus_term
    { let op_loc = Location.make $startpos($1) $endpos($1) in
      Apply ({it= Var "~-."; at= op_loc}, t) }
  | t = plain_app_term
    { t }

plain_app_term:
  | CHECK t = prefix_term
    { Check t }
  | t = prefix_term ts = prefix_term+
    {
      match t.it, ts with
      | Variant (lbl, None), [t] -> Variant (lbl, Some t)
      | Variant (lbl, _), _ -> 
          Error.syntax ~loc:(t.at) 
          ("Constructor [%s] applied to multiple arguments, "
          ^^"but constructors accept at most one argument. Please provide parentheses.") lbl
      | _, _ ->
        let apply t1 t2 = {it= Apply(t1, t2); at= Location.union [t1.at; t2.at]} in
        (List.fold_left apply t ts).it
    }
  | eff = invoked_effect ts = prefix_term+
    {
      match ts with
      | [t] -> Effect (eff, t)
      | _ -> 
          Error.syntax ~loc:(Location.make $startpos(eff) $endpos(eff)) 
          ("Effect [%s] applied to multiple arguments, "
          ^^"but effect invocations accept at most one argument. Please provide parentheses.") eff
    }
  | t = plain_prefix_term
    { t }

prefix_term: mark_position(plain_prefix_term) { $1 }
plain_prefix_term:
  | op = prefixop t = simple_term
    {
      let op_loc = Location.make $startpos(op) $endpos(op) in
      Apply ({it= Var op; at= op_loc}, t)
    }
  | t = plain_simple_term
    { t }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | x = ident
    { Var x }
  | lbl = UNAME
    { Variant (lbl, None) }
  | cst = const_term
    { Const cst }
  | LBRACK ts = separated_list(SEMI, comma_term) RBRACK
    {
      let nil = {it= Variant (CoreTypes.nil_annot, None); at= Location.make $endpos $endpos} in
      let cons t ts =
        let loc = Location.union [t.at; ts.at] in
        let tuple = {it= Tuple [t; ts];at= loc} in
        {it= Variant (CoreTypes.cons_annot, Some tuple); at= loc}
      in
      (List.fold_right cons ts nil).it
    }
  | LPAREN RPAREN
    { Tuple [] }
  | LPAREN t = term COLON ty = ty RPAREN
    { Annotated (t, ty) }
  | LPAREN t = plain_term RPAREN
    { t }
  | BEGIN t = plain_term END
    { t }

(* Auxilliary definitions *)

const_term:
  | n = INT
    { Const.of_integer n }
  | str = STRING
    { Const.of_string str }
  | b = BOOL
    { Const.of_boolean b }
  | f = FLOAT
    { Const.of_float f }

function_case:
  | p = pattern ARROW t = term
    { (p, t) }

match_case:
  | p = pattern ARROW t = term
    { (p, t) }

template_match_case:
  | p = pattern ARROW t = template
    { (p, t) }

lambdas0(SEP):
  | SEP t = term
    { t }
  | p = simple_pattern t = lambdas0(SEP)
    { {it= Lambda (p, t); at= Location.make $startpos $endpos} }

lambdas1(SEP):
  | p = simple_pattern t = lambdas0(SEP)
    { {it= Lambda (p, t); at= Location.make $startpos $endpos} }

let_def:
  | p = pattern EQUAL t = term
    { (p, t) }
  | p = pattern COLON ty = ty EQUAL t = term
    { (p, {it= Annotated(t, ty); at= t.at}) }
  | x = mark_position(ident) t = lambdas1(EQUAL)
    { ({it= PVar x.it; at= x.at}, t) }
  | LPAREN x = mark_position(ident) COLON ty = ty RPAREN t = lambdas1(EQUAL)
    { ({it= PVar x.it; at= x.at}, {it= Annotated(t, ty); at= t.at}) }

let_rec_def:
  | LPAREN f = ident COLON ty = ty RPAREN t = lambdas0(EQUAL)
    { (f, ty, t) }

handler_clause: mark_position(plain_handler_clause) { $1 }
plain_handler_clause:
  | EFFECT eff = effect p = simple_pattern k = simple_pattern ARROW t = term
    { EffectClause (eff, (p, k, t)) }
  | EFFECT eff = effect  k = simple_pattern ARROW t = term
    { let unit_loc = Location.make $startpos(eff) $endpos(eff) in
      EffectClause (eff, ({it= PTuple []; at= unit_loc}, k, t)) }
  | VAL c = function_case
    { ReturnClause c }

pattern: mark_position(plain_pattern) { $1 }
plain_pattern:
  | p = comma_pattern
    { p.it }

comma_pattern: mark_position(plain_comma_pattern) { $1 }
plain_comma_pattern:
  | ps = separated_nonempty_list(COMMA, cons_pattern)
    { match ps with [p] -> p.it | ps -> PTuple ps }

cons_pattern: mark_position(plain_cons_pattern) { $1 }
plain_cons_pattern:
  | p = variant_pattern
    { p.it }
  | p1 = variant_pattern CONS p2 = cons_pattern
    { let ptuple = {it= PTuple [p1; p2]; at= Location.make $startpos $endpos} in
      PVariant (CoreTypes.cons_annot, Some ptuple) }

variant_pattern: mark_position(plain_variant_pattern) { $1 }
plain_variant_pattern:
  | lbl = UNAME p = simple_pattern
    { PVariant (lbl, Some p) }
  | p = simple_pattern
    { p.it }

simple_pattern: mark_position(plain_simple_pattern) { $1 }
plain_simple_pattern:
  | x = ident
    { PVar x }
  | lbl = UNAME
    { PVariant (lbl, None) }
  | UNDERSCORE
    { PNonbinding }
  | cst = const_term
    { PConst cst }
  | LBRACK ts = separated_list(SEMI, pattern) RBRACK
    {
      let nil = {it= PVariant (CoreTypes.nil_annot, None);at= Location.make $endpos $endpos} in
      let cons t ts =
        let loc = Location.union [t.at; ts.at] in
        let tuple = {it= PTuple [t; ts]; at= loc} in
        {it= PVariant (CoreTypes.cons_annot, Some tuple); at= loc}
      in
      (List.fold_right cons ts nil).it
    }
  | LPAREN RPAREN
    { PTuple [] }
  | LPAREN p = pattern RPAREN
    { p.it }

handler: mark_position(plain_handler) { $1 }
plain_handler:
  | cs = cases(handler_clause)
    { Handler (collect_handler_clauses cs) }

lname:
  | x = LNAME
    { x }
  | QUIT
    { "quit" }
  | HELP
    { "help" }
  | USE
    { "use" }

tyname:
  | t = lname
    { t }

ident:
  | x = lname
    { x }
  | LPAREN op = binop RPAREN
    { op }
  | LPAREN op = PREFIXOP RPAREN
    { op }

%inline binop:
  | OR
    { "or" }
  | BARBAR
    { "||" }
  | AMPER
    { "&" }
  | AMPERAMPER
    { "&&" }
  | AT
    { "@" }
  | op = INFIXOP0
    { op }
  | op = INFIXOP1
    { op }
  | op = INFIXOP2
    { op }
  | PLUS
    { "+" }
  | MINUSDOT
    { "-." }
  | MINUS
    { "-" }
  | EQUAL
    { "=" }
  | op = INFIXOP3
    { op }
  | STAR
    { "*" }
  | op = INFIXOP4
    { op }
  | MOD
    { "mod" }


%inline prefixop:
  | op = PREFIXOP
    { op }

cases0(case):
  | BAR? cs = separated_list(BAR, case)
    { cs }

cases(case):
  | BAR? cs = separated_nonempty_list(BAR, case)
    { cs }

mark_position(X):
  x = X
  { {it= x; at= Location.make $startpos $endpos}}

pol_param:
  | p = PARAM
    { (p, Tctx.Fixed) }
  | PLUS p = PARAM
    { (p, Tctx.Co) }
  | MINUS p = PARAM
    { (p, Tctx.Contra) }

pol_params:
  |
    { [] }
  | p = pol_param
    { [p] }
  | LPAREN ps = separated_nonempty_list(COMMA, pol_param) RPAREN
    { ps }

ty_def:
  | ps = pol_params t = tyname EQUAL x = defined_ty
    { (t, (Assoc.of_list ps, x)) }

defined_ty:
  | lst = cases(sum_case)
    { TySum (Assoc.of_list lst) }
  | t = ty
    { TyInline t }

ty: mark_position(plain_ty) { $1 }
plain_ty:
  | t = ty_apply EXCLAMATION LBRACE effs = separated_list(COMMA, effect_in_sig) RBRACE
    { TyCTySig(t, effs) }
  | t = ty_apply EXCLAMATION theory = theory
    { TyCTyTheory(t, theory) }
  | t1 = ty_apply ARROW t2 = ty
    { TyArrow (t1, t2) }
  | t1 = ty HARROW t2 = ty
    { TyHandler (t1, t2) }
  | t = plain_prod_ty
    { t }

prod_ty: mark_position(plain_prod_ty) { $1 }
plain_prod_ty:
  | ts = separated_nonempty_list(STAR, ty_apply)
    {
      match ts with
      | [] -> assert false
      | [t] -> t.it
      | _ -> TyTuple ts
     }

ty_apply: mark_position(plain_ty_apply) { $1 }
plain_ty_apply:
  | LPAREN t = ty COMMA ts = separated_nonempty_list(COMMA, ty) RPAREN t2 = tyname
    { TyApply (t2, (t :: ts)) }
  | t = ty_apply t2 = tyname
    { TyApply (t2, [t]) }
  | t = plain_simple_ty
    { t }

plain_simple_ty:
  | t = tyname
    { TyApply (t, []) }
  | t = PARAM
    { TyParam t }
  | LPAREN t = ty RPAREN
    { t.it }

sum_case:
  | lbl = UNAME
    { (lbl, None) }
  | lbl = UNAME OF t = ty
    { (lbl, Some t) }

effect_in_sig:
  | eff = effect
    { GlobEff eff }
  | eff = effect COLON ty1 = prod_ty ARROW ty2 = prod_ty
    { LocEff (eff, ty1, ty2) }

effect:
  | eff = UNAME
    { eff }

invoked_effect:
  | eff = EFFNAME
    { eff }

theory:
  | theory = LNAME
    { theory}

theory_defs:
  | LBRACE RBRACE
    { [] }
  | th_defs = separated_nonempty_list(AND, theory_def)
    { th_defs }

theory_def:
  | equation = equation
    { Equation equation }
  | theory = theory
    { Theory theory }

equation: mark_position(plain_equation) { $1 }
plain_equation:
  | LBRACE ctx = ctx(ctx_var) SEMI tctx = ctx(tctx_var) VDASH  tmpl1 = template REL tmpl2 = template RBRACE
    { {ctx=ctx; tctx=tctx; left_tmpl=tmpl1; right_tmpl=tmpl2 } }

ctx(var):
  | DOT
    { [] }
  | ctx = separated_nonempty_list(COMMA, var)
    { ctx }

ctx_var:
  | x = ident COLON ty = ty
    { (x, ty) }

tctx_var:
  | x = ident COLON ty = prod_ty ARROW STAR
    { (x, ty) }


template: mark_position(plain_template) { $1 }
plain_template:
  | MATCH t = term WITH tcases = cases0(template_match_case) (* END *)
    { TMatch (t, tcases) }
  | LET defs = separated_nonempty_list(AND, let_def) IN tmpl = template
    { TLet (defs, tmpl) }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def) IN tmpl = template
    { TLetRec (defs, tmpl) }
  | IF t_cond = comma_term THEN tmpl_true = template ELSE tmpl_false = template
    { TConditional (t_cond, tmpl_true, tmpl_false) }
  | id = ident t = simple_term
    { TApply (id, t) }
  | eff = effect LPAREN t = term SEMI id = ident DOT tmpl = template RPAREN
    { TEffect (eff, t, id, tmpl) }

%%
