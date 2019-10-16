(* trans_syntax.thy *)
(* William Mansky *)
(* The syntax of a transformation specification language. *)

theory trans_syntax
imports "$AFP/List-Infinite/ListInfinite"
begin


fun flatten_option where
  "flatten_option (Some (Some x)) = Some x"
| "flatten_option _ = None"

(* General utility type for defining syntax with variables. *)
datatype ('data, 'mvar) literal = Inj 'data | MVar 'mvar

primrec lit_fv where
"lit_fv fv (Inj data) = fv data" |
"lit_fv _ (MVar mv) = {mv}"

lemma union_list_finite [simp]:
fixes f l 
assumes A: "\<forall> x. finite (f x)"
shows "finite (\<Union>x\<in>set l. f x)"
using A
by (induct l, auto)

lemma lit_fv_finite [simp]: fixes fv assumes A: "\<forall> t. finite (fv t)" shows "finite (lit_fv fv l)"
using A
by (case_tac l, auto)

abbreviation "base_lit_fv t \<equiv> lit_fv (\<lambda>x. {}) t"

lemma finite_base_lit_fv [simp]: "finite (base_lit_fv t)"
by (case_tac t, auto)

fun lit_subst where
  "lit_subst data_subst get_data \<sigma> (MVar x) = get_data (\<sigma> x)"
| "lit_subst data_subst get_data \<sigma> (Inj data) = data_subst \<sigma> data"

lemma lit_same_subst [simp]:
assumes DataCase: "\<forall>x. (\<forall> v \<in> data_fv x. \<sigma> v = \<sigma>' v) \<longrightarrow> (data_subst \<sigma> x = data_subst \<sigma>' x)"
and FV: "\<forall> v \<in> lit_fv data_fv x. \<sigma> v = \<sigma>' v"
shows "lit_subst data_subst get_data \<sigma> x = lit_subst data_subst get_data \<sigma>' x"
using DataCase and FV
by (cases x, auto)

definition base_lit_subst where
"base_lit_subst \<equiv> lit_subst (\<lambda>s. \<lambda> d. Some d)"

lemma base_lit_same_subst [simp]:
assumes  FV: "\<forall> v \<in> base_lit_fv x. \<sigma> v = \<sigma>' v"
shows "base_lit_subst get_data \<sigma> x = base_lit_subst get_data \<sigma>' x"
using FV
by (cases x, auto simp add: base_lit_subst_def)

(* Basic syntax bits: node and edge literals. *)
(* Note that these arguments are thread patterns (mvars), not concrete threads. *)
datatype 'mvar node_const = NStart 'mvar  | NExit 'mvar

type_synonym 'mvar node_lit = "('mvar node_const, 'mvar) literal"


(* Expression pattern e<e'> matches "an expression e with e' somewhere in it",
   allowing basic pattern-matching within a transformation. *)
datatype ('expr, 'mvar) expr_pattern 
=
       EPInj "'expr"
     | EPMVar "'mvar"
     | EPSubst 'mvar "'expr" ("_<_>" 102)

(* Collecting free variables. *)

primrec expr_pattern_fv where
"expr_pattern_fv expr_fv (EPInj e) = expr_fv e" |
"expr_pattern_fv expr_fv (x<e>) = insert x (expr_fv e)" |
"expr_pattern_fv expr_fv (EPMVar x) = {x}"

lemma expr_pattern_fv_finite [simp]:
fixes "expr_fv"and "ep" assumes A: "\<forall> e. finite (expr_fv e)" shows "finite (expr_pattern_fv expr_fv ep)"
using A
by (induct_tac "ep", auto)

fun node_fv where
"node_fv (NStart t) = {t}" |
"node_fv (NExit t) = {t}"

lemma node_fv_finite [simp]: shows "finite (node_fv n)" 
by (case_tac n, auto)

(* Actions are the atomic rewrites. *)
datatype ('mvar, 'edge_type, 'pattern) trans_action = 
   AReplace "'mvar node_lit" "'pattern list"
 | ARemoveEdge "'mvar node_lit" "'mvar node_lit" 'edge_type
 | AAddEdge "'mvar node_lit" "'mvar node_lit" 'edge_type
 | ASplitEdge "'mvar node_lit" "'mvar  node_lit" 'edge_type 'pattern

(* Side conditions are CTL formulae on program graphs. *)
datatype ('mvar, 'pred) side_cond = SCTrue | SCPred 'pred 
 | SCAnd "('mvar, 'pred) side_cond" "('mvar, 'pred) side_cond" (infixl "\<and>sc" 120) 
 | SCNot "('mvar, 'pred) side_cond" ("\<not>sc") 
 | SCAU "('mvar, 'pred) side_cond" "('mvar, 'pred) side_cond" ("A _ \<U> _" 125)
 | SCEU "('mvar, 'pred) side_cond" "('mvar, 'pred) side_cond" ("E _ \<U> _" 125)
 | SCAB "('mvar, 'pred) side_cond" "('mvar, 'pred) side_cond" ("A _ \<B> _" 125)
 | SCEB "('mvar, 'pred) side_cond" "('mvar, 'pred) side_cond" ("E _ \<B> _" 125)
 | SCEx 'mvar "('mvar, 'pred) side_cond"

primrec cond_fv where
"cond_fv _ SCTrue = {}" |
"cond_fv pred_fv (SCPred p) = pred_fv p" |
"cond_fv pred_fv (\<phi>1 \<and>sc \<phi>2) = cond_fv pred_fv \<phi>1 \<union> cond_fv pred_fv \<phi>2" |
"cond_fv pred_fv (\<not>sc \<phi>) = cond_fv pred_fv \<phi>" |
"cond_fv pred_fv (A \<phi>1 \<U> \<phi>2) = cond_fv pred_fv \<phi>1 \<union> cond_fv pred_fv \<phi>2" |
"cond_fv pred_fv (E \<phi>1 \<U> \<phi>2) = cond_fv pred_fv \<phi>1 \<union> cond_fv pred_fv \<phi>2" |
"cond_fv pred_fv (A \<phi>1 \<B> \<phi>2) = cond_fv pred_fv \<phi>1 \<union> cond_fv pred_fv \<phi>2" |
"cond_fv pred_fv (E \<phi>1 \<B> \<phi>2) = cond_fv pred_fv \<phi>1 \<union> cond_fv pred_fv \<phi>2" |
"cond_fv pred_fv (SCEx x \<phi>) = cond_fv pred_fv \<phi> - {x}"

lemma cond_fv_finite [simp, intro]: "\<forall>p. finite (pred_fv p) \<Longrightarrow> finite (cond_fv pred_fv \<phi>)"
by (induct \<phi>, auto)

abbreviation SCFalse where "SCFalse \<equiv> \<not>sc SCTrue"
abbreviation SCOr (infixl "\<or>sc" 110) where "\<phi>1 \<or>sc \<phi>2 \<equiv> \<not>sc (\<not>sc \<phi>1 \<and>sc \<not>sc \<phi>2)"
definition SCImp (infixl "\<longrightarrow>sc" 105) where "\<phi>1 \<longrightarrow>sc \<phi>2 \<equiv> \<not>sc (\<phi>1 \<and>sc \<not>sc \<phi>2)"
declare SCImp_def [simp]
abbreviation SCEF ("EF") where "EF \<phi> \<equiv> E SCTrue \<U> \<phi>"
abbreviation SCAF ("AF") where "AF \<phi> \<equiv> A SCTrue \<U> \<phi>"
abbreviation SCEG ("EG") where "EG \<phi> \<equiv> \<not>sc (AF (\<not>sc \<phi>))"
abbreviation SCAG ("AG") where "AG \<phi> \<equiv> \<not>sc (EF (\<not>sc \<phi>))"
abbreviation SCAll where "SCAll x \<phi> \<equiv> \<not>sc (SCEx x (\<not>sc \<phi>))"
abbreviation SCAW ("A _ \<W> _" 125) where "A \<phi> \<W> \<psi> \<equiv> \<not>sc (E \<not>sc \<psi> \<U> (\<not>sc \<phi> \<and>sc \<not>sc \<psi>))"
abbreviation SCEW ("E _ \<W> _" 125) where "E \<phi> \<W> \<psi> \<equiv> (E \<phi> \<U> \<psi>) \<or>sc EG \<phi>"
primrec SCAnds where
"SCAnds [] = SCTrue" |
"SCAnds (p#ps) = p \<and>sc SCAnds ps"
primrec SCOrs where
"SCOrs [] = SCFalse" |
"SCOrs (p#ps) = p \<or>sc SCOrs ps"

(* Transformations are the top-level specs. *)
(* State conditions are paired with metavars indicating the node at which they're evaluated. *)
datatype ('mvar, 'edge_type, 'pattern, 'pred) transform = 
  TIf "('mvar, 'edge_type, 'pattern) trans_action list" "('mvar, 'pred) side_cond"
| TMatch "('mvar, 'pred) side_cond" "('mvar, 'edge_type, 'pattern, 'pred) transform"
| TApplyAll "('mvar, 'edge_type, 'pattern, 'pred) transform"
| TChoice "('mvar, 'edge_type, 'pattern, 'pred) transform" "('mvar, 'edge_type, 'pattern, 'pred) transform"
| TThen "('mvar, 'edge_type, 'pattern, 'pred) transform" "('mvar, 'edge_type, 'pattern, 'pred) transform"

end
