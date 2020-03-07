(* simple_language.thy *)
(* William Mansky *)
(* A simple concurrent language. *)

theory simple_language
imports trans_flowgraph
begin

(* Syntax *)
datatype 'var expr = Num int | Var 'var | Plus "'var expr" "'var expr" (infixl "+L" 104)
 | Eq "'var expr" "'var expr" (infix "===" 103)
(* Do we need wait for anything? *)
datatype ('var, 'expr) instr = assign 'var 'expr (infixr "\<leftarrow>" 101) | wait 'expr | branchifz 'expr 
 | branch | lock 'var | unlock 'var

(* Free variables *)
primrec expr_fv where
"expr_fv (Num i) = {}" |
"expr_fv (Var x) = {x}" |
"expr_fv (e +L e') = expr_fv e \<union> expr_fv e'" |
"expr_fv (e === e') = expr_fv e \<union> expr_fv e'"
lemma finite_expr_fv [simp]: "finite (expr_fv e)"
by (induct e, auto)
corollary finite_expr_pattern_fv [simp]: "finite (expr_pattern_fv expr_fv e)"
by (case_tac e, auto)

primrec instr_fv where
"instr_fv (x \<leftarrow> e) = insert x (expr_fv e)" |
"instr_fv (wait e) = expr_fv e" |
"instr_fv (branchifz e) = expr_fv e" |
"instr_fv branch = {}" |
"instr_fv (lock x) = {x}" |
"instr_fv (unlock x) = {x}"

(* Instruction patterns for use in specifications. *)
type_synonym 'mvar pattern = "(('mvar, ('mvar, 'mvar expr) expr_pattern) instr, 'mvar) literal"

primrec instr_pattern_fv where
"instr_pattern_fv (x \<leftarrow> e) = insert x (expr_pattern_fv expr_fv e)" |
"instr_pattern_fv (wait e) = expr_pattern_fv expr_fv e" |
"instr_pattern_fv (branchifz e) = expr_pattern_fv expr_fv e" |
"instr_pattern_fv branch = {}" |
"instr_pattern_fv (lock x) = {x}" |
"instr_pattern_fv (unlock x) = {x}"
lemma finite_instr_pattern_fv [simp]: "finite (instr_pattern_fv i)"
by (induct i, auto)

abbreviation pattern_fv::"'mvar pattern \<Rightarrow> 'mvar set" where
"pattern_fv p \<equiv> lit_fv instr_pattern_fv p"

lemma finite_pattern_fv [simp]: "finite (pattern_fv p)"
by (case_tac p, auto)

(* Applying a valuation of metavariables to an expression pattern yields a concrete expression. *)
primrec expr_subst where
"expr_subst \<sigma> (Num i) = Some (Num i)" |
"expr_subst \<sigma> (Var x) = (case \<sigma> x of OExpr e \<Rightarrow> Some e | _ \<Rightarrow> None)" |
"expr_subst \<sigma> (a +L b) = (case (expr_subst \<sigma> a, expr_subst \<sigma> b) of 
  (Some a', Some b') \<Rightarrow> Some (a' +L b') | _ \<Rightarrow> None)" |
"expr_subst \<sigma> (a === b) = (case (expr_subst \<sigma> a, expr_subst \<sigma> b) of
 (Some a', Some b') \<Rightarrow> Some (a' === b') | _ \<Rightarrow> None)"

lemma expr_fv_finite [simp]: "finite (expr_fv e)"
by (induct e, auto)

lemma expr_same_subst: "\<forall>v\<in>expr_fv e. \<sigma> v = \<sigma>' v \<Longrightarrow>
 expr_subst \<sigma> e = expr_subst \<sigma>' e"
by (induct e, auto)

lemma self_subst: "expr_subst (\<lambda>y. OExpr (Var y)) e = Some e"
by (induct e, auto)

corollary subst_out: "\<forall>v\<in>expr_fv e. \<sigma> v = OExpr (Var v) \<Longrightarrow> expr_subst \<sigma> e = Some e"
by (rule trans, rule expr_same_subst, auto simp add: self_subst)

lemma sub_out: "\<lbrakk>v \<in> expr_fv e; v' \<notin> expr_fv e\<rbrakk> \<Longrightarrow> \<exists>e'. 
 expr_subst ((\<lambda>y. OExpr (Var y))(v := OExpr (Var v'))) e = Some e' \<and>
 expr_subst ((\<lambda>y. OExpr (Var y))(v' := OExpr (Var v))) e' = Some e"
apply (induct e, simp+)
apply (case_tac "v \<in> expr_fv e1", clarsimp)
apply (case_tac "v \<in> expr_fv e2", clarsimp+)
apply (cut_tac e=e2 and \<sigma>="(\<lambda>y. OExpr (Var y))(v := OExpr (Var v'))" in subst_out, simp+)
apply (cut_tac e=e2 and \<sigma>="(\<lambda>y. OExpr (Var y))(v' := OExpr (Var v))" in subst_out, simp+)
apply (rule_tac x="e' +L e2" in exI, simp)
apply (rule conjI)
apply (rule trans, erule option.weak_case_cong, simp+)+
apply clarsimp
apply (cut_tac e=e1 and \<sigma>="(\<lambda>y. OExpr (Var y))(v := OExpr (Var v'))" in subst_out, simp+)
apply (cut_tac e=e1 and \<sigma>="(\<lambda>y. OExpr (Var y))(v' := OExpr (Var v))" in subst_out, simp+)
apply (rule_tac x="e1 +L e'" in exI, simp)
apply (rule conjI)
apply (rule trans, erule option.weak_case_cong, simp+)+
apply clarsimp
apply (case_tac "v \<in> expr_fv e1", clarsimp)
apply (case_tac "v \<in> expr_fv e2", clarsimp+)
apply (cut_tac e=e2 and \<sigma>="(\<lambda>y. OExpr (Var y))(v := OExpr (Var v'))" in subst_out, simp+)
apply (cut_tac e=e2 and \<sigma>="(\<lambda>y. OExpr (Var y))(v' := OExpr (Var v))" in subst_out, simp+)
apply (rule_tac x="e' === e2" in exI, simp)
apply (rule conjI)
apply (rule trans, erule option.weak_case_cong, simp+)+
apply clarsimp
apply (cut_tac e=e1 and \<sigma>="(\<lambda>y. OExpr (Var y))(v := OExpr (Var v'))" in subst_out, simp+)
apply (cut_tac e=e1 and \<sigma>="(\<lambda>y. OExpr (Var y))(v' := OExpr (Var v))" in subst_out, simp+)
apply (rule_tac x="e1 === e'" in exI, simp)
apply (rule conjI)
apply (rule trans, erule option.weak_case_cong, simp+)+
done

primrec expr_pattern_subst :: "('mvar \<Rightarrow> ('thread, 'node, 'var expr, 'instr) object) \<Rightarrow> 
 ('mvar, 'mvar expr) expr_pattern \<Rightarrow> 'var expr option"  where
"expr_pattern_subst \<sigma> (EPInj e) = expr_subst \<sigma> e" |
"expr_pattern_subst \<sigma> (x<e>) = (case (\<sigma> x, expr_subst \<sigma> e) of 
 (OSynFunc (Var x) e, Some e') \<Rightarrow> expr_subst ((\<lambda>y. OExpr (Var y))
 (x := (OExpr e')::('thread, 'node, 'var expr, 'instr) object)) e | _ \<Rightarrow> None)"
(* Isabelle note: this lengthy type annotation is necessary because OExpr e', in itself,
   is of type (?, ?, expr, ?) object.  We need to identify the missing types with existing
   type variables, or they'll be introduced as separate variables. *)

lemma expr_pattern_fv_finite [simp]: "finite (expr_pattern_fv expr_fv e)"
by (induct e, auto)

lemma expr_pattern_same_subst: "\<forall>v\<in>expr_pattern_fv expr_fv e. \<sigma> v = \<sigma>' v \<Longrightarrow>
 expr_pattern_subst \<sigma> e = expr_pattern_subst \<sigma>' e"
apply (induct e, auto simp add: expr_same_subst)
apply (case_tac "\<sigma>' mvar", simp_all)
apply (case_tac expr1, simp_all)
apply (drule expr_same_subst, simp)
done

(* Similarly, applying a valuation of metavariables to an instruction pattern yields a concrete instruction. *)
primrec instr_subst where
"instr_subst \<sigma> (x \<leftarrow> e) = (case (\<sigma> x, expr_pattern_subst \<sigma> e) of
  (OExpr (Var y), Some e') \<Rightarrow> Some (y \<leftarrow> e') | _ \<Rightarrow> None)" |
"instr_subst \<sigma> (wait e) = (case expr_pattern_subst \<sigma> e of
  Some e' \<Rightarrow> Some (wait e') | _ \<Rightarrow> None)" |
"instr_subst \<sigma> (branchifz e) = (case expr_pattern_subst \<sigma> e of
  Some e' \<Rightarrow> Some (branchifz e') | _ \<Rightarrow> None)" |
"instr_subst _ branch = Some branch" |
"instr_subst \<sigma> (lock x) = (case \<sigma> x of OExpr (Var y) \<Rightarrow> Some (lock y) | _ \<Rightarrow> None)" |
"instr_subst \<sigma> (unlock x) = (case \<sigma> x of OExpr (Var y) \<Rightarrow> Some (unlock y) | _ \<Rightarrow> None)"

primrec subst where
"subst \<sigma> (Inj i) = instr_subst \<sigma> i" |
"subst \<sigma> (MVar x) = (case \<sigma> x of OInstr i \<Rightarrow> Some i)"

(* Utility functions for analysis of expressions. *)

primrec is_const where
"is_const (Num _) = True" |
"is_const (_ +L _) = False" |
"is_const (Var _) = False" |
"is_const (_ === _) = False"

primrec is_var where
"is_var (Num _) = False" |
"is_var (_ +L _) = False" |
"is_var (Var _) = True" |
"is_var (_ === _) = False"

(* Semantics on CFGs *)
primrec instr_edges where
"instr_edges (x \<leftarrow> e) = {\<lambda>t. case t of Seq \<Rightarrow> 1 | Branch \<Rightarrow> 0}" |
"instr_edges (wait e) = {\<lambda>t. case t of Seq \<Rightarrow> 1 | Branch \<Rightarrow> 0}" |
"instr_edges (branchifz e) = {\<lambda>t. case t of Seq \<Rightarrow> 1 | Branch \<Rightarrow> 1}" |
"instr_edges branch = {\<lambda>t. case t of Seq \<Rightarrow> 0 | Branch \<Rightarrow> 1}" |
"instr_edges (lock x) = {\<lambda>t. case t of Seq \<Rightarrow> 1 | Branch \<Rightarrow> 0}" |
"instr_edges (unlock x) = {\<lambda>t. case t of Seq \<Rightarrow> 1 | Branch \<Rightarrow> 0}"

definition "empty_env \<equiv> \<lambda>x. 0"

primrec eval where
"eval env (Num i) = i" |
"eval env (Var x) = env x" |
"eval env (e +L e') = eval env e + eval env e'" |
"eval env (e === e') = (if eval env e = eval env e' then 1 else 0)"

lemma eval_same: "\<forall>x\<in>expr_fv e. env x = env' x \<Longrightarrow> eval env e = eval env' e"
by (induct e, auto)

lemma eval_subst: "\<lbrakk>eval env y = eval env' y'; expr_subst (\<sigma>(x := OExpr (Var x))) e = Some e'; 
 \<forall>x\<in>expr_fv e'. env x = env' x;
 expr_subst (\<sigma>(x := OExpr y)) e = Some a; expr_subst (\<sigma>(x := OExpr y')) e = Some a'\<rbrakk> \<Longrightarrow>
 eval env a = eval env' a'"
apply (induct e arbitrary: e' a a', auto)
apply (case_tac "var = x", simp_all)
apply (case_tac "\<sigma> var", simp_all, erule eval_same)
apply (case_tac "expr_subst (\<sigma>(x := OExpr (Var x))) e1", simp+, case_tac "expr_subst (\<sigma>(x := OExpr (Var x))) e2", simp+)
apply (case_tac "expr_subst (\<sigma>(x := OExpr y)) e1", simp+, case_tac "expr_subst (\<sigma>(x := OExpr y)) e2", simp+)
apply (case_tac "expr_subst (\<sigma>(x := OExpr y')) e1", simp+, case_tac "expr_subst (\<sigma>(x := OExpr y')) e2", simp+)
apply clarsimp
apply (case_tac "expr_subst (\<sigma>(x := OExpr (Var x))) e1", simp+, case_tac "expr_subst (\<sigma>(x := OExpr (Var x))) e2", simp+)
apply (case_tac "expr_subst (\<sigma>(x := OExpr y)) e1", simp+, case_tac "expr_subst (\<sigma>(x := OExpr y)) e2", simp+)
apply (case_tac "expr_subst (\<sigma>(x := OExpr y')) e1", simp+, case_tac "expr_subst (\<sigma>(x := OExpr y')) e2", simp+)
apply clarsimp
done

locale simple_flowgraph = flowgraph where 
 instr_edges="instr_edges::(string, string expr) instr \<Rightarrow> (edge_type \<Rightarrow> nat) set"
begin

definition "next_seq p \<equiv> SOME p'. p' \<in> out_by_t Edges Seq p"
definition "next_branch p \<equiv> SOME p'. p' \<in> out_by_t Edges Branch p"

lemma start_seq_correct: "(Start, next_seq Start, Seq) \<in> Edges"
apply (simp add: next_seq_def, cut_tac P="\<lambda>p'. p' \<in> out_by_t Edges Seq Start" in someI_ex, 
 auto simp add: out_by_t_def)
apply (rule has_start)
done

lemma next_seq_correct: "\<lbrakk>p \<in> Nodes; p \<noteq> Exit; L p \<noteq> branch\<rbrakk> \<Longrightarrow> (p, next_seq p, Seq) \<in> Edges"
apply (simp add: next_seq_def, cut_tac P="\<lambda>p'. p' \<in> out_by_t Edges Seq p" in someI_ex, 
 auto simp add: out_by_t_def)
apply (case_tac "p = Start", simp add: has_start)
apply (drule instr_edges_ok, simp+)
apply (case_tac "L p", simp_all)
apply (simp add: unique_seq, simp add: out_edges_def, force)+
apply (simp add: unique_pair, simp add: out_edges_def, force)
apply (simp add: unique_seq, simp add: out_edges_def, force)+
done

lemma next_seq_out: "\<lbrakk>p \<in> Nodes; p \<noteq> Exit; L p \<noteq> branch\<rbrakk> \<Longrightarrow> (next_seq p, Seq) \<in> out_edges Edges p"
by (simp add: out_edges_def next_seq_correct)

lemma next_branch_correct: "\<lbrakk>p \<in> Nodes; p \<noteq> Start; p \<noteq> Exit; L p = branch \<or> (\<exists>e. L p = branchifz e)\<rbrakk> \<Longrightarrow> 
 (p, next_branch p, Branch) \<in> Edges"
apply (simp add: next_branch_def, cut_tac P="\<lambda>p'. p' \<in> out_by_t Edges Branch p" in someI_ex, 
 auto simp add: out_by_t_def)
apply (drule instr_edges_ok, simp+, simp add: unique_branch, simp add: out_edges_def, force)
apply (drule instr_edges_ok, simp+, simp add: unique_pair, simp add: out_edges_def, force)
done

lemma next_branch_out: "\<lbrakk>p \<in> Nodes; p \<noteq> Start; p \<noteq> Exit; L p = branch \<or> (\<exists>e. L p = branchifz e)\<rbrakk> \<Longrightarrow> 
 (next_branch p, Branch) \<in> out_edges Edges p"
by (simp add: out_edges_def next_branch_correct)

(* At first pass, all vars are global. *)
(* Semantics of a single thread *)
fun step_one_thread where
"step_one_thread p env = 
 (if p = Start then (next_seq p, []) else 
  if p = Exit then (p, []) (* unless we want to terminate? *) else case L p of 
    x \<leftarrow> e \<Rightarrow> (next_seq p, [(x, eval env e)])
  | wait e \<Rightarrow> if eval env e = 0 then (p, []) else (next_seq p, [])
  | branchifz e \<Rightarrow> if eval env e = 0 then (next_branch p, []) else (next_seq p, [])
  | branch \<Rightarrow> (next_branch p, [])
  | lock x \<Rightarrow> if env x = 0 then (next_seq p, [(x, 1)]) else (p, [])
  | unlock x \<Rightarrow> if env x = 1 then (next_seq p, [(x, 0)]) else (p, []))"

end

term simple_flowgraph.step_one_thread
abbreviation "step_one_thread G \<equiv> 
 simple_flowgraph.step_one_thread (Edges G) (Start G) (Exit G) (Label G)"
lemmas step_one_thread_simps = simple_flowgraph.step_one_thread.simps

lemma is_simple_flowgraph [simp]: "is_flowgraph G instr_edges = 
 simple_flowgraph (Nodes G) (Edges G) (Start G) (Exit G) (Label G)"
by (auto simp add: is_flowgraph_def simple_flowgraph_def flowgraph_def is_doubly_pointed_graph_def)

lemma step_same_step: "\<lbrakk>\<forall>x. env x = env' x \<or> (\<forall>n \<in> Nodes G. x \<notin> instr_fv (Label G n)); 
 is_flowgraph G instr_edges; p \<in> Nodes G\<rbrakk> \<Longrightarrow> step_one_thread G p env = step_one_thread G p env'"
apply (clarsimp simp add: simple_flowgraph.step_one_thread.simps)
apply (case_tac "Label G p", simp_all)
apply (rule eval_same, force)
apply (cut_tac e=expr and env=env and env'=env' in eval_same, force, simp)
apply (cut_tac e=expr and env=env and env'=env' in eval_same, force, simp)
apply force+
done

(* Semantics of an entire tCFG, with true concurrency. *)
definition "update_map env changes \<equiv> \<lambda>x. case changes x of Some v \<Rightarrow> v | None \<Rightarrow> env x"

lemma update_map_in [simp]: "change_map x = Some v \<Longrightarrow> update_map env change_map x = v"
by (simp add: update_map_def)

lemma update_map_out [simp]: "change_map x = None \<Longrightarrow> update_map env change_map x = env x"
by (simp add: update_map_def)

lemma update_map_change [dest!]: "update_map env change_map x \<noteq> update_map env' change_map x \<Longrightarrow>
 change_map x = None \<and> env x \<noteq> env' x"
by (simp add: update_map_def split: option.splits)

lemma update_case1 [simp]: "P x \<Longrightarrow> 
 update_map m (\<lambda>x. if P x then m1 x else m2 x) x = update_map m m1 x"
by (simp add: update_map_def)

lemma update_case2 [simp]: "\<not>P x \<Longrightarrow> 
 update_map m (\<lambda>x. if P x then m1 x else m2 x) x = update_map m m2 x"
by (simp add: update_map_def)

lemma update_same: "\<lbrakk>update_map m m1 = update_map m m2; m x = m' x\<rbrakk> \<Longrightarrow>
 update_map m' m1 x = update_map m m2 x"
apply (drule_tac x=x in fun_cong)
apply (case_tac "m1 x", simp+)
done

lemma update_same_x: "\<lbrakk>update_map m m1 x = update_map m m2 x; m x = m' x\<rbrakk> \<Longrightarrow>
 update_map m' m1 x = update_map m m2 x"
by (case_tac "m1 x", simp+)

inductive step where
step [intro]: "\<lbrakk>\<forall>t\<in>ts. \<exists>G n. CFGs t = Some G \<and> ps t = Some n \<and>
 (\<exists>n' change. step_one_thread G n env = (n', change) \<and> changes t = change \<and> ps' t = Some n' \<and>
  (\<forall>x. Label G n = lock x \<and> n' \<noteq> n \<longrightarrow> locker x = t));
 \<forall>t. t \<notin> ts \<longrightarrow> ps' t = ps t \<and> changes t = []; 
(* If a change is added, it was taken from some thread's step. *)
 \<forall>x v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t));
(* If a variable was changed by some thread, it will be changed in the environment
   (but not necessarily by that thread). *)
 \<forall>x v t. (x, v) \<in> set (changes t) \<longrightarrow> (\<exists>v'. change_map x = Some v');
 env' = update_map env change_map\<rbrakk> \<Longrightarrow> 
 step CFGs (env, ps) (env', ps')"

(* We can eliminate the set ts. *)
inductive step' where
step' [intro]: "\<lbrakk>\<forall>t. (\<exists>G n. CFGs t = Some G \<and> ps t = Some n \<and>
 (\<exists>n' change. step_one_thread G n env = (n', change) \<and> changes t = change \<and> ps' t = Some n' \<and>
  (\<forall>x. Label G n = lock x \<and> n' \<noteq> n \<longrightarrow> locker x = t))) \<or> (ps' t = ps t \<and> changes t = []); 
(* If a change is added, it was taken from some thread's step. *)
 \<forall>x v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t));
(* If a variable was changed by some thread, it will be changed in the environment
   (but not necessarily by that thread). *)
 \<forall>x v t. (x, v) \<in> set (changes t) \<longrightarrow> (\<exists>v'. change_map x = Some v');
 env' = update_map env change_map\<rbrakk> \<Longrightarrow> 
 step' CFGs (env, ps) (env', ps')"

lemma step_step': "step = step'"
apply (rule ext)+
apply (rule iffI)
apply (erule step.cases, clarsimp, rule_tac locker=locker in step', simp_all, clarsimp)
apply (erule_tac x=t in ballE, clarsimp+)
apply (erule step'.cases, clarsimp, rule_tac locker=locker and ts="{t. ps' t \<noteq> ps t \<or> changes t \<noteq> []}" in step, 
 simp_all, clarsimp)
apply (erule_tac x=t in allE, clarsimp)
done

inductive step_star where
step_star_refl [simp]: "step_star CFGs C C" |
step_star_trans: "\<lbrakk>step CFGs C C'; step_star CFGs C' C''\<rbrakk> \<Longrightarrow> step_star CFGs C C''"

lemma step_star_trans_gen: "\<lbrakk>step_star CFGs C C'; step_star CFGs C' C''\<rbrakk> \<Longrightarrow>
 step_star CFGs C C''"
apply (induct rule: step_star.induct, auto)
apply (rule step_star_trans, simp+)
done

lemma step_star_write [rule_format]: "\<lbrakk>step_star CFGs C C'\<rbrakk> \<Longrightarrow>
 fst C x \<noteq> fst C' x \<longrightarrow> (\<exists>env'' ps'' t G n. step_star CFGs C (env'', ps'') \<and> step_star CFGs (env'', ps'') C' \<and>
 CFGs t = Some G \<and> ps'' t = Some n \<and> (x, fst C' x) \<in> set (snd (step_one_thread G n env'')))"
apply (induct rule: step_star.induct, simp, clarsimp)
apply (case_tac "aa x \<noteq> ab x", clarsimp)
apply (rule_tac x=env'' in exI, rule_tac x=ps'' in exI, simp, rule conjI)
apply (rule step_star_trans, simp+)
apply force
apply (rule step.cases, simp, clarsimp)
apply (case_tac "change_map x", simp+)
apply (erule_tac x=x and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" in allE, 
 clarsimp)
apply (erule_tac x=t in ballE, clarsimp)
apply (rule_tac x=env in exI, rule_tac x=ps in exI, simp)
apply (rule conjI, rule step_star_trans, simp+)
apply (rule_tac x=t in exI, simp+)
done

lemma same_safe [simp]: "\<lbrakk>CFGs t = Some G; Nodes G' = Nodes G\<rbrakk> \<Longrightarrow> safe_points (CFGs(t \<mapsto> G')) = safe_points CFGs"
apply (rule ext, simp add: safe_points_def, rule iffI, clarsimp)
apply (erule_tac x=ta in allE, clarsimp+)
apply force
done

lemma step_along_edge: "\<lbrakk>is_flowgraph G instr_edges; n \<in> Nodes G;
 step_one_thread G n env = (n', change); n' \<noteq> n\<rbrakk> \<Longrightarrow>  \<exists>e. (n, n', e) \<in> Edges G"
apply (simp add: step_one_thread_simps)
(* Start *)
apply (case_tac "n = Start G", auto simp add: flowgraph_def flowgraph_axioms_def)
apply (cut_tac Edges="Edges G" in simple_flowgraph.start_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Exit *)
apply (case_tac "n = Exit G", auto)
apply (case_tac "Label G n", auto)
(* Assign *)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Wait *)
apply (case_tac "eval env expr = 0", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Branchifz *)
apply (case_tac "eval env expr = 0", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_branch_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Branch *)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_branch_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Lock *)
apply (case_tac "env var = 0", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Unlock *)
apply (case_tac "env var = 1", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
done

lemma step_along_edge2: "\<lbrakk>is_flowgraph G instr_edges; n \<in> Nodes G;
 step_one_thread G n env = (n', change); change \<noteq> []\<rbrakk> \<Longrightarrow>  \<exists>e. (n, n', e) \<in> Edges G"
apply (simp add: step_one_thread_simps)
(* Start *)
apply (case_tac "n = Start G", auto simp add: flowgraph_def flowgraph_axioms_def)
apply (cut_tac Edges="Edges G" in simple_flowgraph.start_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Exit *)
apply (case_tac "n = Exit G", auto)
apply (case_tac "Label G n", auto)
(* Assign *)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Wait *)
apply (case_tac "eval env expr = 0", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Branchifz *)
apply (case_tac "eval env expr = 0", auto)
(* Lock *)
apply (case_tac "env var = 0", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* Unlock *)
apply (case_tac "env var = 1", auto)
apply (cut_tac Edges="Edges G" and Start="Start G" and Exit="Exit G" in simple_flowgraph.next_seq_correct, 
 auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
done

locale simple_tCFG = tCFG where 
 instr_edges="instr_edges::(string, string expr) instr \<Rightarrow> (edge_type \<Rightarrow> nat) set" begin

lemma safe_step: "\<lbrakk>safe_points CFGs ps; step CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow>
 safe_points CFGs ps'"
apply (clarsimp simp add: safe_points_def)
apply (erule step.cases, auto)
apply ((erule_tac x=t in allE)+, clarsimp)
apply (erule_tac x=t in ballE, auto)
apply (cut_tac t=t in CFGs, simp, frule step_along_edge, simp+, clarsimp+)
apply (clarsimp simp add: simple_flowgraph_def flowgraph_def, drule pointed_graph.edges_ok, simp+)
done

lemma safe_step_star: "\<lbrakk>safe_points CFGs ps; step_star CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow>
 safe_points CFGs ps'"
apply (drule_tac P="\<lambda>CFGs' C C'. CFGs' = CFGs \<and> safe_points CFGs (snd C) \<longrightarrow> 
 safe_points CFGs (snd C')" in step_star.induct, simp_all, clarsimp)
apply (drule safe_step, simp+)
done

lemma step_increment_path: "\<lbrakk>step CFGs (env, ps) (env', ps'); l \<in> Paths ps'; safe_points CFGs ps\<rbrakk> \<Longrightarrow>
 [ps] \<frown> l \<in> Paths ps"
apply (rule path_incremental_gen, simp, clarsimp)
apply (erule step.cases, clarsimp)
apply (erule_tac x=t in ballE, clarsimp)
apply (rule ccontr, frule CFGs, drule_tac n=n in step_along_edge)
apply (simp add: safe_points_def, erule_tac x=t in allE, simp+)
done

lemma step_star_path_gen: "\<lbrakk>safe_points CFGs ps; step_star CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow>
 \<exists>l\<in>Paths ps. \<exists>i. l i = ps' \<and> 
 (\<forall>j<i. \<exists>env''. step_star CFGs (env, ps) (env'', l j) \<and> step_star CFGs (env'', l j) (env', ps'))"
apply (drule_tac P="\<lambda>CFGs' C C'. CFGs' = CFGs \<and> safe_points CFGs (snd C) \<longrightarrow> 
 (\<exists>l\<in>tCFG.Paths CFGs (snd C). \<exists>i. l i = snd C' \<and> 
 (\<forall>j<i. \<exists>env''. step_star CFGs C (env'', l j) \<and> step_star CFGs (env'', l j) C'))" in step_star.induct, auto)
apply (cut_tac q=b in exists_path, clarsimp, rule_tac x=l in bexI, auto)
apply (rule_tac x=0 in exI, simp)
apply (drule safe_step, simp+)
apply (frule step_increment_path, simp+)
apply (rule_tac x="[b] \<frown> l" in bexI, simp_all)
apply (rule_tac x="Suc i" in exI, clarsimp)
apply (case_tac j, simp+)
apply (rule_tac x=a in exI, simp)
apply (rule step_star_trans, simp+)
apply (erule_tac x=nat in allE, clarsimp)
apply (rule_tac x=env'' in exI, simp)
apply (rule step_star_trans, simp+)
done

lemma step_star_path: "\<lbrakk>safe_points CFGs ps; step_star CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow>
 \<exists>l\<in>Paths ps. \<exists>i. l i = ps'"
by (drule step_star_path_gen, simp+, force)

lemma specify_rpath_step: "\<lbrakk>\<forall>l\<in>RPaths ps. P l; step_star CFGs (env0, start_points CFGs) (env, ps)\<rbrakk> \<Longrightarrow> 
 \<exists>l\<in>RPaths ps. (\<forall>i. \<exists>env'. step_star CFGs (env0, start_points CFGs) (env', l i) \<and> 
 step_star CFGs (env', l i) (env, ps)) \<and> P l"
apply (cut_tac ps="start_points CFGs" in step_star_path_gen, simp+, clarsimp)
apply (drule specify_rpath, simp+, clarsimp)
apply (rule_tac x=l' in bexI, simp_all, clarsimp)
apply (case_tac "ia \<le> i", erule_tac x=ia and P="\<lambda>j. j\<le>i \<longrightarrow> l' j = l (i - j)" in allE, simp)
apply (case_tac "ia = 0", force, simp+)
apply (erule_tac x=i and P="\<lambda>j. j\<le>i \<longrightarrow> l' j = l (i - j)" in allE, simp)
apply (drule_tac j=ia in before_start, simp+, force)
done

lemma specify_rpath_break: "\<lbrakk>\<forall>l\<in>RPaths ps'. P l; step_star CFGs (env0, start_points CFGs) (env, ps);
 step CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow> \<exists>l\<in>RPaths ps'. l 1 = ps \<and> P l"
apply (cut_tac ps="start_points CFGs" in step_star_path_gen, simp+, clarsimp)
apply (frule_tac i=i in reverse_path, clarsimp)
apply (cut_tac q=ps' in rpath_incremental_gen, simp+)
apply (erule step.cases, clarsimp)
apply (erule_tac x=t in ballE, clarsimp)
apply (rule ccontr, frule CFGs, drule_tac n=n in step_along_edge, simp_all)
apply (cut_tac ps="start_points CFGs" in safe_step_star, simp+, simp add: safe_points_def)
apply ((erule_tac x=t in allE)+, simp+)
apply (rule_tac x="[ps'] \<frown> l'" in bexI, simp+)
done

end

(* Later, we should extend this to a program containing these fragments,
   with possibly more code in P and C as well as other threads. *)
fun sample_program where
"sample_program ''P'' = Some \<lparr>Nodes = {0::nat, 1, 2, 3, 4, 5, 6}, 
 Edges = {(0, 1, Seq), (1, 2, Seq), (1, 6, Branch), (2, 3, Seq), (3, 4, Seq), (4, 5, Seq), (5, 1, Branch)},
 Start = 0, Exit = 6, Label = \<lambda>n. if n = 1 then branchifz (Num 1) else if n = 2 then wait (Var ''s'' === Num 0) 
           else if n = 3 then ''y'' \<leftarrow> Var ''x'' else if n = 4 then ''s'' \<leftarrow> Num 1 else branch\<rparr>" |
"sample_program ''C'' = Some \<lparr>Nodes = {7, 8, 9, 10, 11, 12, 13}, 
 Edges = {(7, 8, Seq), (8, 9, Seq), (8, 13, Branch), (9, 10, Seq), (10, 11, Seq), (11, 12, Seq), (12, 8, Branch)},
 Start = 7, Exit = 13, Label = \<lambda>n. if n = 8 then branchifz (Num 1) else if n = 9 then wait (Var ''s'' === Num 1) 
           else if n = 10 then ''z'' \<leftarrow> Var ''z'' +L Var ''y'' else if n = 11 then ''s'' \<leftarrow> Num 0 else branch\<rparr>" |
"sample_program _ = None"

lemma sample [simp]: "\<lbrakk>t \<noteq> ''C''; t \<noteq> ''P''\<rbrakk> \<Longrightarrow> sample_program t = None"
apply (case_tac t, simp)
apply (case_tac list, auto)
apply (case_tac a, simp_all)
apply (case_tac nibble1, simp_all, (case_tac nibble2, simp_all)+)
done

lemma sample_program_E [elim]: "\<lbrakk>P (sample_program ''P''); P (sample_program ''C''); P None\<rbrakk> \<Longrightarrow>
 P (sample_program t)"
by (case_tac "t = ''C''", simp, case_tac "t = ''P''", simp+)

interpretation sample_program: simple_tCFG sample_program
apply (auto simp add: simple_tCFG_def tCFG_def)
apply (subgoal_tac "pointed_graph (Nodes g) (Edges g) (Start g) (Exit g)", auto simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
(* edge types *)
apply (case_tac "t = ''C''", auto simp add: out_edges_def edge_types_def intro!: ext
 split: edge_type.split)
apply (case_tac "t = ''P''", auto simp add: out_edges_def edge_types_def intro!: ext
 split: edge_type.split)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (case_tac "t = ''C''", auto, case_tac "t = ''P''", auto)
apply unfold_locales
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (case_tac "t = ''C''", force, case_tac "t = ''P''", force, simp)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (simp add: in_edges_def)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (simp add: out_edges_def)
apply (case_tac "t = ''C''", clarsimp, case_tac "t = ''P''", auto)
apply (case_tac "t = ''C''", clarsimp, case_tac "t' = ''P''", auto)
apply (case_tac "t = ''P''", clarsimp, case_tac "t' = ''C''", auto)
apply (simp add: dom_def)
apply (rule_tac n=2 and f="\<lambda>n. if n = 0 then ''C'' else ''P''" in nat_seg_image_imp_finite, 
 auto)
apply (rule ccontr, case_tac "x = ''P''", auto)
apply force
done

end
