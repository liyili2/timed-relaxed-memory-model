(* simple_preds.thy *)
(* William Mansky *)
(* Simple predicates on tCFGs and related lemmas, with a particular focus on mutual exclusion. *)

theory simple_preds
imports simple_language trans_semantics
begin

(* This belongs in sequence.  In fact, there's no need for segment. *)
lemma segment_ilist [simp]: "segment i j l = l \<Up> i \<Down> ((j + 1) - i)"
apply (auto simp add: segment_def i_take_def i_drop_def)
apply (rule nth_equalityI, auto)
apply (cut_tac n="Suc j" and i=ia and m=i in nth_map_upt, simp+)
done

(* Some simple state predicates. *)
datatype ('mvar, 'thread, 'node_expr, 'expr, 'instr) pred = 
 Node 'thread 'node_expr | Stmt 'thread 'instr 
 | Conlit 'expr | Varlit 'expr
 | Freevar 'mvar 'instr
 | Is 'mvar 'mvar | SameVal 'expr 'expr
 | Fresh 'expr | OnlyIn 'thread 'expr 

primrec pred_fv where
"pred_fv tfv nfv _ _ (Node t n) = tfv t \<union> nfv n" |
"pred_fv tfv _ _ ifv (Stmt t i) = tfv t \<union> ifv i" |
"pred_fv _ _ efv _ (Conlit e) = efv e" |
"pred_fv _ _ efv _ (Varlit e) = efv e" |
"pred_fv _ _ efv ifv (Freevar x i) = insert x (ifv i)" |
"pred_fv _ _ _ _ (Is x1 x2) = {x1, x2}" |
"pred_fv _ _ efv _ (SameVal e1 e2) = efv e1 \<union> efv e2" |
"pred_fv _ _ efv _ (Fresh e) = efv e" |
"pred_fv tfv _ efv _ (OnlyIn t e) = tfv t \<union> efv e"

abbreviation "simple_pred_fv \<equiv> pred_fv (\<lambda>t. {t}) node_fv (expr_pattern_fv expr_fv) pattern_fv"

lemma simple_pred_fv_finite [simp]: "finite (simple_pred_fv p)"
by (induct p, auto)

corollary simple_cond_fv_finite [simp]: "finite (cond_fv simple_pred_fv \<phi>)"
by simp

(* Functions for evaluating predicates *)
abbreviation "freevar x i \<equiv> x \<in> instr_fv i"
abbreviation "same_val e e' \<equiv> eval (\<lambda>x. undefined) e = eval (\<lambda>x. undefined) e'"

abbreviation "fresh e CFGs \<equiv> case e of Var x \<Rightarrow> \<forall>n \<in> nodes CFGs. x \<notin> instr_fv (label n CFGs)
 | _ \<Rightarrow> False"
abbreviation "only_in t e CFGs \<equiv> case e of Var x \<Rightarrow> 
 \<forall>n \<in> nodes CFGs. x \<in> instr_fv (label n CFGs) \<longrightarrow> thread_of n CFGs = t | _ \<Rightarrow> False"

context simple_tCFG begin

lemma fresh_step: "\<lbrakk>\<forall>n\<in>nodes CFGs. x \<notin> instr_fv (label n CFGs); CFGs t = Some G; 
 p \<in> Nodes G\<rbrakk> \<Longrightarrow> (x, v) \<notin> set (snd (step_one_thread G p env))"
apply (erule_tac x=p in ballE, simp add: label_def thread_of_correct)
apply (frule CFGs, clarsimp simp add: step_one_thread_simps)
apply (case_tac "Label G p", simp_all)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp+)
apply (case_tac "env var = 1", simp+)
apply (simp add: nodes_by_graph)
done

lemma only_step: "\<lbrakk>\<forall>n\<in>nodes CFGs. x \<in> instr_fv (label n CFGs) \<longrightarrow> thread_of n CFGs = t; 
 CFGs t' = Some G; p \<in> Nodes G; t \<noteq> t'\<rbrakk> \<Longrightarrow> 
 (x, v) \<notin> set (snd (step_one_thread G p env))"
apply (erule_tac x=p in ballE, simp add: label_def thread_of_correct)
apply (frule CFGs, clarsimp simp add: step_one_thread_simps)
apply (case_tac "Label G p", simp_all)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp+)
apply (case_tac "env var = 1", simp+)
apply (simp add: nodes_by_graph)
done

lemma fresh_not_in_G: "\<lbrakk>\<forall>n\<in>nodes CFGs. x \<notin> instr_fv (label n CFGs); CFGs t = Some G\<rbrakk> \<Longrightarrow> 
 \<forall>n \<in> Nodes G. x \<notin> instr_fv (Label G n)"
by (clarsimp, erule_tac x=n in ballE, auto simp add: label_correct)

lemma only_not_in_G: "\<lbrakk>\<forall>n\<in>nodes CFGs. x \<in> instr_fv (label n CFGs) \<longrightarrow> thread_of n CFGs = t;
 CFGs t' = Some G; t' \<noteq> t\<rbrakk> \<Longrightarrow> \<forall>n \<in> Nodes G. x \<notin> instr_fv (Label G n)"
by (clarsimp, erule_tac x=n in ballE, auto simp add: label_correct thread_of_correct)

end

primrec eval_pred where
"eval_pred CFGs q \<sigma> (Node t n)= (case (\<sigma> t, node_subst CFGs \<sigma> n) of (OThread t', Some n') \<Rightarrow> 
 q t' = Some n' | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (Stmt t i) = (case (\<sigma> t, subst \<sigma> i) of (OThread t', Some i') \<Rightarrow> 
 \<exists>n G. q t' = Some n \<and> CFGs t' = Some G \<and> n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i' | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (Conlit e) = (case expr_pattern_subst \<sigma> e of Some e' \<Rightarrow> is_const e' | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (Varlit e) = (case expr_pattern_subst \<sigma> e of Some e' \<Rightarrow> is_var e' | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (Freevar x i) = (case (\<sigma> x, subst \<sigma> i) of (OExpr (Var x'), Some i') \<Rightarrow> 
 freevar x' i' | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (Is x1 x2) = (\<sigma> x1 = \<sigma> x2)" |
"eval_pred CFGs q \<sigma> (SameVal e1 e2) = (case (expr_pattern_subst \<sigma> e1, expr_pattern_subst \<sigma> e2) of
 (Some e1', Some e2') \<Rightarrow> same_val e1' e2' | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (Fresh e) = (case expr_pattern_subst \<sigma> e of Some e' \<Rightarrow> 
 fresh e' CFGs | _ \<Rightarrow> False)" |
"eval_pred CFGs q \<sigma> (OnlyIn t e) = (case (\<sigma> t, expr_pattern_subst \<sigma> e) of (OThread t', Some e') \<Rightarrow> 
 only_in t' e' CFGs | _ \<Rightarrow> False)"

(* Helpful derived predicates. *)
abbreviation SCEX ("EX") where "EX t \<phi> \<equiv> let n = SOME y. y \<noteq> t \<and> y \<notin> cond_fv simple_pred_fv \<phi> in
 SCEx n (SCPred (Node t (MVar n)) \<and>sc E SCPred (Node t (MVar n)) \<U> (\<not>sc (SCPred (Node t (MVar n))) \<and>sc \<phi>))"
(* This is wrong.  It might work with weak-until.
abbreviation SCAX ("AX") where "AX t \<phi> \<equiv> let n = SOME y. y \<noteq> t \<and> y \<notin> cond_fv simple_pred_fv \<phi> in
 SCEx n (SCPred (Node t (MVar n)) \<and>sc A SCPred (Node t (MVar n)) \<U> (\<not>sc (SCPred (Node t (MVar n))) \<and>sc \<phi>))"*)
abbreviation SCEP ("EP") where "EP t \<phi> \<equiv> let n = SOME y. y \<noteq> t \<and> y \<notin> cond_fv simple_pred_fv \<phi> in
 SCEx n (SCPred (Node t (MVar n)) \<and>sc E SCPred (Node t (MVar n)) \<B> (\<not>sc (SCPred (Node t (MVar n))) \<and>sc \<phi>))"
abbreviation SCAP ("AP") where "AP t \<phi> \<equiv> let n = SOME y. y \<noteq> t \<and> y \<notin> cond_fv simple_pred_fv \<phi> in
 SCEx n (SCPred (Node t (MVar n)) \<and>sc A SCPred (Node t (MVar n)) \<B> (\<not>sc (SCPred (Node t (MVar n))) \<and>sc \<phi>))"
(* Problem with this: "all paths" includes the paths where t never progresses. 
   Would it make sense to add fairness?  This is static analysis, after all. *)

definition "write t x \<equiv> let e = SOME y. y \<noteq> x \<and> y \<noteq> t in (SCEx e (SCPred (Stmt t (Inj (x \<leftarrow> EPInj (Var e))))) \<or>sc
 SCPred (Stmt t (Inj (lock x))) \<or>sc SCPred (Stmt t (Inj (unlock x))))"
definition "assigns t x \<equiv> let e = SOME y. y \<noteq> x \<and> y \<noteq> t in SCEx e (SCPred (Stmt t (Inj (x \<leftarrow> EPInj (Var e)))))"
definition "write_val t x v \<equiv> let e = SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_pattern_fv expr_fv v in 
 (SCEx e (SCPred (Stmt t (Inj (x \<leftarrow> EPInj (Var e)))) \<and>sc SCPred (SameVal (EPInj (Var e)) v)) \<or>sc
  (SCPred (Stmt t (Inj (lock x))) \<and>sc SCPred (SameVal (EPInj (Num 1)) v)) \<or>sc
  (SCPred (Stmt t (Inj (unlock x))) \<and>sc SCPred (SameVal (EPInj (Num 0)) v)))"
definition "read t x \<equiv> let e = SOME y. y \<noteq> x \<and> y \<noteq> t in let y = SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<noteq> e in
 SCEx y (SCEx e (SCPred (Stmt t (Inj (y \<leftarrow> (e<Var x>)))) \<or>sc SCPred (Stmt t (Inj (branchifz (e<Var x>)))) \<or>sc
 SCPred (Stmt t (Inj (wait (e<Var x>)))) \<or>sc SCPred (Stmt t (Inj (lock x))) \<or>sc SCPred (Stmt t (Inj (unlock x)))))"
definition "only_writes t x v \<equiv> AG (write t x \<longrightarrow>sc write_val t x v)"
definition "not_write_val t x v \<equiv> let v' = SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv v in 
 write t x \<longrightarrow>sc SCEx v' (write_val t x (EPInj (Var v')) \<and>sc \<not>sc (SCPred (SameVal (EPInj v) (EPInj (Var v')))))"
definition "only_writer t x \<equiv> let t' = SOME y. y \<noteq> x \<and> y \<noteq> t in 
 AG (SCAll t' (write t' x \<longrightarrow>sc SCPred (Is t' t)))"
abbreviation "locked t x \<equiv> A \<not>sc (SCPred (Stmt t (Inj (unlock x)))) \<B> 
 SCPred (Stmt t (Inj (lock x)))"
(* A point is in the critical section if all paths to it are locked. *)
definition "in_critical t x \<equiv> AP t (locked t x)"
(* A lock is good if it isn't used as a regular variable, it is only unlocked
   after being locked, and every locked section is critical (i.e., we can't make
   unsafe jumps into locked sections). *)
definition "good_lock t x \<equiv> AG (\<not>sc (assigns t x) \<and>sc 
 (SCPred (Stmt t (Inj (unlock x))) \<longrightarrow>sc in_critical t x) \<and>sc
 ((EP t (locked t x)) \<longrightarrow>sc in_critical t x))"

locale TRANS_simple = TRANS_basics where expr_subst=expr_pattern_subst 
 and subst="subst::(string \<Rightarrow> (string, 'node, string expr, (string, string expr) instr) object) \<Rightarrow> 
((string, (string, string expr) expr_pattern) instr, string) literal \<Rightarrow> (string, string expr) instr option"
 and pred_fv=simple_pred_fv and eval_pred=eval_pred + 
 simple_tCFG where CFGs="CFGs::(string, ('node, (char list, char list expr) instr) flowgraph) map" for CFGs
begin

(* The essence of the write predicate. *)
lemma change_writes: "\<lbrakk>(x, v) \<in> set (snd (step_one_thread G n env)); 
 CFGs t = Some G; q t = Some n; \<sigma> t' = OThread t; \<sigma> x' = OExpr (Var x)\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> q (write t' x')"
apply (frule CFGs, simp add: step_one_thread_simps)
apply (case_tac "n = Start G", simp+, case_tac "n = Exit G", simp+, case_tac "Label G n", simp_all)
apply (clarsimp simp add: write_def Let_def)
apply (rule_tac x="OExpr expr" in exI, clarsimp)
apply (cut_tac x="x' @ t' @ ''a''" and P="\<lambda>y. y \<noteq> x' \<and> y \<noteq> t'" in someI, simp+, clarsimp)
apply (case_tac "eval env expr = 0", simp+)+
apply (clarsimp simp add: write_def Let_def)
apply (case_tac "env var = 0", simp+)
apply (clarsimp simp add: write_def Let_def)
apply (case_tac "env var = 1", simp+)
done

theorem read_same_step: "\<lbrakk>\<forall>x. env x = env' x \<or> 
 \<not>models CFGs (\<sigma>(SOME y. y \<noteq> t := OExpr (Var x))) ps (read t (SOME y. y \<noteq> t)); 
 \<sigma> t = OThread t'; CFGs t' = Some G; ps t' = Some p\<rbrakk> \<Longrightarrow> 
 step_one_thread G p env = step_one_thread G p env'"
apply (frule CFGs, clarsimp simp add: step_one_thread_simps read_def Let_def)
apply (cut_tac A="{SOME y. y \<noteq> t, t}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{SOME y. y \<noteq> t, t, SOME y. y \<noteq> (SOME y. y \<noteq> t) \<and> y \<noteq> t}" in fresh_new, simp+, 
 clarsimp)
apply (cut_tac A="{t}" in fresh_new, simp+)
apply (case_tac "Label G p", simp_all)
apply (rule eval_same, clarsimp, erule_tac x=x in allE, clarsimp)
apply (erule_tac x="OExpr (Var var)" in allE, simp)
apply (frule_tac v'="SOME v'. v' \<notin> expr_fv expr" in sub_out)
apply (cut_tac A="expr_fv expr" in fresh_new, simp+, clarsimp)
apply (erule_tac x="OSynFunc (Var (SOME v'. v' \<notin> expr_fv expr)) e'" in allE, clarsimp)
apply (erule_tac P="case case expr_subst ((\<lambda>y. OExpr (Var y))(SOME v'. v' \<notin> expr_fv expr := 
 OExpr (Var x))) e' of None \<Rightarrow> None | Some e' \<Rightarrow> Some (var \<leftarrow> e') of None \<Rightarrow> False | Some i' \<Rightarrow> 
 \<exists>n G. ps t' = Some n \<and> CFGs t' = Some G \<and> n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i'" in notE)
apply (simp split: option.splits, cut_tac s="expr_subst ((\<lambda>y. OExpr (Var y))
 (SOME v'. v' \<notin> expr_fv expr := OExpr (Var x))) e'" and t=None in trans, erule sym, assumption, simp+)
apply (cut_tac e=expr and env=env and env'=env' in eval_same, clarsimp, erule_tac x=x in allE, clarsimp)
apply (erule_tac x="OExpr (Var var)" in allE, simp)
apply (frule_tac v'="SOME v'. v' \<notin> expr_fv expr" in sub_out)
apply (cut_tac A="expr_fv expr" in fresh_new, simp+, clarsimp)
apply (erule_tac x="OSynFunc (Var (SOME v'. v' \<notin> expr_fv expr)) e'" in allE, clarsimp)
apply (erule_tac P="case case expr_subst ((\<lambda>y. OExpr (Var y))(SOME v'. v' \<notin> expr_fv expr := 
 OExpr (Var x))) e' of None \<Rightarrow> None | Some e' \<Rightarrow> Some (wait e') of None \<Rightarrow> False | Some i' \<Rightarrow> 
 \<exists>n G. ps t' = Some n \<and> CFGs t' = Some G \<and> n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i'" in notE)
apply (simp split: option.splits, cut_tac s="expr_subst ((\<lambda>y. OExpr (Var y))
 (SOME v'. v' \<notin> expr_fv expr := OExpr (Var x))) e'" and t=None in trans, erule sym, assumption, simp+)
apply (cut_tac e=expr and env=env and env'=env' in eval_same, clarsimp, erule_tac x=x in allE, clarsimp)
apply (erule_tac x="OExpr (Var var)" in allE, simp)
apply (frule_tac v'="SOME v'. v' \<notin> expr_fv expr" in sub_out)
apply (cut_tac A="expr_fv expr" in fresh_new, simp+, clarsimp)
apply (erule_tac x="OSynFunc (Var (SOME v'. v' \<notin> expr_fv expr)) e'" in allE, clarsimp)
apply (erule_tac P="case case expr_subst ((\<lambda>y. OExpr (Var y))(SOME v'. v' \<notin> expr_fv expr := 
 OExpr (Var x))) e' of None \<Rightarrow> None | Some e' \<Rightarrow> Some (branchifz e') of None \<Rightarrow> False | Some i' \<Rightarrow> 
 \<exists>n G. ps t' = Some n \<and> CFGs t' = Some G \<and> n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i'" in notE)
apply (simp split: option.splits, cut_tac s="expr_subst ((\<lambda>y. OExpr (Var y))
 (SOME v'. v' \<notin> expr_fv expr := OExpr (Var x))) e'" and t=None in trans, erule sym, assumption, simp+)
apply (erule_tac x=var in allE, clarsimp)+
done

definition "reachable C \<equiv> \<exists>env0. step_star CFGs (env0, start_points CFGs) C"

lemma reachableI [intro]: "step_star CFGs (env0, start_points CFGs) C \<Longrightarrow> reachable C"
by (simp add: reachable_def, force)

lemma reachable_path: "reachable (env, ps) \<Longrightarrow> \<exists>l\<in>Paths (start_points CFGs). \<exists>i. l i = ps"
by (clarsimp simp add: reachable_def, cut_tac step_star_path, simp_all)

lemma reachable_safe: "reachable (env, ps) \<Longrightarrow> safe_points CFGs ps"
by (clarsimp simp add: reachable_def, rule safe_step_star, simp_all)

lemma reachable_step: "\<lbrakk>reachable (env, ps); step CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow> 
 reachable (env', ps')"
apply (clarsimp simp add: reachable_def)
apply (rule_tac x=env0 in exI, rule step_star_trans_gen, simp+)
apply (rule step_star_trans, simp+)
done

lemma reachable_start [simp]: "reachable (env, start_points CFGs)"
by (simp add: reachable_def, rule_tac x=env in exI, simp)

(* Actually, locking is hard without built-in locks.  We could prove the correctness of
   Dekker's or Peterson's Algorithm, or add built-in locks, or just look at a single pass. *)

lemma only_writer_writes: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (only_writer t' x');
 reachable (env, ps); (x, v) \<in> set (snd (step_one_thread G n env)); 
 CFGs t2 = Some G; ps t2 = Some n; \<sigma> t' = OThread t; \<sigma> x' = OExpr (Var x)\<rbrakk> \<Longrightarrow> t2 = t"
apply (frule reachable_path)
apply (clarsimp simp add: only_writer_def Let_def)
apply (erule_tac x=l in ballE, simp_all, erule_tac x=i in allE, erule_tac x="OThread t2" in allE)
apply (cut_tac x="x' @ t' @ ''a''" and P="\<lambda>y. y \<noteq> x' \<and> y \<noteq> t'" in someI, simp+, clarsimp)
apply (erule notE, rule change_writes, simp+)
done

lemma back_along_path: "\<lbrakk>l \<in> Paths (start_points CFGs); models CFGs \<sigma> (l i) (A \<phi> \<B> \<psi>)\<rbrakk> \<Longrightarrow> 
 \<exists>i'\<le>i. models CFGs \<sigma> (l i') \<psi> \<and> (\<forall>j>i'. j \<le> i \<longrightarrow> models CFGs \<sigma> (l j) \<phi>)"
apply clarsimp
apply (frule_tac i=i in reverse_path, clarsimp)
apply (erule_tac x=l' in ballE, simp_all, clarsimp)
apply (case_tac "ia \<le> i", rule_tac x=ia in allE, simp, rule_tac x="i - ia" in exI, clarsimp)
apply ((erule_tac x="i - j" in allE)+, simp)
apply (drule_tac i=i and j=ia in before_start, simp+)
apply (rule_tac x=0 in exI, clarsimp)
apply ((erule_tac x="i - j" in allE)+, simp)
done

lemma start_not_critical [simp]: "\<not>models CFGs \<sigma> (start_points CFGs) (in_critical t x)"
apply (clarify, clarsimp simp add: in_critical_def Let_def)
apply (drule specify_start_rpath, clarsimp)
done

lemma good_lock_stays_critical: "models CFGs \<sigma> ps (good_lock t x) \<Longrightarrow>
 models CFGs \<sigma> ps (AG (in_critical t x \<longrightarrow>sc A in_critical t x \<U> (in_critical t x \<and>sc 
 SCPred (Stmt t (Inj (unlock x))))))"
apply (clarsimp simp add: good_lock_def Let_def)
apply (erule_tac x=l in ballE, simp_all)
apply (rule_tac x=0 in exI, simp)
apply (case_tac "\<sigma> t", simp_all)
oops
(* Would be true with weak until. *)

lemma conj_eqI: "\<lbrakk>P = P'; Q = Q'\<rbrakk> \<Longrightarrow> (P \<and> Q) = (P' \<and> Q')"
by simp

lemma disj_eqI: "\<lbrakk>P = P'; Q = Q'\<rbrakk> \<Longrightarrow> (P \<or> Q) = (P' \<or> Q')"
by simp

lemma imp_eqI: "\<lbrakk>P = P'; Q = Q'\<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q) = (P' \<longrightarrow> Q')"
by simp

lemma ball_eqI: "\<lbrakk>S = S'; P = P'\<rbrakk> \<Longrightarrow> (\<forall>a\<in>S. P a) = (\<forall>a'\<in>S'. P' a')"
by simp

lemma write_same_subst: "\<forall>v\<in>{t,x}. \<sigma> v = \<sigma>' v \<Longrightarrow> 
 models CFGs \<sigma> q (write t x) = models CFGs \<sigma>' q (write t x)"
apply (clarsimp simp add: write_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma>' t", simp_all)
done

lemma write_val_same_subst: "\<forall>v\<in>{t,x} \<union> expr_fv e. \<sigma> v = \<sigma>' v \<Longrightarrow> 
 models CFGs \<sigma> q (write_val t x (EPInj e)) = models CFGs \<sigma>' q (write_val t x (EPInj e))"
apply (clarsimp simp add: write_val_def Let_def)
apply (cut_tac A="{x, t} \<union> expr_fv e" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma>' t", simp_all)
apply (case_tac "\<sigma>' x", simp_all)
apply (case_tac expr, simp_all)
apply (frule expr_same_subst, simp)
apply (rule disj_eqI, rule ex_eqI, case_tac obj, simp_all)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv e := OExpr expra)" and
 \<sigma>'="\<sigma>'(SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv e := OExpr expra)" and e=e in expr_same_subst, simp+)
done

lemma not_write_same_subst: "\<forall>v\<in>{t,x} \<union> expr_fv e. \<sigma> v = \<sigma>' v \<Longrightarrow> 
 models CFGs \<sigma> q (not_write_val t x e) = models CFGs \<sigma>' q (not_write_val t x e)"
apply (clarsimp simp add: not_write_val_def Let_def)
apply (rule imp_eqI, rule write_same_subst, simp+)
apply (cut_tac A="{x, t} \<union> expr_fv e" in fresh_new, simp+, clarsimp)
apply (rule ex_eqI, rule conj_eqI, rule write_val_same_subst, simp+)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv e := obj)" and
 \<sigma>'="\<sigma>'(SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv e := obj)" and e=e in expr_same_subst, simp+)
done

lemma AP_step_gen: "\<lbrakk>models CFGs \<sigma> (lq iq) (AP t (SCPred (Node t n))); \<sigma> t = OThread t'; 
 node_subst CFGs \<sigma> n = Some n'; reachable (env, ps); 
 step CFGs (env, ps) (env', ps'); lq iq t' = ps' t'; lq \<in> Paths (start_points CFGs)\<rbrakk> \<Longrightarrow> 
 ps t' = ps' t' \<or> ps t' = Some n'"
apply (frule reachable_path, clarsimp)
apply (frule_tac i=i and l=l in reverse_path, clarsimp)
apply (cut_tac q=ps' in rpath_incremental_gen, simp+)
apply (erule step.cases, clarsimp)
apply (erule_tac x=ta in ballE, clarsimp)
apply (rule ccontr, frule CFGs, drule_tac n=na in step_along_edge, simp_all)
apply (frule reachable_safe, simp add: safe_points_def)
apply ((erule_tac x=ta in allE)+, simp+)
apply (clarsimp simp add: Let_def)
apply (cut_tac A="insert t (node_fv n)" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (frule_tac l=lq and i=iq in reverse_path, clarsimp)
apply (frule_tac l="[ps'] \<frown> l'" and q'="lq iq" and t=t' in rpath_by_thread, simp+, clarsimp)
apply (erule_tac x=l'b in ballE, simp_all, clarsimp)
apply (cut_tac \<sigma>=\<sigma> and \<sigma>'="\<sigma>(SOME y. y \<noteq> t \<and> y \<notin> node_fv n := ONode node)" and n=n and CFGs=CFGs
 in node_same_subst, simp+)
apply (case_tac "1 < ia", clarsimp)
apply ((erule_tac x=1 in allE)+, simp)
apply (case_tac ia, simp+)
done

lemma AP_step: "\<lbrakk>models CFGs \<sigma> ps' (AP t (SCPred (Node t n))); \<sigma> t = OThread t'; 
 node_subst CFGs \<sigma> n = Some n'; reachable (env, ps); 
 step CFGs (env, ps) (env', ps')\<rbrakk> \<Longrightarrow> ps t' = ps' t' \<or> ps t' = Some n'"
apply (simp add: reachable_def, erule exE)
apply (cut_tac ps="start_points CFGs" and ps'=ps' in step_star_path, simp+)
apply (rule step_star_trans_gen, simp, rule step_star_trans, simp, rule step_star_refl)
apply (erule bexE, erule exE)
apply (rule_tac lq=l and iq=i in AP_step_gen, auto simp add: reachable_def)
done

lemma AP_edge: "\<lbrakk>models CFGs \<sigma> ps' (AP t (SCPred (Node t n))); 
 models CFGs \<sigma> ps' (EP t (SCPred (Node t n))); \<sigma> t = OThread t'; CFGs t' = Some G;
 node_subst CFGs \<sigma> n = Some n'; ps' t' = Some n''\<rbrakk> \<Longrightarrow> \<exists>e. (n', n'', e) \<in> Edges G"
apply (clarsimp simp add: Let_def)
apply (cut_tac A="insert t (node_fv n)" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x=l in ballE, simp_all, clarsimp)
apply (case_tac obja, simp_all)
apply (cut_tac \<sigma>=\<sigma> and \<sigma>'="\<sigma>(SOME y. y \<noteq> t \<and> y \<notin> node_fv n := ONode node)" and n=n and CFGs=CFGs 
 in node_same_subst, simp+)
apply (case_tac i, simp+)
apply (erule_tac x=nat in allE, drule_tac i=nat in RPath_next, simp+)
done

lemma critical_step: "\<lbrakk>models CFGs \<sigma> ps' (in_critical t x); step CFGs (env, ps) (env', ps');
 \<sigma> t = OThread t'; \<sigma> x = OExpr (Var x'); safe_points CFGs ps\<rbrakk> \<Longrightarrow>
 models CFGs \<sigma> ps (in_critical t x) \<or> (\<exists>G n. CFGs t' = Some G \<and> ps t' = Some n \<and> ps' t' \<noteq> Some n \<and> 
 n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = lock x' \<and> env x' = 0)"
apply (clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (erule step.cases, clarsimp)
apply (case_tac "ps t'", clarsimp)
apply (erule_tac x=t' in ballE, simp+)
apply (rule_tac x="ONode a" in exI, clarsimp)
apply (erule_tac x="[ps'] \<frown> l" in ballE, clarsimp)
apply (case_tac "ps t' = ps' t'", clarsimp)
apply (case_tac i, simp+)
apply (rule_tac x=nat in exI, clarsimp)
apply (erule_tac x="Suc j" in allE, simp)
apply (erule_tac x=t' in ballE, clarsimp)
apply (case_tac i, simp+)
apply (case_tac nat, clarsimp)
apply (rule_tac x="LEAST i. l i t' \<noteq> Some a" in exI)
apply (cut_tac P="\<lambda>i. l i t' \<noteq> Some a" in LeastI_ex)
apply (rule ccontr, clarsimp)
apply (erule_tac x=l in ballE, simp+)
apply (frule CFGs)
apply (clarsimp simp add: step_one_thread_simps)
apply simp+
apply (rule conjI, clarsimp)
apply (drule combine_rpaths, simp+)
apply (erule_tac x="l \<Down> (LEAST i. l i t' \<noteq> Some a) \<frown> la" in ballE, simp_all, clarsimp)
apply (case_tac "i < (LEAST i. l i t' \<noteq> Some a)", simp)
apply (drule not_less_Least, simp+)
apply (frule CFGs)
apply (clarsimp simp add: step_one_thread_simps)
apply (rule_tac x="i - (LEAST i. l i t' \<noteq> Some a)" in exI, clarsimp)
apply (erule_tac x="j + (LEAST i. l i t' \<noteq> Some a)" in allE, clarsimp)
apply (clarsimp, drule not_less_Least, simp+)
apply clarsimp
apply (rule_tac x=1 in allE, simp, clarsimp)
apply (drule_tac q=ps' in rpath_incremental_gen, simp_all, clarsimp)
apply (erule_tac x=ta in ballE, clarsimp)
apply (rule ccontr, cut_tac n=n in step_along_edge, simp_all)
apply (cut_tac t=ta in CFGs, simp+)
apply (simp add: safe_points_def, erule_tac x=ta in allE, simp+)
done

lemma in_critical_thread: "models CFGs \<sigma> ps (in_critical t x) \<Longrightarrow> 
 \<exists>t' G. \<sigma> t = OThread t'"
apply (clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma> t", simp_all)
done

lemma in_critical_types_gen: "\<lbrakk>l \<in> Paths (start_points CFGs); models CFGs \<sigma> (l i) (in_critical t x)\<rbrakk> \<Longrightarrow> 
 \<exists>t' G n x'. \<sigma> t = OThread t' \<and> CFGs t' = Some G \<and> l i t' = Some n \<and> \<sigma> x = OExpr (Var x')"
apply (frule in_critical_thread, clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (drule specify_rpath, simp+, clarsimp)
apply (drule_tac i="i - ia" in specify_rpath, simp+)
apply (case_tac "ia \<le> i", (erule_tac x=ia in allE)+, clarsimp)
apply (drule_tac i=i and j=ia in before_start, simp+)
apply clarsimp
apply (case_tac "\<sigma> x", simp_all)
apply (case_tac expr, simp_all, clarsimp)
done

lemma in_critical_types: "\<lbrakk>reachable (env, ps); models CFGs \<sigma> ps (in_critical t x)\<rbrakk> \<Longrightarrow> 
 \<exists>t' G n x'. \<sigma> t = OThread t' \<and> CFGs t' = Some G \<and> ps t' = Some n \<and> \<sigma> x = OExpr (Var x')"
by (drule reachable_path, clarsimp, drule in_critical_types_gen, simp+)

definition "no_critical x \<equiv> let t = SOME y. y \<noteq> x in SCAll t (\<not>sc (in_critical t x))"
definition "one_critical x \<equiv> let t = SOME y. y \<noteq> x in let t' = SOME y. y \<noteq> x \<and> y \<noteq> t in
 SCEx t (in_critical t x \<and>sc SCAll t' (in_critical t' x \<longrightarrow>sc SCPred (Is t t')))"

lemma start_no_critical [simp]: "models CFGs \<sigma> (start_points CFGs) (no_critical x)"
by (simp add: no_critical_def Let_def)

lemma write_cong_gen: "\<lbrakk>\<sigma> t = OThread t1; \<sigma>' t' = OThread t1; \<sigma> x = \<sigma>' x'; CFGs t1 = CFGs' t1; 
 ps t1 = ps' t1\<rbrakk> \<Longrightarrow> models CFGs \<sigma> ps (write t x) = models CFGs' \<sigma>' ps' (write t' x')"
apply (clarsimp simp add: write_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (case_tac "\<sigma>' t'", simp_all)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply auto
apply (erule_tac x=obj in allE)
apply (case_tac obj, simp_all)
apply (erule_tac x=obj in allE)
apply (case_tac obj, simp_all)
done

lemma write_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'\<rbrakk> \<Longrightarrow> models CFGs \<sigma> ps (write t x) =
 models CFGs \<sigma>' ps (write t' x')"
apply (clarsimp simp add: write_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (case_tac "\<sigma>' t'", simp_all)
done

lemma read_cong_gen: "\<lbrakk>\<sigma> t = OThread t1; \<sigma>' t' = OThread t1; \<sigma> x = \<sigma>' x'; CFGs t1 = CFGs' t1; ps t1 = ps' t1\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> ps (read t x) = models CFGs' \<sigma>' ps' (read t' x')"
apply (clarsimp simp add: read_def Let_def)
apply (cut_tac A="{x,t,SOME y. y \<noteq> x \<and> y \<noteq> t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t',SOME y. y \<noteq> x' \<and> y \<noteq> t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (rule ex_eqI)+
apply (rule disj_eqI, case_tac obj, simp_all)
apply (case_tac expr, simp_all)
apply (case_tac obja, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply (rule disj_eqI)
apply (case_tac obja, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply (rule disj_eqI)
apply (case_tac obja, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply (simp split: option.splits)
done

lemma read_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'\<rbrakk> \<Longrightarrow> models CFGs \<sigma> ps (read t x) =
 models CFGs \<sigma>' ps (read t' x')"
apply (clarsimp simp add: read_def Let_def)
apply (cut_tac A="{x,t,SOME y. y \<noteq> x \<and> y \<noteq> t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t',SOME y. y \<noteq> x' \<and> y \<noteq> t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (case_tac "\<sigma>' t'", simp_all)
apply (rule ex_eqI)+
apply (rule disj_eqI, case_tac obj, simp_all)
apply (case_tac expr, simp_all)
apply (case_tac obja, simp_all)
apply (case_tac expr1, simp_all)
apply (case_tac obja, simp_all)
apply (case_tac expr1, simp_all)
done

lemma write_val_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'; expr_subst \<sigma> e = expr_subst \<sigma>' e'\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> ps (write_val t x (EPInj e)) = models CFGs \<sigma>' ps (write_val t' x' (EPInj e'))"
apply (clarsimp simp add: write_val_def Let_def)
apply (cut_tac A="{x,t} \<union> expr_fv e" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'} \<union> expr_fv e'" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (case_tac "\<sigma>' t'", simp_all)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply (rule disj_eqI, rule ex_eqI)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv e := obj)" and \<sigma>'=\<sigma> and e=e 
 in expr_same_subst, simp+)
apply (cut_tac \<sigma>="\<sigma>'(SOME y. y \<noteq> x' \<and> y \<noteq> t' \<and> y \<notin> expr_fv e' := obj)" and \<sigma>'=\<sigma>' and e=e'
 in expr_same_subst, simp+)
apply (case_tac obj, simp_all)
done

lemma not_write_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'; expr_subst \<sigma> e = expr_subst \<sigma>' e'\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> ps (not_write_val t x e) = models CFGs \<sigma>' ps (not_write_val t' x' e')"
apply (clarsimp simp add: not_write_val_def Let_def)
apply (rule imp_eqI, rule write_cong, simp+)
apply (cut_tac A="{x,t} \<union> expr_fv e" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'} \<union> expr_fv e'" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (rule ex_eqI, rule conj_eqI)
apply (rule write_val_cong, simp+)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> x \<and> y \<noteq> t \<and> y \<notin> expr_fv e := obj)" and \<sigma>'=\<sigma> and e=e 
 in expr_same_subst, simp+)
apply (cut_tac \<sigma>="\<sigma>'(SOME y. y \<noteq> x' \<and> y \<noteq> t' \<and> y \<notin> expr_fv e' := obj)" and \<sigma>'=\<sigma>' and e=e'
 in expr_same_subst, simp+)
done

lemma in_critical_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> ps (in_critical t x) = models CFGs \<sigma>' ps (in_critical t' x')"
apply (clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{t, x, t}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{t', x', t'}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma>' t'", simp_all)
done

lemma assigns_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'\<rbrakk> \<Longrightarrow> models CFGs \<sigma> ps (assigns t x) =
 models CFGs \<sigma>' ps (assigns t' x')"
apply (clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (cut_tac A="{x',t'}" in fresh_new, simp+, clarsimp simp add: neq_commute)
apply (case_tac "\<sigma>' t'", simp_all)
done

lemma good_lock_cong: "\<lbrakk>\<sigma> t = \<sigma>' t'; \<sigma> x = \<sigma>' x'\<rbrakk> \<Longrightarrow>
 models CFGs \<sigma> ps (good_lock t x) = models CFGs \<sigma>' ps (good_lock t' x')"
apply (clarsimp simp add: good_lock_def Let_def)
apply (rule ball_eqI, simp, rule ext)
apply (rule all_eqI, rule conj_eqI, simp)
apply (rule assigns_cong, simp+)
apply (rule conj_eqI)
apply (case_tac "\<sigma>' t'", simp_all)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply (rule imp_eqI, simp)
apply (rule in_critical_cong, simp+)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+)
apply (cut_tac A="{t',x',t'}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma>' t'", simp_all)
apply (rule disj_eqI, rule all_eqI)
apply (case_tac obj, simp_all)
apply (rule in_critical_cong, simp+)
done

lemma no_critical: "models CFGs \<sigma> ps (no_critical x) \<Longrightarrow> \<not>models CFGs \<sigma> ps (in_critical t x)"
apply (clarsimp simp add: no_critical_def Let_def)
apply (frule in_critical_thread, clarsimp)
apply (erule_tac x="OThread t'" in allE)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (erule_tac P="models CFGs (\<sigma>(SOME y. y \<noteq> x := OThread t')) ps (in_critical (SOME y. y \<noteq> x) x)" 
 in notE, rule in_critical_cong [THEN subst], simp_all)
done

lemma one_critical: "\<lbrakk>models CFGs \<sigma> ps (one_critical x); models CFGs \<sigma> ps (in_critical t x); 
 models CFGs \<sigma> ps (in_critical t' x)\<rbrakk> \<Longrightarrow> \<sigma> t = \<sigma> t'"
apply (clarsimp simp add: one_critical_def Let_def)
apply (frule in_critical_thread, clarsimp)
apply (frule_tac t=t' in in_critical_thread, clarsimp)
apply (rule_tac x="OThread t'a" in allE, simp, erule_tac x="OThread t'aa" in allE)
apply (cut_tac A="{x, SOME y. y \<noteq> x}" in fresh_new, simp+)
apply (cut_tac A="{x}" in fresh_new, simp+, clarsimp)
apply (erule impE, rule in_critical_cong [THEN subst], simp_all)
apply (erule impE, rule_tac t1=t' in in_critical_cong [THEN subst], simp_all)
done

lemma no_new_locks: "\<lbrakk>env x' \<noteq> 0; step CFGs (env, ps) (env', ps'); models CFGs \<sigma> ps' (in_critical t x);
 \<sigma> x = OExpr (Var x'); safe_points CFGs ps\<rbrakk> \<Longrightarrow> models CFGs \<sigma> ps (in_critical t x)"
apply (frule in_critical_thread, clarsimp)
apply (frule critical_step, simp+)
done

lemma reverse_changes [simp]: "([(x, v)] = changes t) = (changes t = [(x, v)])"
by auto

lemma leave_one_critical: "\<lbrakk>step CFGs (env, ps) (env', ps'); env x' \<noteq> 0; t \<noteq> x;
 reachable (env, ps); models CFGs \<sigma> ps (one_critical x); env' x' = 0; 
 models CFGs \<sigma> (start_points CFGs) (SCAll t (good_lock t x)); \<sigma> x = OExpr (Var x')\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> ps' (no_critical x)"
apply (clarsimp simp add: one_critical_def no_critical_def Let_def)
apply (cut_tac A="{x, SOME y. y \<noteq> x}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (frule_tac ps=ps' in in_critical_thread, clarsimp)
apply (frule critical_step, simp+)
apply (erule reachable_safe)
apply (rule step.cases, simp, clarsimp)
apply (case_tac "change_map x'", simp+)
apply (erule_tac x=x' and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))"
 in allE, clarsimp)
apply (erule_tac x=ta in ballE, clarsimp)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (case_tac "n = Start G", simp+)
apply (case_tac "n = Exit G", simp+)
apply (frule reachable_path, clarsimp)
apply (case_tac "Label G n", simp_all, clarsimp)
apply (erule_tac x="OThread ta" in allE, clarsimp simp add: good_lock_def)
apply (erule_tac x=l in ballE, erule_tac x=i in allE, clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (erule_tac x="OExpr expr" in allE, simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp_all)
apply (case_tac "env var = 1", simp_all, clarsimp)
apply (erule_tac x="OThread ta" in allE, clarsimp simp add: good_lock_def)
apply (erule_tac x=l in ballE, simp_all, erule_tac x=i in allE, clarsimp)
apply (rule_tac x="OThread ta" in allE, simp, erule impE)
apply (rule_tac t1=t in in_critical_cong [THEN subst], simp_all)
apply (clarsimp, erule_tac x="OThread t'" in allE, erule impE)
apply (rule_tac \<sigma>1="\<sigma>(SOME y. y \<noteq> x := OThread t')" in in_critical_cong [THEN subst], simp_all)
apply (thin_tac "models CFGs (\<sigma>(SOME y. y \<noteq> x := OThread t')) (l i) (in_critical (SOME y. y \<noteq> x) x)",
 thin_tac "models CFGs (\<sigma>(t := OThread t')) (l i) (in_critical t x)")
apply (clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{SOME y. y \<noteq> x, x, SOME y. y \<noteq> x}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (clarsimp simp add: reachable_def)
apply (drule specify_rpath_break, simp+, clarsimp)
apply (case_tac "ia > 1", erule_tac x=1 in allE, simp)
apply (frule_tac p=n in simple_flowgraph.next_seq_correct)
apply (cut_tac ps="start_points CFGs" in safe_step_star, simp+, simp add: safe_points_def)
apply ((erule_tac x=t' in allE)+, simp+)
apply (simp add: simple_flowgraph_def, drule_tac u=n in flowgraph.no_loop, simp)
apply (case_tac ia, simp+)
apply (drule specify_rpath_step, simp+, clarsimp)
apply force
done

lemma critical_node_gen: "\<lbrakk>\<sigma> t = OThread t'; l i t' = ps' t'; 
 l \<in> Paths (start_points CFGs); reachable (env', ps')\<rbrakk> \<Longrightarrow>
 models CFGs \<sigma> (l i) (in_critical t x) = models CFGs \<sigma> ps' (in_critical t x)"
apply (clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (rule ex_eqI, case_tac obj, simp_all)
apply (rule conj_eqI, simp+)
apply (rule iffI, clarsimp)
apply (drule_tac i=i in reverse_path, clarsimp)
apply (drule rpath_by_thread, simp+, clarsimp)
apply (erule_tac x=l'a in ballE, simp_all, clarsimp)
apply (rule_tac x=ia in exI, clarsimp)
apply (drule_tac l=l'a and i=ia in rpath_suffix)
apply (drule_tac q="la ia" and l'="l'a \<Up> ia" and t=t' in rpath_by_thread, simp+, clarsimp)
apply (erule_tac x=l'b in ballE, simp_all, clarsimp)
apply (rule_tac x=iaa in exI, case_tac "\<sigma> x", simp_all)
apply (case_tac expr, simp_all)
apply clarsimp
apply (frule reachable_path, clarsimp)
apply (drule_tac l=laa and i=ia in reverse_path, clarsimp)
apply (drule_tac q'="laa ia" and t=t' in rpath_by_thread, simp+, clarsimp)
apply (erule_tac x=l'a in ballE, simp_all, clarsimp)
apply (rule_tac x=iaa in exI, clarsimp)
apply (drule_tac l=l'a and i=iaa in rpath_suffix)
apply (drule_tac q="la iaa" and l'="l'a \<Up> iaa" and t=t' in rpath_by_thread, simp+, clarsimp)
apply (erule_tac x=l'b in ballE, simp_all, clarsimp)
apply (rule_tac x=ib in exI, case_tac "\<sigma> x", simp_all)
apply (case_tac expr, simp_all)
done

lemma critical_node: "\<lbrakk>\<sigma> t = OThread t'; ps t' = ps' t'; reachable (env, ps); reachable (env', ps')\<rbrakk> \<Longrightarrow>
 models CFGs \<sigma> ps (in_critical t x) = models CFGs \<sigma> ps' (in_critical t x)"
apply (frule reachable_path, clarsimp)
apply (rule critical_node_gen, simp+)
done

(* To prove that we don't leave the critical section until we hit an unlock,
   we need to know that we can't make unsafe jumps into what was previously a critical section. *)
lemma step_in_critical: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (good_lock t x);
 reachable (env, ps); step CFGs (env, ps) (env', ps'); models CFGs \<sigma> ps (in_critical t x); 
 \<sigma> t = OThread t'; \<sigma> x = OExpr (Var x'); CFGs t' = Some G; ps t' = Some n; 
 Label G n \<noteq> unlock x' \<or> ps' t' = ps t'\<rbrakk> \<Longrightarrow>
 models CFGs \<sigma> ps' (in_critical t x)"
apply (clarsimp simp add: good_lock_def)
apply (frule reachable_path, clarsimp)
apply (cut_tac q=ps' in exists_path, clarsimp)
apply (frule step_increment_path, simp+)
apply (erule reachable_safe)
apply (frule combine_paths, simp+)
apply (erule_tac x="(l \<Down> i @ [l i]) \<frown> la" in ballE, simp_all)
apply (erule_tac x="i+1" in allE, clarsimp simp add: Let_def)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "ps' t'", erule step.cases, clarsimp)
apply (erule_tac x=t' in ballE, simp+)
apply (erule_tac x="ONode a" in allE, simp)
apply (clarsimp simp add: reachable_def)
apply (drule specify_rpath_break, simp+, clarsimp)
apply (erule_tac x=1 in allE, clarsimp)
apply (erule_tac P="n = a" in disjE, rule critical_node [THEN subst], simp_all)
apply clarsimp
apply (clarsimp simp add: reachable_def, force)
apply (clarsimp simp add: reachable_def, rule_tac x=env0 in exI)
apply (rule step_star_trans_gen, simp, rule step_star_trans, simp, rule step_star_refl)
apply clarsimp
apply (clarsimp simp add: in_critical_def Let_def)
apply (erule_tac x=lc in ballE, simp_all, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x="lc \<Up> ia" in ballE, clarsimp)
apply (erule_tac x="ia + ib" in allE, clarsimp)
apply (erule_tac x=j in allE, case_tac "j < ia", simp+)
apply (erule_tac x="j - ia" in allE, simp)
apply (drule_tac l=lc and i=ia in rpath_suffix, simp) 
done

lemma start_thread_not_critical: "\<lbrakk>CFGs t' = Some G; ps t' = Some (Start G); \<sigma> t = OThread t'; 
 reachable (env, ps)\<rbrakk> \<Longrightarrow> \<not>models CFGs \<sigma> ps (in_critical t x)"
apply (frule_tac ps=ps and ps'="start_points CFGs" in critical_node, simp_all)
apply (simp add: start_points_def)
done

lemma keep_one_critical: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (SCAll t (good_lock t x));
 step CFGs (env, ps) (env', ps'); env x' \<noteq> 0; t \<noteq> x; reachable (env, ps);
 models CFGs \<sigma> ps (one_critical x); env' x' \<noteq> 0; \<sigma> x = OExpr (Var x')\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> ps' (one_critical x)"
apply (clarsimp simp add: one_critical_def Let_def)
apply (cut_tac A="{x, SOME y. y \<noteq> x}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (rule_tac x=obj in exI)
apply (frule in_critical_types, simp+, clarsimp)
apply (case_tac "n = Start G", drule_tac \<sigma>="\<sigma>(SOME y. y \<noteq> x := OThread t')" and t="SOME y. y \<noteq> x" 
 and x=x in start_thread_not_critical, simp_all, simp+)
apply (rule conjI, rule step_in_critical)
apply (erule_tac x="OThread t'" in allE, rule_tac \<sigma>1="\<sigma>(t := OThread t')" and t1=t and x1=x 
 in good_lock_cong [THEN subst], simp+)
apply (erule step.cases, clarsimp)
apply (rule_tac x=t' in ballE, simp, clarsimp)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (case_tac "n = Exit G", simp+)
apply (case_tac "env x' = 1", simp_all)
apply (clarsimp, erule_tac x=x' and P="\<lambda>x. (\<exists>v t. (x, v) \<in> set (changes t)) \<longrightarrow> 
 (\<exists>v'. change_map x = Some v')" in allE)
apply (erule impE, rule_tac x=0 in exI, rule_tac x=t' in exI, simp, clarsimp)
apply (erule_tac x=x' and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, clarsimp)
apply (erule_tac x=ta in ballE, erule_tac x="OThread ta" in allE, clarsimp simp add: good_lock_def)
apply (frule reachable_path, clarsimp)
apply (erule_tac x=l in ballE, simp_all)
apply (erule_tac x=i in allE, clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (frule_tac t=ta in CFGs, simp add: step_one_thread_simps)
apply (case_tac "na = Start Ga", simp+, case_tac "na = Exit Ga", simp+, 
 case_tac "Label Ga na", simp_all)
apply ((erule_tac x="OExpr expr" in allE)+, simp)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp+)
apply (case_tac "env var = 1", simp+)
apply clarsimp
apply (frule_tac ps=ps' in in_critical_thread, clarsimp)
apply (frule_tac ps'=ps' in critical_step, simp+)
apply (erule reachable_safe)
apply (erule_tac x="OThread t'a" in allE, auto)
done

lemma mutex0: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (SCAll t (good_lock t x));
 step_star CFGs (env0, start_points CFGs) (env, ps); \<sigma> x = OExpr (Var x');
 models CFGs \<sigma> ps (in_critical t x); models CFGs \<sigma> ps (in_critical t' x); env0 x' = 0\<rbrakk> \<Longrightarrow> 
 \<sigma> t = \<sigma> t'"
apply (drule_tac P="\<lambda>CFGs' C C'. CFGs' = CFGs \<and> step_star CFGs (env0, start_points CFGs) C \<and> 
 ((fst C x' = 0 \<and> models CFGs \<sigma> (snd C) (no_critical x)) \<or> 
  (fst C x' \<noteq> 0 \<and> models CFGs \<sigma> (snd C) (one_critical x))) \<longrightarrow> 
 ((fst C' x' = 0 \<and> models CFGs \<sigma> (snd C') (no_critical x)) \<or> 
  (fst C' x' \<noteq> 0 \<and> models CFGs \<sigma> (snd C') (one_critical x)))" 
 in step_star.induct, simp_all, clarsimp)
apply (erule impE)
apply (frule in_critical_thread, clarsimp)
apply (rule conjI, rule step_star_trans_gen, simp+)
apply (rule step_star_trans, simp+)
apply (thin_tac "ab x' = 0 \<or> \<not> TRANS_basics.models eval_pred CFGs \<sigma> bb (one_critical x)")
apply (erule disjE, clarsimp)
apply (case_tac "aa x' = 0", clarsimp simp add: no_critical_def Let_def)
apply (frule_tac ps=ba in in_critical_thread, clarsimp)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (frule_tac ps'=ba in critical_step, simp_all)
apply (rule safe_step_star, simp_all)
apply clarsimp
apply (erule step.cases, clarsimp)
apply (rule_tac x=t'aa in ballE, simp, clarsimp)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (clarsimp, erule_tac x=x' and P="\<lambda>x. (\<exists>v t. (x, v) \<in> set (changes t)) \<longrightarrow> 
 (\<exists>v'. change_map x = Some v')" in allE)
apply (erule impE, rule_tac x=1 in exI, rule_tac x="locker x'" in exI, simp, clarsimp)
apply (erule_tac x=x' and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, clarsimp)
apply (erule_tac x=ta in ballE, erule_tac x="OThread ta" in allE, clarsimp simp add: good_lock_def)
apply (cut_tac ps="start_points CFGs" in step_star_path, simp+, clarsimp)
apply (erule_tac x=l in ballE, simp_all)
apply (erule_tac x=i in allE, clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (frule_tac t=ta in CFGs, simp add: step_one_thread_simps)
apply (case_tac "na = Start Ga", simp+, case_tac "na = Exit Ga", simp+, 
 case_tac "Label Ga na", simp_all)
apply (case_tac "x = t", simp+)
apply ((erule_tac x="OExpr expr" in allE)+, simp)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp+)
apply (case_tac "env var = 1", simp+)
apply (rule step.cases, simp, clarsimp)
apply (case_tac "change_map x'", simp+)
apply (erule_tac x=x' and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> 
 (\<exists>t. (x, v) \<in> set (changes t))" in allE, clarsimp)
apply (rule_tac x=ta in ballE, simp, clarsimp)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (case_tac "n = Start G", simp+, case_tac "n = Exit G", simp+,
 case_tac "Label G n", simp_all)
apply (erule_tac x="OThread ta" in allE, clarsimp simp add: good_lock_def)
apply (cut_tac ps="start_points CFGs" in step_star_path, simp+, clarsimp)
apply (erule_tac x=l in ballE, simp_all, erule_tac x=i in allE, clarsimp simp add: assigns_def Let_def)
apply (case_tac "x = t", simp+)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (erule_tac x="OExpr expr" in allE, simp)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp_all)
apply clarsimp
apply (frule_tac p=n in simple_flowgraph.next_seq_correct)
apply (cut_tac ps="start_points CFGs" in safe_step_star, simp+, simp add: safe_points_def)
apply ((erule_tac x=ta in allE)+, simp+)
apply (case_tac "n = simple_flowgraph.next_seq (Edges G) n", simp add: simple_flowgraph_def, 
 drule_tac u=n in flowgraph.no_loop, clarsimp+)
apply (clarsimp simp add: one_critical_def Let_def)
apply (erule_tac x="OThread (locker x')" in allE, erule impE)
apply (erule_tac x="OThread (locker x')" in allE, clarsimp simp add: good_lock_def Let_def)
apply (cut_tac ps="start_points CFGs" in step_star_path, simp+)
apply (cut_tac q=ps' in exists_path, clarsimp)
apply (frule step_increment_path, simp+)
apply (rule safe_step_star, simp_all)
apply (frule combine_paths, simp+)
apply (erule_tac x="(l \<Down> i @ [l i]) \<frown> la" in ballE, simp_all)
apply (erule_tac x="i+1" in allE, clarsimp)
apply (case_tac "x = t", simp+)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (erule disjE, erule_tac x="ONode (simple_flowgraph.next_seq (Edges G) n)" in allE, simp)
apply (drule specify_rpath_break, simp+, clarsimp)
apply (erule_tac x=1 in allE, clarsimp)
apply (erule_tac x=0 in allE, simp)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (cut_tac A="{x, SOME y. y \<noteq> x}" in fresh_new, simp+, clarsimp)
apply (frule_tac ps=ps' in in_critical_thread, clarsimp)
apply (drule_tac ps'=ps' in critical_step, simp+)
apply (rule safe_step_star, simp_all)
apply (erule disjE, clarsimp simp add: no_critical_def Let_def)
apply (erule_tac x="OThread t'aa" in allE)+
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> x := OThread (locker x'), SOME y. y \<noteq> x \<and> y \<noteq> (SOME y. y \<noteq> x) := OThread t'aa)" 
 and \<sigma>'="\<sigma>(SOME y. y \<noteq> x := OThread t'aa)" and t="SOME y. y \<noteq> x \<and> y \<noteq> (SOME y. y \<noteq> x)" and
 t'="SOME y. y \<noteq> x" and x=x and x'=x and ps=psa in in_critical_cong, simp_all)
apply (clarsimp, erule_tac x=t'aa in ballE, clarsimp+)
apply (case_tac "env var = 1", simp+)
apply (cut_tac A="{x, SOME y. y \<noteq> x}" in fresh_new, simp+)
apply (case_tac "aa x' = 0 \<and> TRANS_basics.models eval_pred CFGs \<sigma> ba (no_critical x)", simp+, rule disjI2)
apply (frule reachableI)
apply (clarsimp, case_tac "aa x' = 0", frule_tac x=x and ps=b in leave_one_critical, simp+)
apply (clarsimp, erule_tac x=obj in allE, rule_tac \<sigma>1="\<sigma>(t := obj)" in good_lock_cong [THEN subst], 
 simp_all)
apply clarsimp+
apply (cut_tac x=x and env'=aa in keep_one_critical, simp_all)
apply (clarsimp, erule_tac x=obj in allE, rule_tac \<sigma>1="\<sigma>(t := obj)" in good_lock_cong [THEN subst], 
 simp_all)
apply clarsimp+
apply (frule in_critical_thread, clarsimp)
apply (erule disjE, clarsimp, drule_tac t=t in no_critical, clarsimp+)
apply (frule_tac t=t' in in_critical_thread, clarsimp)
apply (drule_tac t=t and t'=t' in one_critical, simp+)
done

lemma mutex1: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (SCAll t (good_lock t x));
 step_star CFGs (env0, start_points CFGs) (env, ps); \<sigma> x = OExpr (Var x');
 env0 x' \<noteq> 0\<rbrakk> \<Longrightarrow> \<not>models CFGs \<sigma> ps (in_critical t x)"
apply (clarsimp, frule in_critical_thread, clarsimp)
apply (drule_tac P="\<lambda>CFGs' C C'. CFGs' = CFGs \<and> step_star CFGs (env0, start_points CFGs) C \<and> 
 (fst C x' \<noteq> 0 \<and> models CFGs \<sigma> (snd C) (no_critical x)) \<longrightarrow> 
 (fst C' x' \<noteq> 0 \<and> models CFGs \<sigma> (snd C') (no_critical x))" 
 in step_star.induct, simp_all, clarsimp)
apply (erule impE, rule step_star_trans_gen, simp, rule step_star_trans, simp+)
apply (erule disjE)
apply (erule step.cases, clarsimp)
apply (case_tac "change_map x'", simp+)
apply (erule_tac x=x' and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> 
 (\<exists>t. (x, v) \<in> set (changes t))" in allE, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (erule_tac x="OThread ta" in allE)
apply (case_tac "n = Start G", simp+, case_tac "n = Exit G", simp+)
apply (cut_tac ps="start_points CFGs" in step_star_path, simp+, clarsimp)
apply (clarsimp simp add: good_lock_def Let_def)
apply (erule_tac x=l in ballE, simp_all, erule_tac x=i in allE, clarsimp)
apply (case_tac "Label G n", simp_all)
apply (clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "x = t", simp+)
apply (erule_tac x="OExpr expr" in allE, simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "eval env expr = 0", simp+)
apply (case_tac "env var = 0", simp+)
apply (case_tac "x = t", simp+)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "env var = 1", simp_all)
apply (clarsimp simp add: no_critical_def Let_def, erule_tac x="OThread ta" in allE)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (cut_tac \<sigma>="\<sigma>(t := OThread ta)" and \<sigma>'="\<sigma>(SOME y. y \<noteq> x := OThread ta)" and t=t and 
 t'="SOME y. y \<noteq> x" and x=x and x'=x and ps="l i" in in_critical_cong, simp+)
apply (clarsimp simp add: no_critical_def Let_def)
apply (cut_tac A="{x}" in fresh_new, simp+)
apply (drule_tac env=a in no_new_locks, simp+)
apply (rule safe_step_star, simp_all)
apply (clarsimp, frule_tac t=t in no_critical, simp)
done

theorem mutex: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (SCAll t (good_lock t x));
 reachable (env, ps); \<sigma> x = OExpr (Var x');
 models CFGs \<sigma> ps (in_critical t x); models CFGs \<sigma> ps (in_critical t' x)\<rbrakk> \<Longrightarrow> 
 \<sigma> t = \<sigma> t'"
apply (clarsimp simp add: reachable_def)
apply (case_tac "env0 x' = 0", rule mutex0, simp+)
apply (simp add: mutex1)
done

lemma good_lock_threads: "(\<forall>obj. models CFGs (\<sigma>(t := obj)) q (good_lock t x)) = 
 (\<forall>t'\<in>dom CFGs. models CFGs (\<sigma>(t := OThread t')) q (good_lock t x))"
apply auto
apply (clarsimp simp add: good_lock_def Let_def)
apply (cut_tac A="{t}" in fresh_new, simp+)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "x = t", clarsimp simp add: assigns_def Let_def)
apply (case_tac obj, simp_all)
apply (erule_tac x=thread in ballE, simp_all)
apply (simp add: dom_def)
apply (rule disjI1, clarsimp)
apply (drule_tac l=la and i=ia in rpath_suffix, force)
apply (clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x=thread in ballE, simp_all)
apply (simp add: dom_def)
apply (rule conjI, clarsimp)
apply (case_tac "\<sigma> x", simp_all)
apply (case_tac expr, simp_all)
apply (case_tac obja, simp_all)
apply (rule conjI, clarsimp)
apply (case_tac "\<sigma> x", simp_all)
apply (case_tac expr, simp_all)
apply (rule disjI1, clarsimp)
apply (drule_tac l=la and i=ia in rpath_suffix, rule_tac x="la \<Up> ia" in bexI, simp_all, clarsimp)
apply (case_tac "\<sigma> x", simp_all)
apply (case_tac expr, simp_all)
done

lemma in_critical_cong_graphs: "\<lbrakk>\<sigma> t = OThread t1; \<sigma>' t' = OThread t1; CFGs t1 = CFGs' t1;
 \<sigma> x = \<sigma>' x'; simple_tCFG CFGs'; l \<in> Paths (start_points CFGs); \<forall>i. l i t1 = l' i t1;
 l' \<in> tCFG.Paths CFGs' (start_points CFGs')\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> (l i) (in_critical t x) = models CFGs' \<sigma>' (l' i) (in_critical t' x')"
apply (clarsimp simp add: in_critical_def Let_def)
apply (cut_tac A="{t, x, t}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{t', x', t'}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma>' t'", simp_all)
apply (rule ex_cong, clarsimp)
apply (case_tac obj, simp_all)
apply (rule conj_cong, simp+)
apply (rule iffI, clarsimp)
apply (drule_tac i=i in reverse_path, clarsimp)
apply (cut_tac CFGs=CFGs' and CFGs'=CFGs in tCFG.rpath_by_thread_gen, 
 simp add: simple_tCFG_def, simp+)
apply (unfold_locales)
apply simp+
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'aa in ballE, simp_all, clarsimp)
apply (rule_tac x=ia in exI, clarsimp)
apply (frule_tac l=l'aa and i=ia in rpath_suffix)
apply (cut_tac CFGs=CFGs' and CFGs'=CFGs and l=laa and l'="l'aa \<Up> ia" in tCFG.rpath_by_thread_gen, 
 simp add: simple_tCFG_def, simp+)
apply (unfold_locales)
apply simp+
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'b in ballE, simp_all, clarsimp)
apply (rule_tac x=iaa in exI)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply clarsimp
apply (simp add: simple_tCFG_def)
apply (frule_tac i=i in tCFG.reverse_path, simp+, clarsimp)
apply (frule_tac rpath_by_thread_gen, simp+)
apply (rule sym, simp+)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'aa in ballE, simp_all, clarsimp)
apply (rule_tac x=ia in exI, clarsimp)
apply (frule_tac l=l'aa and i=ia in tCFG.rpath_suffix, simp+)
apply (cut_tac l=laa and l'="l'aa \<Up> ia" in rpath_by_thread_gen, simp+)
apply (rule sym, simp+)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'b in ballE, simp_all, clarsimp)
apply (rule_tac x=iaa in exI)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
done

lemma good_lock_cong_graphs: "\<lbrakk>\<sigma> t = OThread t1; \<sigma>' t' = OThread t1; CFGs t1 = CFGs' t1;
 \<sigma> x = \<sigma>' x'; simple_tCFG CFGs'\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> (start_points CFGs) (good_lock t x) = models CFGs' \<sigma>' (start_points CFGs') (good_lock t' x')"
apply (clarsimp simp add: good_lock_def Let_def)
apply (cut_tac A="{t, x, t}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{t', x', t'}" in fresh_new, simp+, clarsimp)
apply (rule iffI, clarsimp)
apply (cut_tac CFGs=CFGs' and CFGs'=CFGs and q="start_points CFGs'" and q'="start_points CFGs" 
 in tCFG.path_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply unfold_locales
apply (simp add: start_points_def)
apply (clarsimp, erule_tac x=l' in ballE, erule_tac x=i in allE, clarsimp)
apply (cut_tac A="{x, t}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{x', t'}" in fresh_new, simp+, clarsimp)
apply (rule conjI, clarsimp simp add: assigns_def Let_def)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply (erule_tac x=obj in allE)
apply (case_tac obj, simp_all)
apply (rule conjI, clarsimp)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply (rule in_critical_cong_graphs [THEN subst], simp_all)
apply clarsimp
apply (cut_tac l=l' and \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and x=x and x'=x' and i=i and l'=l in in_critical_cong_graphs, 
 simp_all)
apply (erule disjE, simp_all)
apply (erule_tac x=obj in allE)
apply (case_tac obj, simp_all)
apply (frule_tac l=l' and i=i in reverse_path, clarsimp)
apply (cut_tac CFGs=CFGs' and CFGs'=CFGs and l=la and q="l i" and q'="l' i" 
 in tCFG.rpath_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply unfold_locales
apply simp
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'b in ballE, clarsimp)
apply (erule_tac x=ia and P="\<lambda>i. la i t1 = Some node \<or> (\<exists>l\<in>RPaths (l'b i).
  \<forall>i. (case case \<sigma>' x' of ONode x \<Rightarrow> empty x | OInstr x \<Rightarrow> empty x | OExpr (Num xa) \<Rightarrow> empty xa 
       | OExpr (Var y) \<Rightarrow> Some (lock y) | OExpr (expr1 +L xa) \<Rightarrow> empty xa 
       | OExpr (expr1 === xa) \<Rightarrow> empty xa | OSynFunc expr1 x \<Rightarrow> empty x | OType x \<Rightarrow> empty x
       | OThread x \<Rightarrow> empty x of None \<Rightarrow> False | Some i' \<Rightarrow> \<exists>n G. l i t1 = Some n \<and> CFGs t1 = Some G \<and> 
 n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i') \<longrightarrow> (\<exists>j<i. case case \<sigma>' x' of ONode x \<Rightarrow> empty x 
 | OInstr x \<Rightarrow> empty x | OExpr (Num xa) \<Rightarrow> empty xa | OExpr (Var y) \<Rightarrow> Some (unlock y) 
 | OExpr (expr1 +L xa) \<Rightarrow> empty xa | OExpr (expr1 === xa) \<Rightarrow> empty xa | OSynFunc expr1 x \<Rightarrow> empty x 
 | OType x \<Rightarrow> empty x | OThread x \<Rightarrow> empty x of None \<Rightarrow> False | Some i' \<Rightarrow> \<exists>n G. l j t1 = Some n \<and> 
 CFGs t1 = Some G \<and> n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i')) \<or>
           (\<exists>j<i. la j t1 \<noteq> Some node)" in allE, clarsimp)
apply (erule disjE, clarsimp)
apply (cut_tac l=la and i=ia in tCFG.rpath_suffix, simp_all)
apply (simp add: simple_tCFG_def)
apply (cut_tac CFGs'=CFGs' and l=lb and q="l'b ia" and q'="la ia" and t=t1 in rpath_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply (simp add: start_points_def)
apply clarsimp
apply (rule_tac x=l'c in bexI, clarsimp)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply clarsimp

apply clarsimp
apply (cut_tac CFGs'=CFGs' and q="start_points CFGs" and q'="start_points CFGs'" and t=t1 
 in path_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply (simp add: start_points_def)
apply (clarsimp, erule_tac x=l' in ballE, erule_tac x=i in allE, clarsimp)
apply (cut_tac A="{x, t}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{x', t'}" in fresh_new, simp+, clarsimp)
apply (rule conjI, clarsimp simp add: assigns_def Let_def)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply (erule_tac x=obj in allE)
apply (case_tac obj, simp_all)
apply (rule conjI, clarsimp)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply (rule TRANS_simple.in_critical_cong_graphs [THEN subst], simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply unfold_locales
apply clarsimp
apply (cut_tac l=l' and \<sigma>=\<sigma>' and \<sigma>'=\<sigma> and x=x' and x'=x and i=i and l'=l in TRANS_simple.in_critical_cong_graphs, 
 simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply unfold_locales
apply (erule disjE, simp_all)
apply (erule_tac x=obj in allE)
apply (case_tac obj, simp_all)
apply (cut_tac l=l' and i=i in tCFG.reverse_path, simp add: simple_tCFG_def, simp, clarsimp)
apply (cut_tac l=la and CFGs'=CFGs' and q="l i" and q'="l' i" and t=t1 in rpath_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'b in ballE, clarsimp)
apply (erule_tac x=ia and P="\<lambda>i. la i t1 = Some node \<or> (\<exists>l\<in>tCFG.RPaths CFGs' (l'b i).
  \<forall>i. (case case \<sigma>' x' of ONode x \<Rightarrow> empty x | OInstr x \<Rightarrow> empty x | OExpr (Num xa) \<Rightarrow> empty xa 
       | OExpr (Var y) \<Rightarrow> Some (lock y) | OExpr (expr1 +L xa) \<Rightarrow> empty xa 
       | OExpr (expr1 === xa) \<Rightarrow> empty xa | OSynFunc expr1 x \<Rightarrow> empty x | OType x \<Rightarrow> empty x
       | OThread x \<Rightarrow> empty x of None \<Rightarrow> False | Some i' \<Rightarrow> \<exists>n G. l i t1 = Some n \<and> CFGs' t1 = Some G \<and> 
 n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i') \<longrightarrow> (\<exists>j<i. case case \<sigma>' x' of ONode x \<Rightarrow> empty x 
 | OInstr x \<Rightarrow> empty x | OExpr (Num xa) \<Rightarrow> empty xa | OExpr (Var y) \<Rightarrow> Some (unlock y) 
 | OExpr (expr1 +L xa) \<Rightarrow> empty xa | OExpr (expr1 === xa) \<Rightarrow> empty xa | OSynFunc expr1 x \<Rightarrow> empty x 
 | OType x \<Rightarrow> empty x | OThread x \<Rightarrow> empty x of None \<Rightarrow> False | Some i' \<Rightarrow> \<exists>n G. l j t1 = Some n \<and> 
 CFGs' t1 = Some G \<and> n \<noteq> Start G \<and> n \<noteq> Exit G \<and> Label G n = i')) \<or>
           (\<exists>j<i. la j t1 \<noteq> Some node)" in allE, clarsimp)
apply (erule disjE, clarsimp)
apply (cut_tac l=la and i=ia in rpath_suffix, simp_all)
apply (cut_tac CFGs'=CFGs and CFGs=CFGs' and l=lb and q="l'b ia" and q'="la ia" and t=t1 
 in tCFG.rpath_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply unfold_locales
apply (simp add: start_points_def)
apply clarsimp
apply (rule_tac x=l'c in bexI, clarsimp)
apply (case_tac "\<sigma>' x'", simp_all)
apply (case_tac expr, simp_all)
apply clarsimp
done

lemma good_lock_wrong_type: "\<forall>t'. \<sigma> t \<noteq> OThread t' \<Longrightarrow> models CFGs \<sigma> q (good_lock t x)"
apply (clarsimp simp add: good_lock_def Let_def)
apply (rule conjI, clarsimp simp add: assigns_def Let_def)
apply (cut_tac A="{x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma> t", simp_all, force)
apply (cut_tac A="{t,x,t}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma> t", simp_all, force)
done

end

end
