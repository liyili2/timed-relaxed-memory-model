(* simple_opt.thy *)
(* William Mansky *)
(* Specification and verification of a simple concurrent transformation. *)

theory simple_opt
imports simple_preds
begin

(* What is program equivalence?  Trace equivalence? 
   With what equivalence relation?  Ignore some vars? 
   Even in single-threaded, we couldn't expect trace equality. 
   Spend some time thinking about this. *)
(* RGTL doesn't belong in specification.  We'll use it to factor the side conditions
   into module-by-module properties.  This will be an interesting problem. 
   For the meantime, we should use CTL. *)

definition "reorder_actions \<equiv> [AReplace (MVar ''n1'') [Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))],
 AReplace (MVar ''n2'') [Inj (''x1'' \<leftarrow> EPInj (Var ''e1''))]]"
(* Do we need the EF?  If the node isn't reachable, it can't affect executions. *)
definition "reorder_sc \<equiv> EF (in_critical ''t'' ''s'' \<and>sc SCPred (Node ''t'' (MVar ''n2'')) \<and>sc
 SCPred (Stmt ''t'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2'')))) \<and>sc 
 AP ''t'' (SCPred (Node ''t'' (MVar ''n1'')) \<and>sc (SCPred (Stmt ''t'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))))) \<and>sc 
 EP ''t'' (SCPred (Node ''t'' (MVar ''n1'')) \<and>sc (SCPred (Stmt ''t'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1''))))))) \<and>sc 
 \<not>sc (SCPred (Freevar ''x1'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc 
 \<not>sc (SCPred (Freevar ''x2'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1''))))) \<and>sc
 SCAll ''t'' (good_lock ''t'' ''s'') \<and>sc 
 SCAll ''t'' (SCAll ''x'' (AG (((SCPred (Freevar ''x'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))) \<or>sc 
 SCPred (Freevar ''x'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc write ''t'' ''x'') \<longrightarrow>sc 
 in_critical ''t'' ''s''))) \<and>sc 
 SCAll ''t'' (AG ((read ''t'' ''x1'' \<or>sc read ''t'' ''x2'') \<longrightarrow>sc in_critical ''t'' ''s''))"
(* We could also consider the version in which there's some space between the two. *)
definition "reorder \<equiv> TIf reorder_actions reorder_sc"

context simple_tCFG begin

lemma default_safe: "\<lbrakk>CFGs t = Some G; n \<in> Nodes G\<rbrakk> \<Longrightarrow> safe_points CFGs (default_state CFGs n)"
apply (clarsimp simp add: safe_points_def default_state_def)
apply (case_tac "ta = thread_of n CFGs", clarsimp)
apply (frule thread_of_correct, simp+)
apply (clarsimp simp add: start_points_def)
apply (drule_tac t=ta in CFGs, clarsimp simp add: simple_flowgraph_def flowgraph_def, 
 erule pointed_graph.has_start)
done

lemma default_safe2: "n \<in> nodes CFGs \<Longrightarrow> safe_points CFGs (default_state CFGs n)"
by (clarsimp simp add: nodes_def ran_def default_safe)

lemma same_thread [simp]: "\<lbrakk>CFGs t = Some G; n \<in> Nodes G; n' \<in> Nodes G;  Nodes G' = Nodes G\<rbrakk> \<Longrightarrow> 
 thread_of n' (CFGs(thread_of n CFGs \<mapsto> G')) = thread_of n CFGs"
apply (frule thread_of_correct, simp+)
apply (auto simp add: thread_of_def)
apply (rule the_equality, auto)
apply (rule ccontr, frule_tac t="(THE t. \<exists>g. CFGs t = Some g \<and> n \<in> Nodes g)" and t'=t in disjoint, simp+)
apply blast
done

end

context TRANS_simple begin

lemma new_node_graph: "CFGs t = Some G \<Longrightarrow>  (SOME x. x \<notin> nodes CFGs) \<notin> Nodes G"
apply (cut_tac nodes_finite)
apply (cut_tac A="nodes CFGs" in fresh_new, auto)
done

(* If the transformation can be applied, the valuation gives things the right types
   and the side condition holds. *)
lemma reorder_vals: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs;
 side_cond_sf reorder_sc \<sigma> CFGs; part_matches \<sigma> \<tau>\<rbrakk> \<Longrightarrow>
 \<exists>G t. \<sigma> ''t'' = OThread t \<and> CFGs t = Some G \<and>
 (\<exists>n1\<in>Nodes G. \<sigma> ''n1'' = ONode n1 \<and> n1 \<noteq> Start G \<and> n1 \<noteq> Exit G \<and> 
 (\<exists>x1 e1. \<sigma> ''x1'' = OExpr (Var x1) \<and> \<sigma> ''e1'' = OExpr e1 \<and> Label G n1 = x1 \<leftarrow> e1 \<and> 
 (\<exists>n2\<in>Nodes G. \<sigma> ''n2'' = ONode n2 \<and> n2 \<noteq> Start G \<and> n2 \<noteq> Exit G \<and> 
  n1 \<noteq> n2 \<and> out_edges (Edges G) n1 = {(n2, Seq)} \<and>
 (\<exists>x2 e2. \<sigma> ''x2'' = OExpr (Var x2) \<and> \<sigma> ''e2'' = OExpr e2 \<and> Label G n2 = x2 \<leftarrow> e2 \<and>
  CFGs' = CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>) \<and> 
 x1 \<noteq> x2 \<and> x1 \<notin> expr_fv e2 \<and> x2 \<notin> expr_fv e1 \<and>
 (\<exists>l\<in>Paths (start_points CFGs). \<exists>i. l i t = Some n2 \<and> models CFGs \<sigma> (l i) (in_critical ''t'' ''s'')) \<and> 
  models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (good_lock ''t'' ''s'')) \<and>
  models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (SCAll ''x'' (AG (((SCPred (Freevar ''x'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))) \<or>sc 
 SCPred (Freevar ''x'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc write ''t'' ''x'') \<longrightarrow>sc 
 in_critical ''t'' ''s'')))) \<and>
 models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (AG ((read ''t'' ''x1'' \<or>sc read ''t'' ''x2'') \<longrightarrow>sc 
 in_critical ''t'' ''s'')))))))"
apply (clarsimp simp add: reorder_sc_def)
apply (case_tac "\<sigma> ''t''", simp_all)
apply (case_tac "\<sigma> ''n2''", simp_all)
apply (case_tac "\<sigma> ''x2''", simp_all)
apply (case_tac expr, simp_all)
apply (case_tac "\<sigma> ''e2''", simp_all, clarsimp)
apply (frule_tac i=i in Path_safe, simp, simp add: safe_points_def)
apply (erule_tac x=thread in allE, simp)
apply (frule thread_of_correct, simp+)
apply (clarsimp simp add: Let_def)
apply (cut_tac A="{''t'', ''x1'', ''e1'', ''t'', ''n1'', ''t''}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (case_tac "\<sigma> ''n1''", simp_all)
apply (case_tac "\<sigma> ''x1''", simp_all)
apply (case_tac expr, simp_all)
apply (case_tac "\<sigma> ''e1''", simp_all)
apply (clarsimp simp add: reorder_actions_def action_list_sf_def)
apply (case_tac "nodeb \<notin> nodes CFGs", simp+)
apply (frule default_safe2)
apply (case_tac obja, simp_all)
apply (frule_tac i=ia in RPath_safe, erule Path_safe, simp+)
apply (simp add: safe_points_def, (erule_tac x="thread_of node CFGs" in allE)+, simp)
apply (case_tac ia, simp+)
apply (erule_tac x=nat in allE, simp)
apply (drule_tac i=nat in RPath_next, simp+, clarsimp)
apply (frule CFGs, simp add: default_state_def)
apply (frule_tac n=nodeb in thread_of_correct, simp+)
apply (case_tac "node \<notin> nodes CFGs", simp+)
apply (simp add: simple_flowgraph_def, frule_tac u=nodeb in flowgraph.instr_edges_ok, simp+)
apply (cut_tac e="out_edges (Edges G) nodeb" in unique_seq)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.finite_out_edges)
apply (clarsimp simp add: out_edges_def)
apply (rule conjI)
apply (subgoal_tac "(node, e) \<in> {(u, t). (nodeb, u, t) \<in> Edges G}", simp, blast)
apply (rule_tac x=l in bexI, rule_tac x=i in exI, simp+)
done

lemma reorder_semantics: "CFGs' \<in> trans_sf reorder \<tau> CFGs \<Longrightarrow>
 \<exists>\<sigma>. part_matches \<sigma> \<tau> \<and> (\<exists>G t. \<sigma> ''t'' = OThread t \<and> CFGs t = Some G \<and>
 (\<exists>n1\<in>Nodes G. \<sigma> ''n1'' = ONode n1 \<and> n1 \<noteq> Start G \<and> n1 \<noteq> Exit G \<and> 
 (\<exists>x1 e1. \<sigma> ''x1'' = OExpr (Var x1) \<and> \<sigma> ''e1'' = OExpr e1 \<and> Label G n1 = x1 \<leftarrow> e1 \<and> 
 (\<exists>n2\<in>Nodes G. \<sigma> ''n2'' = ONode n2 \<and> n2 \<noteq> Start G \<and> n2 \<noteq> Exit G \<and> 
  n1 \<noteq> n2 \<and> out_edges (Edges G) n1 = {(n2, Seq)} \<and>
 (\<exists>x2 e2. \<sigma> ''x2'' = OExpr (Var x2) \<and> \<sigma> ''e2'' = OExpr e2 \<and> Label G n2 = x2 \<leftarrow> e2 \<and>
  CFGs' = CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>) \<and>  
 x1 \<noteq> x2 \<and> x1 \<notin> expr_fv e2 \<and> x2 \<notin> expr_fv e1 \<and>
 (\<exists>l\<in>Paths (start_points CFGs). \<exists>i. l i t = Some n2 \<and> models CFGs \<sigma> (l i) (in_critical ''t'' ''s'')) \<and> 
  models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (good_lock ''t'' ''s'')) \<and>
  models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (SCAll ''x'' (AG (((SCPred (Freevar ''x'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))) \<or>sc 
 SCPred (Freevar ''x'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc write ''t'' ''x'') \<longrightarrow>sc 
 in_critical ''t'' ''s'')))) \<and>
 models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (AG ((read ''t'' ''x1'' \<or>sc read ''t'' ''x2'') \<longrightarrow>sc 
 in_critical ''t'' ''s''))))))))"
apply (clarsimp simp add: reorder_def, drule reorder_vals, simp+, clarsimp)
apply (rule_tac x=\<sigma> in exI, clarsimp)
apply (rule_tac x=l in bexI, rule_tac x=i in exI, simp+)
done

lemma reorder_preserves_tCFGs: "CFGs' \<in> trans_sf reorder \<tau> CFGs \<Longrightarrow> simple_tCFG CFGs'"
apply (drule reorder_semantics, simp, clarsimp)
apply (frule CFGs)
apply (unfold_locales, simp_all)
apply (case_tac "ta = t", clarsimp)
apply (clarsimp simp add: simple_flowgraph_def flowgraph_def flowgraph_axioms_def)
apply (cut_tac e="{(n2, Seq)}" in unique_seq, simp+)
apply (erule_tac x=n2 in allE, simp+)
apply (frule_tac t=ta in CFGs, simp+)
apply (case_tac "CFGs ta", simp split: if_splits)
apply (case_tac "CFGs t'", simp split: if_splits)
apply (cut_tac t=ta and t'=t' in disjoint, simp+)
apply (clarsimp split: if_splits)
done

(* Finally, the transformation preserves semantics. *)
theorem mfc_preserves_semantics: "\<lbrakk>simple_tCFG CFGs; CFGs' \<in> trans_sf move_from_critical \<tau> CFGs\<rbrakk> \<Longrightarrow>
 RGSim_code CFGs' CFGs"
oops

end

definition "final Gs ps \<equiv> \<forall>t G. Gs t = Some G \<longrightarrow> ps t = Some (Exit G)"

thm step_star.induct

definition "simulates CFGs1 CFGs2 sim_rel \<equiv> \<lambda>graph C C'. \<forall>env. graph=CFGs1 \<and> 
 TRANS_simple.reachable CFGs1 C \<and> TRANS_simple.reachable CFGs2 (env, snd C) \<and> sim_rel (snd C) (fst C) env \<longrightarrow> 
 (\<exists>env'. step_star CFGs2 (env, snd C) (env', snd C') \<and> sim_rel (snd C') (fst C') env')"

definition "reorder_sim_rel t n2 x1 e1 x2 e2 ps env env' \<equiv> if ps t = Some n2 then
 env x2 = eval env' e2 \<and> env' x1 = eval env e1 \<and> (\<forall>x. x = x1 \<or> x = x2 \<or> env x = env' x)
 else env = env'"

definition "reorder_sim_rel_rev t n2 x1 e1 x2 e2 ps env env' \<equiv> 
 reorder_sim_rel t n2 x1 e1 x2 e2 ps env' env"
declare reorder_sim_rel_rev_def [simp]

lemma reorder_step_out: "\<lbrakk>is_flowgraph G instr_edges; 
 is_flowgraph (G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>) instr_edges; n \<noteq> n1; n \<noteq> n2\<rbrakk> \<Longrightarrow>
 simple_flowgraph.step_one_thread (Edges G) (Start G) (Exit G) ((Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)) n env = 
 step_one_thread G n env"
by (simp add: step_one_thread_simps)

context TRANS_simple begin

lemma next_seq_out [simp]: "\<lbrakk>simple_flowgraph N1 E1 s1 x1 L1; simple_flowgraph N2 (rep_edges E1 ll) s2 x2 L2; ps t \<notin> set ll\<rbrakk> \<Longrightarrow> 
 simple_flowgraph.next_seq E1 (ps t) = simple_flowgraph.next_seq (rep_edges E1 ll) (ps t)"
by (simp add: simple_flowgraph.next_seq_def)

lemma next_branch_out [simp]: "\<lbrakk>simple_flowgraph N1 E1 s1 x1 L1; simple_flowgraph N2 (rep_edges E1 ll) s2 x2 L2; ps t \<notin> set ll\<rbrakk> \<Longrightarrow> 
 simple_flowgraph.next_branch E1 (ps t) = simple_flowgraph.next_branch (rep_edges E1 ll) (ps t)"
by (simp add: simple_flowgraph.next_branch_def)

lemma reorder_preserves_final: "\<lbrakk>CFGs' \<in> trans_sf reorder \<tau> CFGs; final CFGs ps\<rbrakk> \<Longrightarrow> final CFGs' ps"
apply (drule reorder_semantics, simp, clarsimp simp add: final_def)
apply (case_tac "ta = t", auto)
done

lemma reorder_critical: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs;
 side_cond_sf reorder_sc \<sigma> CFGs; part_matches \<sigma> \<tau>; \<sigma> ''n1'' = ONode n1; reachable (env, ps); 
 ps t = Some n1; \<sigma> ''t'' = OThread t\<rbrakk> \<Longrightarrow>
 models CFGs \<sigma> ps (in_critical ''t'' ''s'')"
apply (frule reorder_vals, simp+, clarsimp)
apply (erule_tac x="OThread t" in allE, erule_tac x="OExpr (Var x1)" in allE, simp)
apply (cut_tac n=n1 and q=ps and \<sigma>="\<sigma>(''t'' := OThread t, ''x'' := OExpr (Var x1))" and t'="''t''" 
 and x'="''x''" in change_writes, simp_all)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (drule reachable_path, clarsimp)
apply (erule_tac x=la in ballE, erule_tac x=ia in allE, simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
done

lemma writes_critical: "\<lbrakk>models CFGs \<sigma> (start_points CFGs) (SCAll ''t'' (SCAll ''x'' 
 (AG (((SCPred (Freevar ''x'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))) \<or>sc 
 SCPred (Freevar ''x'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc write ''t'' ''x'') \<longrightarrow>sc 
 in_critical ''t'' ''s'')))); (x, v) \<in> set (snd (step_one_thread G n env)); 
 subst \<sigma> (Inj (''x1'' \<leftarrow> EPInj (Var ''e1''))) = Some i1; 
 subst \<sigma> (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))) = Some i2; ps t = Some n;
 x \<in> instr_fv i1 \<or> x \<in> instr_fv i2; CFGs t = Some G; reachable (env', ps)\<rbrakk> \<Longrightarrow>
 models CFGs (\<sigma>(''t'' := OThread t)) ps (in_critical ''t'' ''s'')"
apply clarsimp
apply (erule_tac x="OThread t" in allE, erule_tac x="OExpr (Var x)" in allE, simp)
apply (frule reachable_path, clarsimp)
apply (erule_tac x=l in ballE, simp_all, erule_tac x=i in allE)
apply (erule impE, rule change_writes, simp+)
apply (erule_tac P="x \<notin> instr_fv i1 \<and> x \<notin> instr_fv i2" in disjE, simp)
apply (rule in_critical_cong [THEN subst], simp_all)
done

lemma reorder_start [simp]: "CFGs t = Some G \<Longrightarrow> 
 start_points (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>)) = start_points CFGs"
by (rule ext, simp add: start_points_def)

lemma reorder_simulates_step1: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs; part_matches \<sigma> \<tau>;
 side_cond_sf reorder_sc \<sigma> CFGs; \<sigma> ''t'' = OThread t; \<sigma> ''n2'' = ONode n2; \<sigma> ''x1'' = OExpr (Var x1); 
 \<sigma> ''e1'' = OExpr e1; \<sigma> ''x2'' = OExpr (Var x2); \<sigma> ''e2'' = OExpr e2; step CFGs' (enva, ps) (envb, ps');
 TRANS_simple.reachable CFGs' (enva, ps); reachable (env, ps);
 reorder_sim_rel t n2 x1 e1 x2 e2 ps enva env\<rbrakk> \<Longrightarrow>
 \<exists>env'. step CFGs (env, ps) (env', ps') \<and> reorder_sim_rel t n2 x1 e1 x2 e2 ps' envb env'"
apply (subgoal_tac "CFGs' \<in> trans_sf reorder \<tau> CFGs")
apply (frule reorder_preserves_tCFGs)
apply (frule reorder_vals, simp+, clarsimp)
apply (subgoal_tac "TRANS_simple (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>))")
apply (clarsimp simp add: reorder_sim_rel_def)
apply (frule TRANS_simple.reachable_step, simp+)
apply (frule in_critical_types_gen, simp+, clarsimp)
apply (erule step.cases, clarsimp)
apply (case_tac "t \<notin> ts")
apply (rule_tac x="update_map env change_map" in exI, clarsimp)
apply (subgoal_tac "step CFGs (env, ps) (update_map env change_map, ps')", clarsimp)
apply (subgoal_tac "\<forall>x\<in>(instr_fv (x1 \<leftarrow> e1) \<union> instr_fv (x2 \<leftarrow> e2)). change_map x = None", clarsimp)
apply (rule conjI, rule eval_same, simp)+
apply (clarsimp, (erule_tac x=x in allE)+, simp)
apply (clarify, rule ccontr)
apply (erule_tac x=x and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" in allE,
 clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", simp+)
apply (cut_tac x=x and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply clarsimp
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac changes=changes and change_map=change_map and ts=ts and locker=locker in step, clarsimp+)
apply (case_tac "ta = t", simp+)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ps t = Some n2", simp_all)
apply (rule trans, rule_tac ps=ps and \<sigma>="\<sigma>(''t'' := OThread ta)" and t="''t''" in read_same_step, 
 simp_all, clarsimp)
apply (frule reachable_path, clarsimp)
apply (erule_tac x="OThread ta" in allE, erule_tac x=la in ballE, simp_all, 
 erule_tac x=ia in allE)
apply (erule disjE, clarsimp)
apply (cut_tac A="{''t''}" in fresh_new, simp+)
apply ((erule_tac x=x in allE)+, simp, erule disjE, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x1))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x1''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x2))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x2''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
(* Now, the case in which we actually use the changed thread. *)
apply (rule_tac x=t in ballE, simp, clarsimp)
apply (case_tac "n = n1", clarsimp)
apply (simp add: simple_tCFG_def, frule_tac t=t in tCFG.CFGs, simp+, simp add: step_one_thread_simps)
apply (clarsimp, frule simple_flowgraph.next_seq_correct, simp+)
apply (case_tac "simple_flowgraph.next_seq (Edges G) n1 \<noteq> n2", simp add: out_edges_def)
apply (subgoal_tac "(simple_flowgraph.next_seq (Edges G) n1, Seq) \<in> {(u, t). (n1, u, t) \<in> Edges G}", 
 simp, blast)
apply clarsimp
apply (rule_tac x=x2 and P="\<lambda>x. (\<exists>v t. (x, v) \<in> set (changes t)) \<longrightarrow> (\<exists>v'. change_map x = Some v')" 
 in allE, simp, erule impE, rule_tac x="eval env e2" in exI, rule_tac x=t in exI, simp, clarsimp)
apply (rule_tac x=x2 and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, simp, erule_tac x=v' in allE, clarify)
apply (cut_tac CFGs'="CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, 
 simple_flowgraph.next_seq (Edges G) n1 := x1 \<leftarrow> e1)\<rparr>)" and \<sigma>=\<sigma> and ps=ps in reorder_critical, simp_all)
apply (case_tac "ta \<noteq> t")
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (erule_tac x=ta in ballE, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x2))" and t'="''t''" and x'="''x''" and
 G=Ga and n=n and env=env and q=ps in change_writes, simp_all)
apply (drule reachable_path, clarsimp)
apply (thin_tac "\<forall>obj. \<forall>l\<in>Paths (start_points CFGs).
 \<forall>i. \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x1'') \<and>
     \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x2'') \<or>
       TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (in_critical ''t'' ''s'')")
apply (erule_tac x="OThread ta" in allE, erule_tac x="OExpr (Var x2)" in allE, 
 erule_tac x=la in ballE, erule_tac x=ia in allE, simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x2))" 
 in in_critical_cong [THEN subst], simp_all)
(* The assignment to x2 recorded was the one we moved. *)
apply (rule_tac x="((update_map env change_map)(x2 := env x2))(x1 := eval env e1)" in exI, clarsimp)
apply (rule conjI, rule_tac ts=ts and changes="changes(t := [(x1, eval env e1)])" and locker=locker 
 and change_map="(change_map(x1 \<mapsto> eval env e1))(x2 := None)" in step, simp_all, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta \<noteq> t", simp+)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (clarsimp, rule conjI, force, clarsimp)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (rule_tac x=ta in exI, case_tac "ta = t", simp+)
apply (clarsimp, rule conjI, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x2))" and t'="''t''" and x'="''x''" and
 n=n and env=env and q=ps in change_writes, simp_all)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (drule reachable_path, clarsimp)
apply (thin_tac "\<forall>obj. \<forall>l\<in>Paths (start_points CFGs).
 \<forall>i. \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x1'') \<and>
     \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x2'') \<or>
       TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (in_critical ''t'' ''s'')")
apply (erule_tac x="OThread ta" in allE, erule_tac x="OExpr (Var x2)" in allE, 
 erule_tac x=la in ballE, erule_tac x=ia in allE, simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x2))" 
 in in_critical_cong [THEN subst], simp_all)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (simp add: update_map_def, rule ext, simp)
apply (subgoal_tac "\<forall>x\<in>(expr_fv e1 \<union> expr_fv e2 - {x2}). change_map x = None")
apply (rule conjI, rule eval_same, simp)
apply (rule eval_same, clarsimp, erule_tac x=x in ballE, simp+)
apply (clarify, rule ccontr)
apply (erule_tac x=x and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" in allE,
 clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", clarsimp+)
apply (cut_tac x=x and G=Ga and n=n and env=env and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply (case_tac "n = n2", clarsimp)
(* The second changed node. *)
apply (simp add: simple_tCFG_def, frule_tac t=t in tCFG.CFGs, simp+, simp add: step_one_thread_simps)
apply (clarsimp, frule_tac p=n2 in simple_flowgraph.next_seq_correct, simp+)
apply (simp add: simple_flowgraph_def, drule_tac u=n2 in flowgraph.no_loop)
apply (case_tac "simple_flowgraph.next_seq (Edges G) n2 = n2", simp+)
apply (rule_tac ts=ts and changes="changes(t := [(x2, enva x2)])" and 
 change_map="(change_map(x1 := None))(x2 \<mapsto> enva x2)" and locker=locker in step, clarsimp)
apply (rule conjI, clarsimp)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (rule trans, rule_tac ps=ps and \<sigma>="\<sigma>(''t'' := OThread ta)" and t="''t''" in read_same_step, 
 simp_all, clarsimp)
apply (frule reachable_path, clarsimp)
apply (erule_tac x="OThread ta" in allE, erule_tac x=la in ballE, simp_all, 
 erule_tac x=ia in allE)
apply (erule disjE, clarsimp)
apply (cut_tac A="{''t''}" in fresh_new, simp+)
apply ((erule_tac x=x in allE)+, simp, erule disjE, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x1))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x1''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x2))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x2''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (clarsimp, rule conjI, force, clarsimp)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (rule_tac x=ta in exI, case_tac "ta = t", simp+)
apply (clarsimp, rule conjI, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x1))" and t'="''t''" and x'="''x''" and
 n=n and env=enva and q=ps in change_writes, simp_all)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (cut_tac x=x1 and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (rule ext, case_tac "x = x1", simp)
apply (erule_tac x=x1 and P="\<lambda>x. (\<exists>v t. (x, v) \<in> set (changes t)) \<longrightarrow> (\<exists>v'. change_map x = Some v')" 
 in allE, erule impE, rule_tac x="eval enva e1" in exI, rule_tac x=t in exI, simp, clarsimp)
apply (erule_tac x=x1 and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", clarsimp+)
apply (cut_tac x=x1 and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply (case_tac "x = x2", clarsimp)
apply (case_tac "change_map x2", simp, clarsimp)
apply (erule_tac x=x2 and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, clarsimp)
apply (case_tac "ta = t", simp+)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (cut_tac x=x2 and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply ((erule_tac x=x in allE)+, case_tac "change_map x", simp+)
(* The case in which we don't use the changed nodes. *)
apply (rule_tac x="update_map env change_map" in exI, simp)
apply (subgoal_tac "step CFGs (env, ps) (update_map env change_map, ps')", simp)
apply (clarsimp simp add: reorder_sc_def Let_def)
apply (cut_tac A="{''t'',''n1'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''t'',''x1'',''e1'',''t'',''n1'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac ps=ps and \<sigma>=\<sigma> and lq=la and iq=ia and n="MVar ''n1''" and ps'=ps' in AP_step_gen, simp_all)
apply (simp add: Let_def)
apply (rule_tac x="ONode n2" in exI, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x=lc in ballE, simp_all, clarsimp)
apply (rule_tac x=ic in exI, simp)
apply (rule_tac changes=changes and change_map=change_map and ts=ts and locker=locker
 in step, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", clarsimp)
apply (rule reorder_step_out [THEN subst], simp_all)
apply (drule CFGs, simp+)
apply (simp add: simple_tCFG_def, drule_tac t=t in tCFG.CFGs, simp+)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply (simp add: reorder_def)
apply force
done

theorem reorder_simulates1: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs; part_matches \<sigma> \<tau>;
 side_cond_sf reorder_sc \<sigma> CFGs; step_star CFGs' (env0, start_points CFGs) (env, ps); 
 \<sigma> ''t'' = OThread t; \<sigma> ''n2'' = ONode n2; \<sigma> ''x1'' = OExpr (Var x1); \<sigma> ''e1'' = OExpr e1;
 \<sigma> ''x2'' = OExpr (Var x2); \<sigma> ''e2'' = OExpr e2\<rbrakk> \<Longrightarrow>
 \<exists>env'. reorder_sim_rel t n2 x1 e1 x2 e2 ps env env' \<and> 
        step_star CFGs (env0, start_points CFGs) (env', ps)"
apply (subgoal_tac "CFGs' \<in> trans_sf reorder \<tau> CFGs")
apply (frule reorder_preserves_tCFGs)
apply (frule reorder_vals, simp+, clarsimp)
apply (subgoal_tac "TRANS_simple (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>))")

apply (drule_tac P="simulates (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>)) 
 CFGs (reorder_sim_rel t n2 x1 e1 x2 e2)" in step_star.induct, clarsimp)
apply (clarsimp simp add: simulates_def reorder_sim_rel_def)
apply (rule_tac x=env in exI, simp)
apply (clarsimp simp add: simulates_def)
apply (frule simple_tCFG.safe_step, simp_all)
apply (frule TRANS_simple.reachable_safe, simp add: TRANS_simple_def TRANS_basics_def)
apply (simp add: reorder_sim_rel_def)
apply (frule TRANS_simple.reachable_step, simp+)
apply (frule reorder_simulates_step1, simp_all, clarsimp)
apply (frule reachable_step, simp+)
apply (erule_tac x=env' in allE, clarsimp)
apply (rule_tac x=env'a in exI, simp)
apply (rule step_star_trans, simp+)
apply (clarsimp simp add: simulates_def)
apply (erule_tac x=env0 in allE, erule impE, clarsimp simp add: reorder_sim_rel_def 
 TRANS_simple.reachable_def start_points_def)
apply (rule_tac x=env0 in exI, simp+, clarsimp)
apply (rule_tac x=env' in exI, simp)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply (simp add: reorder_def)
apply force
done

(* If a trace exists in the transformed program, it existed in the original. *)
corollary reorder_simulates1_final: "\<lbrakk>CFGs' \<in> trans_sf reorder \<tau> CFGs; final CFGs ps; 
 step_star CFGs' (env0, start_points CFGs) (env, ps)\<rbrakk> \<Longrightarrow>
 step_star CFGs (env0, start_points CFGs) (env, ps)"
apply (clarsimp simp add: reorder_def, frule reorder_vals, simp+, clarsimp)
apply (frule reorder_simulates1, simp+)
apply (simp add: reorder_sim_rel_def final_def)
done

lemma reorder_simulates_step2: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs; part_matches \<sigma> \<tau>;
 side_cond_sf reorder_sc \<sigma> CFGs; \<sigma> ''t'' = OThread t; \<sigma> ''n2'' = ONode n2; \<sigma> ''x1'' = OExpr (Var x1); 
 \<sigma> ''e1'' = OExpr e1; \<sigma> ''x2'' = OExpr (Var x2); \<sigma> ''e2'' = OExpr e2; step CFGs (enva, ps) (envb, ps');
 TRANS_simple.reachable CFGs' (env, ps); reachable (enva, ps);
 reorder_sim_rel t n2 x1 e1 x2 e2 ps env enva\<rbrakk> \<Longrightarrow>
 \<exists>env'. step CFGs' (env, ps) (env', ps') \<and> reorder_sim_rel t n2 x1 e1 x2 e2 ps' env' envb"
apply (subgoal_tac "CFGs' \<in> trans_sf reorder \<tau> CFGs")
apply (frule reorder_preserves_tCFGs)
apply (frule reorder_vals, simp+, clarsimp)
apply (subgoal_tac "TRANS_simple (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>))")
apply (clarsimp simp add: reorder_sim_rel_def)
apply (frule reachable_step, simp+)
apply (frule in_critical_types_gen, simp+, clarsimp)
apply (erule step.cases, clarsimp)
apply (case_tac "t \<notin> ts")
apply (rule_tac x="update_map env change_map" in exI, clarsimp)
apply (subgoal_tac "step (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>)) (env, ps) 
 (update_map env change_map, ps')", clarsimp)
apply (rule conjI, clarsimp)
apply (subgoal_tac "\<forall>x\<in>(instr_fv (x1 \<leftarrow> e1) \<union> instr_fv (x2 \<leftarrow> e2)). change_map x = None", clarsimp)
apply (rule conjI, rule eval_same, simp)+
apply (clarsimp, (erule_tac x=x in allE)+, simp)
apply (clarify, rule ccontr)
apply (erule_tac x=x and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" in allE,
 clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", simp+)
apply (cut_tac x=x and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply clarsimp
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply clarsimp
apply (rule_tac changes=changes and change_map=change_map and ts=ts and locker=locker in step, clarsimp+)
apply (case_tac "ta = t", simp+)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ps t = Some n2", simp_all)
apply (rule trans, rule_tac ps=ps and \<sigma>="\<sigma>(''t'' := OThread ta)" and t="''t''" in read_same_step, 
 simp_all, clarsimp)
apply (frule reachable_path, clarsimp)
apply (erule_tac x="OThread ta" in allE, erule_tac x=la in ballE, simp_all, 
 erule_tac x=ia in allE)
apply (erule disjE, clarsimp)
apply (cut_tac A="{''t''}" in fresh_new, simp+)
apply ((erule_tac x=x in allE)+, simp, erule disjE, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x1))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x1''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x2))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x2''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
(* Now, the case in which we actually use the changed thread. *)
apply (rule_tac x=t in ballE, simp, clarsimp)
apply (case_tac "n = n1", clarsimp)
apply (frule CFGs, simp+, simp add: step_one_thread_simps)
apply (clarsimp, frule simple_flowgraph.next_seq_correct, simp+)
apply (case_tac "simple_flowgraph.next_seq (Edges G) n1 \<noteq> n2", simp add: out_edges_def)
apply (subgoal_tac "(simple_flowgraph.next_seq (Edges G) n1, Seq) \<in> {(u, t). (n1, u, t) \<in> Edges G}", 
 simp, blast)
apply clarsimp
apply (rule_tac x=x1 and P="\<lambda>x. (\<exists>v t. (x, v) \<in> set (changes t)) \<longrightarrow> (\<exists>v'. change_map x = Some v')" 
 in allE, simp, erule impE, rule_tac x="eval enva e1" in exI, rule_tac x=t in exI, simp, clarsimp)
apply (rule_tac x=x1 and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, simp, erule_tac x=v' in allE, clarify)
apply (cut_tac CFGs'="CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, 
 simple_flowgraph.next_seq (Edges G) n1 := x1 \<leftarrow> e1)\<rparr>)" and \<sigma>=\<sigma> and ps=ps in reorder_critical, simp_all)
apply (case_tac "ta \<noteq> t")
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (erule_tac x=ta in ballE, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x1))" and t'="''t''" and x'="''x''" and
 G=Ga and n=n and env=enva and q=ps in change_writes, simp_all)
apply (drule reachable_path, clarsimp)
apply (thin_tac "\<forall>obj. \<forall>l\<in>Paths (start_points CFGs).
 \<forall>i. \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x1'') \<and>
     \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x2'') \<or>
       TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (in_critical ''t'' ''s'')")
apply (erule_tac x="OThread ta" in allE, erule_tac x="OExpr (Var x1)" in allE, 
 erule_tac x=la in ballE, erule_tac x=ia in allE, simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x1))" 
 in in_critical_cong [THEN subst], simp_all)
(* The assignment to x2 recorded was the one we moved. *)
apply (rule_tac x="((update_map enva change_map)(x1 := enva x1))(x2 := eval enva e2)" in exI, clarsimp)
apply (rule conjI, rule_tac ts=ts and changes="changes(t := [(x2, eval enva e2)])" and locker=locker 
 and change_map="(change_map(x2 \<mapsto> eval enva e2))(x1 := None)" in step, simp_all)
apply (simp add: simple_tCFG_def, frule_tac t=t in tCFG.CFGs, simp+, simp add: step_one_thread_simps)
apply (clarsimp, rule conjI, force, clarsimp)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (rule_tac x=ta in exI, case_tac "ta = t", simp+)
apply (clarsimp, rule conjI, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x1))" and t'="''t''" and x'="''x''" and
 n=n and env=enva and q=ps in change_writes, simp_all)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (drule reachable_path, clarsimp)
apply (thin_tac "\<forall>obj. \<forall>l\<in>Paths (start_points CFGs).
 \<forall>i. \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x1'') \<and>
     \<not> TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (read ''t'' ''x2'') \<or>
       TRANS_basics.models eval_pred CFGs (\<sigma>(''t'' := obj)) (l i) (in_critical ''t'' ''s'')")
apply (erule_tac x="OThread ta" in allE, erule_tac x="OExpr (Var x1)" in allE, 
 erule_tac x=la in ballE, erule_tac x=ia in allE, simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x1))" 
 in in_critical_cong [THEN subst], simp_all)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (simp add: update_map_def, rule ext, simp)
apply (subgoal_tac "\<forall>x\<in>(expr_fv e1 \<union> expr_fv e2 - {x1}). change_map x = None")
apply (rule conjI, rule eval_same, clarsimp)
apply (erule_tac x=x in ballE, simp+)
apply (rule eval_same, simp+)
apply (clarify, rule ccontr)
apply (erule_tac x=x and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" in allE,
 clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", clarsimp+)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac x=x and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply clarsimp
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply (case_tac "n = n2", clarsimp)
(* The second changed node. *)
apply (frule CFGs, simp add: step_one_thread_simps)
apply (clarsimp, frule_tac p=n2 in simple_flowgraph.next_seq_correct, simp+)
apply (simp add: simple_flowgraph_def, drule_tac u=n2 in flowgraph.no_loop)
apply (case_tac "simple_flowgraph.next_seq (Edges G) n2 = n2", simp+)
apply (rule_tac ts=ts and changes="changes(t := [(x1, enva x1)])" and 
 change_map="(change_map(x2 := None))(x1 \<mapsto> enva x1)" and locker=locker in step, simp_all, clarsimp)
apply (rule conjI, clarsimp)
apply (simp add: simple_tCFG_def, frule_tac t=t in tCFG.CFGs, simp+, simp add: step_one_thread_simps)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (rule trans, rule_tac ps=ps and \<sigma>="\<sigma>(''t'' := OThread ta)" and t="''t''" in read_same_step, 
 simp_all, clarsimp)
apply (frule reachable_path, clarsimp)
apply (erule_tac x="OThread ta" in allE, erule_tac x=la in ballE, simp_all, 
 erule_tac x=ia in allE)
apply (erule disjE, clarsimp)
apply (cut_tac A="{''t''}" in fresh_new, simp+)
apply ((erule_tac x=x in allE)+, simp, erule disjE, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x1))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x1''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, SOME y. y \<noteq> ''t'' := OExpr (Var x2))" and 
 \<sigma>'="\<sigma>(''t'' := OThread ta)" and t="''t''" and t'="''t''" and x="SOME y. y \<noteq> ''t''" and x'="''x2''" 
 and ps="la ia" in read_cong, simp+)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule in_critical_cong [THEN subst], simp_all)
apply (clarsimp, rule conjI, force, clarsimp)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (rule_tac x=ta in exI, case_tac "ta = t", simp+)
apply (clarsimp, rule conjI, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(''t'' := OThread ta, ''x'' := OExpr (Var x2))" and t'="''t''" and x'="''x''" and
 n=n and env=enva and q=ps in change_writes, simp_all)
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (cut_tac x=x2 and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (rule ext, case_tac "x = x2", simp)
apply (erule_tac x=x2 and P="\<lambda>x. (\<exists>v t. (x, v) \<in> set (changes t)) \<longrightarrow> (\<exists>v'. change_map x = Some v')" 
 in allE, erule impE, rule_tac x="eval enva e2" in exI, rule_tac x=t in exI, simp, clarsimp)
apply (erule_tac x=x2 and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, clarsimp)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (case_tac "ta = t", clarsimp+)
apply (cut_tac x=x2 and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply (case_tac "x = x1", clarsimp)
apply (case_tac "change_map x1", simp, clarsimp)
apply (erule_tac x=x1 and P="\<lambda>x. \<forall>v. change_map x = Some v \<longrightarrow> (\<exists>t. (x, v) \<in> set (changes t))" 
 in allE, clarsimp)
apply (case_tac "ta = t", simp+)
apply (erule_tac x=ta in ballE, simp_all, clarsimp)
apply (cut_tac x=x1 and G=Ga and n=n and env=enva and ps=ps and \<sigma>=\<sigma> in writes_critical, simp_all)
apply simp+
apply (cut_tac A="{''t'',''s''}" in fresh_new, simp+, clarsimp)
apply (cut_tac \<sigma>="\<sigma>(SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s'' := OThread ta)" and t="''t''" and x="''s''" and
 t'="SOME y. y \<noteq> ''t'' \<and> y \<noteq> ''s''" in mutex, clarsimp)
apply (erule_tac x=obj in allE)
apply (rule good_lock_cong [THEN subst], simp_all)
apply (rule_tac i1=i in critical_node_gen [THEN subst], simp_all)
apply clarsimp
apply (rule in_critical_cong [THEN subst], simp_all)
apply (rule_tac \<sigma>1="\<sigma>(''t'' := OThread ta)" in in_critical_cong [THEN subst], simp_all)
apply ((erule_tac x=x in allE)+, case_tac "change_map x", simp+)
(* The case in which we don't use the changed nodes. *)
apply (rule_tac x="update_map enva change_map" in exI, simp)
apply (subgoal_tac "step (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>)) (enva, ps) 
 (update_map enva change_map, ps')", simp)
apply (clarsimp simp add: reorder_sc_def Let_def)
apply (cut_tac A="{''t'',''n1'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''t'',''x1'',''e1'',''t'',''n1'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac ps=ps and \<sigma>=\<sigma> and lq=la and iq=ia and n="MVar ''n1''" and ps'=ps' in AP_step_gen, simp_all)
apply (simp add: Let_def)
apply (rule_tac x="ONode n2" in exI, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x=lc in ballE, simp_all, clarsimp)
apply (rule_tac x=ic in exI, simp)
apply (rule_tac changes=changes and change_map=change_map and ts=ts and locker=locker
 in step, simp_all, clarsimp)
apply (rule_tac changes=changes and change_map=change_map and ts=ts and locker=locker
 in step, simp_all)
apply (frule CFGs)
apply (simp add: simple_tCFG_def, drule_tac t=t in tCFG.CFGs, simp+)
apply (rule trans, rule reorder_step_out, simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply (simp add: reorder_def)
apply force
done

theorem reorder_simulates2: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs; part_matches \<sigma> \<tau>;
 side_cond_sf reorder_sc \<sigma> CFGs; step_star CFGs (env0, start_points CFGs) (env, ps); 
 \<sigma> ''t'' = OThread t; \<sigma> ''n2'' = ONode n2; \<sigma> ''x1'' = OExpr (Var x1); \<sigma> ''e1'' = OExpr e1;
 \<sigma> ''x2'' = OExpr (Var x2); \<sigma> ''e2'' = OExpr e2\<rbrakk> \<Longrightarrow>
 \<exists>env'. reorder_sim_rel t n2 x1 e1 x2 e2 ps env' env \<and> 
        step_star CFGs' (env0, start_points CFGs) (env', ps)"
apply (subgoal_tac "CFGs' \<in> trans_sf reorder \<tau> CFGs")
apply (frule reorder_preserves_tCFGs)
apply (frule reorder_vals, simp+, clarsimp)
apply (subgoal_tac "TRANS_simple (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>))")

apply (drule_tac P="simulates CFGs (CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2, n2 := x1 \<leftarrow> e1)\<rparr>))
 (reorder_sim_rel_rev t n2 x1 e1 x2 e2)" in step_star.induct, clarsimp)
apply (clarsimp simp add: simulates_def reorder_sim_rel_def)
apply (rule_tac x=env in exI, simp)
apply (clarsimp simp add: simulates_def)
apply (cut_tac ps=b in safe_step, erule reachable_safe, simp+)
apply (frule reachable_step, simp+)
apply (frule reorder_simulates_step2, simp_all, clarsimp)
apply (frule TRANS_simple.reachable_step, simp+)
apply (erule_tac x=env' in allE, clarsimp)
apply (rule_tac x=env'a in exI, simp)
apply (rule step_star_trans, simp+)
apply (clarsimp simp add: simulates_def)
apply (erule_tac x=env0 in allE, erule impE, clarsimp simp add: reorder_sim_rel_def 
 TRANS_simple.reachable_def start_points_def)
apply (rule_tac x=env0 in exI, simp+, clarsimp)
apply (rule_tac x=env' in exI, simp)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply (simp add: reorder_def)
apply force
done

corollary reorder_simulates2_final: "\<lbrakk>CFGs' \<in> trans_sf reorder \<tau> CFGs; final CFGs ps; 
 step_star CFGs (env0, start_points CFGs) (env, ps)\<rbrakk> \<Longrightarrow>
 step_star CFGs' (env0, start_points CFGs) (env, ps)"
apply (clarsimp simp add: reorder_def, frule reorder_vals, simp+, clarsimp)
apply (frule reorder_simulates2, simp+)
apply (simp add: reorder_sim_rel_def final_def)
done

theorem reorder_same_finals: "\<lbrakk>CFGs' \<in> trans_sf reorder \<tau> CFGs; final CFGs ps\<rbrakk> \<Longrightarrow>
 step_star CFGs' (env0, start_points CFGs) (env, ps) \<longleftrightarrow> 
 step_star CFGs (env0, start_points CFGs) (env, ps)"
by (auto simp add: reorder_simulates1_final reorder_simulates2_final)

(* Compositionality *)
definition "reorder_sc_t_only \<equiv> EF (in_critical ''t'' ''s'' \<and>sc SCPred (Node ''t'' (MVar ''n2'')) \<and>sc
 SCPred (Stmt ''t'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2'')))) \<and>sc 
 AP ''t'' (SCPred (Node ''t'' (MVar ''n1'')) \<and>sc (SCPred (Stmt ''t'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))))) \<and>sc 
 EP ''t'' (SCPred (Node ''t'' (MVar ''n1'')) \<and>sc (SCPred (Stmt ''t'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1''))))))) \<and>sc 
 \<not>sc (SCPred (Freevar ''x1'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc 
 \<not>sc (SCPred (Freevar ''x2'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1''))))) \<and>sc good_lock ''t'' ''s'' \<and>sc 
 SCAll ''x'' (AG (((SCPred (Freevar ''x'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))) \<or>sc 
 SCPred (Freevar ''x'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc write ''t'' ''x'') \<longrightarrow>sc 
 in_critical ''t'' ''s'')) \<and>sc 
 AG ((read ''t'' ''x1'' \<or>sc read ''t'' ''x2'') \<longrightarrow>sc in_critical ''t'' ''s'')"

definition "reorder_sc_all_threads \<equiv> SCAll ''t'' (good_lock ''t'' ''s'') \<and>sc 
 SCAll ''t'' (SCAll ''x'' (AG (((SCPred (Freevar ''x'' (Inj (''x1'' \<leftarrow> EPInj (Var ''e1'')))) \<or>sc 
 SCPred (Freevar ''x'' (Inj (''x2'' \<leftarrow> EPInj (Var ''e2''))))) \<and>sc write ''t'' ''x'') \<longrightarrow>sc 
 in_critical ''t'' ''s''))) \<and>sc 
 SCAll ''t'' (AG ((read ''t'' ''x1'' \<or>sc read ''t'' ''x2'') \<longrightarrow>sc in_critical ''t'' ''s''))"

lemma composition: "\<lbrakk>models [t \<mapsto> G] \<sigma> (start_points (empty(t \<mapsto> G))) reorder_sc_t_only;
 action_list_sf reorder_actions \<sigma> [t \<mapsto> G] = Some CFGs'; CFGs' t = Some G'; is_flowgraph G instr_edges;
 models CFGs \<sigma> (start_points CFGs) reorder_sc_all_threads; part_matches \<sigma> \<tau>; simple_tCFG (CFGs(t \<mapsto> G))\<rbrakk> \<Longrightarrow>
 CFGs(t \<mapsto> G') \<in> trans_sf reorder \<tau> (CFGs(t \<mapsto> G))"
apply (simp add: reorder_def)
apply (rule_tac x=\<sigma> in exI, simp)
apply (subgoal_tac "TRANS_simple [t \<mapsto> G]")
apply (frule TRANS_simple.reorder_vals)
apply (erule sym)
apply (clarsimp simp add: reorder_sc_def reorder_sc_t_only_def Let_def)
apply (simp add: TRANS_simple.good_lock_threads)
apply (case_tac "\<sigma> ''t''", simp_all)
apply (cut_tac A="{''t'',''x1'',''e1'',''t'',''n1'',''t''}" in fresh_new, simp+, clarsimp)
apply (case_tac "\<sigma> ''x2''", simp_all)
apply (case_tac expr, simp_all)
apply (case_tac "\<sigma> ''e2''", simp_all, clarsimp)
apply (case_tac "thread \<noteq> t", simp+, clarsimp simp add: fun_upd_idem)
apply (case_tac "\<sigma> ''x1''", simp_all)
apply (rule conjI, clarsimp)
apply (case_tac "objb = OThread t", clarsimp simp add: fun_upd_idem)
apply (erule_tac x=objc in allE, (erule_tac x=lb and A="tCFG.Paths [t \<mapsto> G] (start_points [t \<mapsto> G])" 
 in ballE)+, (erule_tac x=ib in allE)+, simp_all)
apply (simp add: fun_upd_idem write_def Let_def)
apply (cut_tac A="{''x'',''t''}" in fresh_new, simp+, clarsimp)
apply (case_tac objb, simp_all)
apply (case_tac objc, simp_all)
apply (case_tac exprb, simp_all, clarsimp)
apply (case_tac objd, simp_all)
apply clarsimp
apply ((erule_tac x=lb and A="tCFG.Paths [t \<mapsto> G] (start_points [t \<mapsto> G])" 
 in ballE)+, (erule_tac x=ib in allE)+, simp_all)
apply (case_tac "objb = OThread t", simp add: fun_upd_idem)
apply (clarsimp simp add: read_def Let_def)
apply (cut_tac A="{''x1'',''t'',SOME y. y \<noteq> ''x1'' \<and> y \<noteq> ''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''x1'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''x2'',''t'',SOME y. y \<noteq> ''x2'' \<and> y \<noteq> ''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''x2'',''t''}" in fresh_new, simp+, clarsimp)
apply (case_tac objb, simp_all)
apply (rule conjI, clarsimp)
apply (case_tac expr, simp_all)
apply (rule conjI, case_tac objc, simp_all)
apply (case_tac exprb, simp_all)
apply (case_tac objd, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply (case_tac objd, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply clarsimp
apply (case_tac expr, simp_all)
apply (rule conjI, case_tac objc, simp_all)
apply (case_tac exprb, simp_all)
apply (case_tac objd, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply (case_tac objd, simp_all)
apply (case_tac expr1, simp_all)
apply (simp split: option.splits)
apply clarsimp
apply (case_tac "ta \<noteq> t", simp, clarsimp)
apply (rule conjI, clarsimp simp add: action_list_sf_def Let_def reorder_actions_def)
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and t=t and n=n2 in tCFG.thread_of_correct, 
 simp add: simple_tCFG_def, simp+)
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and t=t and n=n1 in tCFG.thread_of_correct, 
 simp add: simple_tCFG_def, simp+)
apply (frule_tac t=t and n'=n2 and G'="G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2)\<rparr>" 
 in simple_tCFG.same_thread, simp+)
apply (cut_tac CFGs="CFGs(t \<mapsto> G\<lparr>Label := (Label G)(n1 := x2 \<leftarrow> e2)\<rparr>)" and t=t and n=n2 
 in nodes_by_graph, simp+)
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and t=t and n=n1 in nodes_by_graph, simp+)
(* Now the hard part: proving that the combined condition was satisfied. *)
apply (clarsimp simp add: reorder_sc_def)
apply (rule conjI)
apply (simp add: simple_tCFG_def, frule_tac q="start_points (CFGs(t \<mapsto> G))" in tCFG.exists_path, 
 clarsimp)
apply (cut_tac t=t and CFGs="[t \<mapsto> G]" and instr_edges=instr_edges and q'="start_points (CFGs(t \<mapsto> G))" 
 in tCFG.path_by_thread_gen, simp add: tCFG_def, simp+)
apply (simp add: start_points_def)
apply clarsimp
apply (rule_tac x=l' in bexI, simp_all, rule_tac x=i in exI, simp)
apply (rule conjI)
apply (frule_tac CFGs1="[t \<mapsto> G]" and CFGs'1="CFGs(t \<mapsto> G)" in TRANS_simple.in_critical_cong_graphs [THEN subst], simp_all)
apply (rule conjI, simp+)
apply (simp add: simple_tCFG_def, simp+)
apply (simp add: Let_def)
apply (cut_tac A="{''t'',''x1'',''e1'',''t'',''n1'',''t''}" in fresh_new, simp+, clarsimp)
apply (rule conjI)
apply (rule_tac x="ONode n2" in exI, clarsimp)
apply (clarsimp simp add: reorder_sc_t_only_def Let_def)
apply (frule_tac l=lb and CFGs'="[t \<mapsto> G]" and t=t in tCFG.rpath_by_thread_gen, simp+)
apply (simp add: TRANS_simple_def simple_tCFG_def, simp+)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x=l'a and A="tCFG.RPaths [t \<mapsto> G] (lc ia)" in ballE, clarsimp)
apply (rule_tac x=ic in exI, simp)
apply (case_tac obj, simp_all)
apply (rule_tac x="ONode n2" in exI, clarsimp)
apply (clarsimp simp add: reorder_sc_t_only_def Let_def)
apply (frule_tac l=l' and i=i in tCFG.reverse_path, simp, clarsimp)
apply (cut_tac CFGs="[t \<mapsto> G]" and l=lc and CFGs'="CFGs(t \<mapsto> G)" and t=t and instr_edges=instr_edges
 in tCFG.rpath_by_thread_gen)
apply (simp add: TRANS_simple_def simple_tCFG_def, simp+)
apply (simp add: start_points_def)
apply clarsimp
apply (rule_tac x=l'b in bexI, clarsimp)
apply (case_tac obj, simp_all)
apply (rule conjI, clarsimp)
apply (case_tac "\<exists>t'. obj = OThread t'", clarsimp)
apply (case_tac "t' = t", clarsimp)
apply (erule_tac x="OThread t" in allE, simp add: fun_upd_idem)
apply (rule_tac CFGs'1="CFGs(t \<mapsto> G)" in TRANS_simple.good_lock_cong_graphs [THEN subst], simp_all)
apply (rule conjI, simp+)
apply (clarsimp simp add: reorder_sc_all_threads_def)
apply (erule_tac x="OThread t'" in allE)+
apply (rule_tac CFGs'1="CFGs(t \<mapsto> G)" in good_lock_cong_graphs [THEN subst], simp_all)
apply clarsimp
apply (rule TRANS_simple.good_lock_wrong_type)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply simp
apply (rule conjI, clarsimp)
apply (case_tac obja, simp_all)
apply (case_tac expr, simp_all)
apply (case_tac "\<exists>t'. obj = OThread t'", clarsimp)
apply (case_tac "t' = t", clarsimp)
apply (cut_tac l=la and CFGs="CFGs(t \<mapsto> G)" and CFGs'="[t \<mapsto> G]" and q="start_points (CFGs(t \<mapsto> G))" 
 and q'="start_points [t \<mapsto> G]" and t=t in tCFG.path_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply (simp add: TRANS_simple_def TRANS_basics_def simple_tCFG_def)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x="OThread t" in allE, erule_tac x="OExpr (Var var)" in allE, 
 erule_tac x=l' in ballE, erule_tac x=ia in allE, erule impE)
apply (rule_tac CFGs1="CFGs(t \<mapsto> G)" and \<sigma>1="\<sigma>(''t'' := OThread t, ''x'' := OExpr (Var var))" and
 t1="''t''" and x1="''x''" in TRANS_simple.write_cong_gen [THEN subst], simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and \<sigma>="\<sigma>(''t'' := OThread t, ''x'' := OExpr (Var var))" and
 t="''t''" and x="''s''" and l'=l' and \<sigma>'="\<sigma>(''t'' := OThread t, ''x'' := OExpr (Var var))" and i=ia 
 and t'="''t''" and x'="''s''" in TRANS_simple.in_critical_cong_graphs, simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (clarsimp simp add: reorder_sc_all_threads_def)
apply (cut_tac l=la and CFGs="CFGs(t \<mapsto> G)" and CFGs'="CFGs" and q="start_points (CFGs(t \<mapsto> G))" 
 and q'="start_points CFGs" and t=t' in tCFG.path_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply unfold_locales
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x="OThread t'" in allE, erule_tac x="OExpr (Var var)" in allE, 
 erule_tac x=l' and A="Paths (start_points CFGs)" in ballE, erule_tac x=ia in allE, erule impE)
apply (rule_tac CFGs1="CFGs(t \<mapsto> G)" and \<sigma>1="\<sigma>(''t'' := OThread t', ''x'' := OExpr (Var var))" and
 t1="''t''" and x1="''x''" in TRANS_simple.write_cong_gen [THEN subst], simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and \<sigma>="\<sigma>(''t'' := OThread t', ''x'' := OExpr (Var var))" and
 t="''t''" and x="''s''" and l'=l' and \<sigma>'="\<sigma>(''t'' := OThread t', ''x'' := OExpr (Var var))" and i=ia 
 and t'="''t''" and x'="''s''" in TRANS_simple.in_critical_cong_graphs, simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (clarsimp simp add: simple_tCFG_def tCFG_def)
apply (rule conjI, clarsimp)
apply (drule CFGs, simp)
apply (clarsimp, drule disjoint, simp+)
apply (clarsimp simp add: write_def Let_def)
apply (cut_tac A="{''x'',''t''}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x=thread in allE, simp)
apply clarsimp
apply (case_tac "\<exists>t'. obj = OThread t'", clarsimp)
apply (case_tac "t' = t", clarsimp)
apply (cut_tac l=la and CFGs="CFGs(t \<mapsto> G)" and CFGs'="[t \<mapsto> G]" and q="start_points (CFGs(t \<mapsto> G))" 
 and q'="start_points [t \<mapsto> G]" and t=t in tCFG.path_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply (simp add: TRANS_simple_def TRANS_basics_def simple_tCFG_def)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x="OThread t" in allE, erule_tac x=l' in ballE, erule_tac x=ia in allE, 
 erule disjE, clarsimp)
apply (rule conjI)
apply (rule TRANS_simple.read_cong_gen [THEN subst], simp_all)
apply (clarsimp, clarsimp)
apply (rule_tac x1="''x2''" in TRANS_simple.read_cong_gen [THEN subst], simp_all)
apply clarsimp+
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and \<sigma>="\<sigma>(''t'' := OThread t)" and
 t="''t''" and x="''s''" and l'=l' and \<sigma>'="\<sigma>(''t'' := OThread t)" and i=ia 
 and t'="''t''" and x'="''s''" in TRANS_simple.in_critical_cong_graphs, simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (clarsimp simp add: reorder_sc_all_threads_def)
apply (cut_tac l=la and CFGs="CFGs(t \<mapsto> G)" and CFGs'=CFGs and q="start_points (CFGs(t \<mapsto> G))" 
 and q'="start_points CFGs" and t=t' in tCFG.path_by_thread_gen, simp_all)
apply (simp add: simple_tCFG_def)
apply (clarsimp simp add: tCFG_def)
apply (rule conjI, clarsimp)
apply (drule CFGs, simp)
apply (clarsimp, drule disjoint, simp+)
apply (simp add: start_points_def)
apply clarsimp
apply (erule_tac x="OThread t'" in allE, erule_tac x=l' and A="Paths (start_points CFGs)" in ballE, 
 erule_tac x=ia in allE, erule disjE, clarsimp)
apply (rule conjI)
apply (rule TRANS_simple.read_cong_gen [THEN subst], simp_all)
apply (clarsimp simp add: TRANS_simple_def TRANS_basics_def simple_tCFG_def tCFG_def)
apply (rule conjI, clarsimp)
apply (drule CFGs, simp)
apply (clarsimp, drule disjoint, simp+)
apply (rule_tac x1="''x2''" in TRANS_simple.read_cong_gen [THEN subst], simp_all)
apply (clarsimp simp add: TRANS_simple_def TRANS_basics_def simple_tCFG_def tCFG_def)
apply (rule conjI, clarsimp)
apply (drule CFGs, simp)
apply (clarsimp, drule disjoint, simp+)
apply (cut_tac CFGs="CFGs(t \<mapsto> G)" and \<sigma>="\<sigma>(''t'' := OThread t')" and
 t="''t''" and x="''s''" and l'=l' and \<sigma>'="\<sigma>(''t'' := OThread t')" and i=ia 
 and t'="''t''" and x'="''s''" in TRANS_simple.in_critical_cong_graphs, simp_all)
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply clarsimp+
apply (clarsimp simp add: simple_tCFG_def tCFG_def)
apply (rule conjI, clarsimp)
apply (drule CFGs, simp)
apply (clarsimp, drule disjoint, simp+)
apply (clarsimp simp add: read_def Let_def)
apply (cut_tac A="{''x1'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''x1'',''t'',SOME y. y \<noteq> ''x1'' \<and> y \<noteq> ''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''x2'',''t''}" in fresh_new, simp+, clarsimp)
apply (cut_tac A="{''x2'',''t'',SOME y. y \<noteq> ''x2'' \<and> y \<noteq> ''t''}" in fresh_new, simp+, clarsimp)
apply (case_tac obj, simp_all)
apply (erule_tac x=thread in allE, simp)
apply (simp split: if_splits)+
done

(* We need a more realistic example - real optimization and real IR. *)

end

end
