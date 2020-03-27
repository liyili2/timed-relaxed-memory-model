theory step_rel
imports memory_model trans_sim
begin

locale step_rel = memory_model
 where free_set = "free_set :: 'memory \<Rightarrow> 'loc set" 
    and can_read = "can_read :: 'memory \<Rightarrow> 'thread \<Rightarrow> 'loc \<Rightarrow> 'val set"
    and update_mem=
        "update_mem::'memory \<Rightarrow> ('thread, 'loc, 'val) access set \<Rightarrow> 'memory \<Rightarrow> bool" 
    and start_mem = "start_mem:: 'memory"
  for free_set and can_read and update_mem and start_mem +
  fixes step_rel::"'thread \<Rightarrow> ('node, 'edge_type, 'instr) flowgraph \<Rightarrow> 'memory \<Rightarrow> 'config \<Rightarrow> 
  ('thread, 'loc, 'val) access set \<Rightarrow> 'config \<Rightarrow> bool"
  and start_state::"('thread \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)
                                       \<Rightarrow> ('thread \<rightharpoonup> 'config) \<Rightarrow> 'memory \<Rightarrow> bool"
  and get_point::"'config \<Rightarrow> 'node"
  and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq::'edge_type
  assumes start_points [simp]: "start_state CFGs S m
         \<Longrightarrow> (\<lambda> x . case S x of Some a \<Rightarrow> (\<lambda>C. Some (get_point C)) a 
                              | None \<Rightarrow> None) = start_points CFGs"
      and step_along_edge: "\<lbrakk>step_rel t G m C ops C'; is_flowgraph G Seq instr_edges; get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> 
    \<exists>ty. (get_point C, get_point C', ty) \<in> Edges (G::('node, 'edge_type, 'instr) flowgraph)"

begin

lemma step_safe: "\<lbrakk>step_rel t G m C ops C'; is_flowgraph G Seq instr_edges; get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> 
    get_point C' \<in> Nodes G"
by (drule step_along_edge, simp+, simp add: is_flowgraph_def flowgraph_def pointed_graph_def)

abbreviation "well_formed G \<equiv> is_flowgraph G Seq instr_edges"

inductive one_step where
step_single [intro!]: "\<lbrakk>step_rel t G mem C ops C'; update_mem mem ops mem'\<rbrakk> \<Longrightarrow> 
  one_step t G (C, mem) (C', mem')"

lemma one_step_safe: "\<lbrakk>one_step t G (C, mem) (C', mem'); well_formed G; get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  get_point C' \<in> Nodes G"
by (erule one_step.cases, rule step_safe, simp+)

lemma one_step_along_edge: "\<lbrakk>one_step t G (C, m) (C', m'); is_flowgraph G Seq instr_edges; 
  get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> \<exists>ty. (get_point C, get_point C', ty) \<in> Edges G"
by (erule one_step.cases, rule step_along_edge, simp+)

inductive conc_step where
step_thread [intro]: "\<lbrakk>CFGs t = Some G; states t = Some C; step_rel t G mem C ops C'; 
  update_mem mem ops mem'\<rbrakk> \<Longrightarrow> conc_step CFGs (states, mem) (states(t \<mapsto> C'), mem')"

abbreviation "get_points (S::'thread \<rightharpoonup> 'config) \<equiv>
                  (\<lambda> x . case S x of Some a \<Rightarrow> (\<lambda>C. Some (get_point C)) a 
                              | None \<Rightarrow> None)"

lemma one_step_conc_step: "\<lbrakk>one_step t G (C, m) (C', m'); CFGs t = Some G; states t = Some C\<rbrakk> \<Longrightarrow> 
  conc_step CFGs (states, m) (states(t \<mapsto> C'), m')"
by (erule one_step.cases, rule step_thread, auto)

lemma conc_step_safe: "\<lbrakk>conc_step CFGs (states, mem) (states', mem'); tCFG CFGs instr_edges Seq; 
  safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points states')"
apply (erule conc_step.cases, clarsimp simp add: safe_points_def)
apply (case_tac "t = t", clarsimp)
apply (rule step_safe, simp+)
apply (erule tCFG.CFGs, simp)
apply force
apply (force simp add: map_comp_def)
done

lemma conc_steps_safe: "\<lbrakk>(conc_step CFGs)^** (states, mem) (states', mem'); tCFG CFGs instr_edges Seq; 
  safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points states')"
by (drule_tac P="\<lambda>(states, mem) (states', mem'). safe_points CFGs (get_points states) \<longrightarrow> 
  safe_points CFGs (get_points states')" in rtranclp.induct, auto intro: conc_step_safe)

definition "run_prog CFGs C \<equiv> \<exists>C0 mem0. start_state CFGs C0 mem0 \<and> (conc_step CFGs)^** (C0, mem0) C"

lemma run_progI [intro]: "\<lbrakk>start_state CFGs C0 mem0; (conc_step CFGs)^** (C0, mem0) C\<rbrakk> \<Longrightarrow> 
  run_prog CFGs C"
by (force simp add: run_prog_def)

lemma run_prog_conc_step [intro]: "\<lbrakk>run_prog CFGs C; conc_step CFGs C C'\<rbrakk> \<Longrightarrow> run_prog CFGs C'"
by (force simp add: run_prog_def)

lemma run_prog_conc_steps [intro]: "\<lbrakk>run_prog CFGs C; (conc_step CFGs)^** C C'\<rbrakk> \<Longrightarrow> run_prog CFGs C'"
by (force simp add: run_prog_def)

lemma run_prog_induct [elim]: "\<lbrakk>run_prog CFGs C; \<And>C0 mem0. start_state CFGs C0 mem0 \<Longrightarrow> P (C0, mem0); 
 \<And>C C'. run_prog CFGs C \<Longrightarrow> P C \<Longrightarrow> conc_step CFGs C C' \<Longrightarrow> P C'\<rbrakk> \<Longrightarrow> P C"
apply (clarsimp simp add: run_prog_def)
apply (drule_tac P="\<lambda>C C'. start_state CFGs (fst C) (snd C) \<longrightarrow> P C'" in rtranclp.induct, auto)
by (metis (mono_tags))

lemma run_prog_one_step: "\<lbrakk>run_prog CFGs (S, mem); S t = Some s; CFGs t = Some G;
 one_step t G (s, mem) (s', mem')\<rbrakk> \<Longrightarrow> run_prog CFGs (S(t \<mapsto> s'), mem')"
by (erule run_prog_conc_step, erule one_step.cases, auto)

lemma run_prog_one_steps: "\<lbrakk>run_prog CFGs (S, mem); S t = Some s; CFGs t = Some G;
 (one_step t G)^** (s, mem) (s', mem')\<rbrakk> \<Longrightarrow> run_prog CFGs (S(t \<mapsto> s'), mem')"
apply (drule_tac P="\<lambda>(s, mem) (s', mem'). run_prog CFGs (S, mem) \<and> S t = Some s \<and> CFGs t = Some G \<longrightarrow> 
  run_prog CFGs (S(t \<mapsto> s'), mem')" in rtranclp.induct, auto simp add: map_upd_triv)
apply (drule_tac mem=ba in run_prog_one_step, simp+, force, simp+)
done

lemma run_prog_step: "\<lbrakk>run_prog CFGs (S, mem); S t = Some s; CFGs t = Some G;
 step_rel t G mem s ops s'; update_mem mem ops mem'\<rbrakk> \<Longrightarrow> run_prog CFGs (S(t \<mapsto> s'), mem')"
by (erule run_prog_one_step, auto)

lemma run_prog_safe: "\<lbrakk>run_prog CFGs (S, mem); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points S)"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs (S, mem); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points S)"
by (clarsimp simp add: run_prog_def, rule conc_steps_safe, simp+)
qed

(* paths *)
lemma step_increment_path: "\<lbrakk>step_rel t G m C a C'; tCFG CFGs instr_edges Seq; CFGs t = Some G; 
  l \<in> pre_tCFG.Paths CFGs ps; p = get_point C; p' = get_point C'; ps t = Some p'; p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  [ps(t \<mapsto> p)] \<frown> l \<in> pre_tCFG.Paths CFGs (ps(t \<mapsto> p))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>step_rel t G m C a C'; tCFG CFGs instr_edges Seq; CFGs t = Some G; 
  l \<in> pre_tCFG.Paths CFGs ps; p = get_point C; p' = get_point C'; ps t = Some p'; p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  [ps(t \<mapsto> p)] \<frown> l \<in> pre_tCFG.Paths CFGs (ps(t \<mapsto> p))"
apply (rule pre_tCFG.path_incremental_gen, unfold_locales, simp)
apply (frule step_along_edge)
apply (erule tCFG.CFGs, simp+)
done
qed

lemma step_increment_rpath: "\<lbrakk>step_rel t G m C a C'; tCFG CFGs instr_edges Seq; CFGs t = Some G; 
  l \<in> pre_tCFG.RPaths CFGs ps; p0 = get_point C; p = get_point C'; ps t = Some p0; p0 \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 [ps(t \<mapsto> p)] \<frown> l \<in> pre_tCFG.RPaths CFGs (ps(t \<mapsto> p))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>step_rel t G m C a C'; tCFG CFGs instr_edges Seq; CFGs t = Some G; 
  l \<in> pre_tCFG.RPaths CFGs ps; p0 = get_point C; p = get_point C'; ps t = Some p0; p0 \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 [ps(t \<mapsto> p)] \<frown> l \<in> pre_tCFG.RPaths CFGs (ps(t \<mapsto> p))"
apply (rule rpath_incremental_gen, simp+, clarsimp)
apply (frule step_along_edge)
apply (erule tCFG.CFGs, simp+)
done
qed

lemma one_step_increment_path: "\<lbrakk>one_step t G (C, m) (C', m'); tCFG CFGs instr_edges Seq; CFGs t = Some G; 
  l \<in> pre_tCFG.Paths CFGs ps; p = get_point C; p' = get_point C'; ps t = Some p'; p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  [ps(t \<mapsto> p)] \<frown> l \<in> pre_tCFG.Paths CFGs (ps(t \<mapsto> p))"
by (erule one_step.cases, rule step_increment_path, simp+)

lemma one_step_increment_rpath: "\<lbrakk>one_step t G (C, m) (C', m'); tCFG CFGs instr_edges Seq; CFGs t = Some G; 
  l \<in> pre_tCFG.RPaths CFGs ps; p0 = get_point C; p = get_point C'; ps t = Some p0; p0 \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 [ps(t \<mapsto> p)] \<frown> l \<in> pre_tCFG.RPaths CFGs (ps(t \<mapsto> p))"
by (erule one_step.cases, rule step_increment_rpath, simp+)

lemma conc_step_increment_path: "\<lbrakk>conc_step CFGs C C'; tCFG CFGs instr_edges Seq; 
  l \<in> pre_tCFG.Paths CFGs (get_points (fst C')); safe_points CFGs (get_points (fst C))\<rbrakk> \<Longrightarrow> 
 [get_points (fst C)] \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst C))"
apply (auto elim!: conc_step.cases)
apply (frule_tac ps="get_points (states(t \<mapsto> C'a))" in step_increment_path, auto simp add: safe_points_def)
apply force
apply (subgoal_tac "get_points (states(t \<mapsto> C'a))(t \<mapsto> get_point Ca) = get_points states", simp)
apply (rule ext, clarsimp simp add: map_comp_def)
done

lemma conc_steps_path: "\<lbrakk>(conc_step CFGs)^** (states, mem) (states', mem'); tCFG CFGs instr_edges Seq; 
  l \<in> pre_tCFG.Paths CFGs (get_points states'); safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points states \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points states)"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>(conc_step CFGs)^** (states, mem) (states', mem'); tCFG CFGs instr_edges Seq; 
  l \<in> pre_tCFG.Paths CFGs (get_points states'); safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points states \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points states)"
apply (drule_tac P="\<lambda>(states, mem) (states', mem'). \<forall>l. l \<in> pre_tCFG.Paths CFGs (get_points states') \<and> 
  safe_points CFGs (get_points states) \<longrightarrow> (\<exists>l'. hd (l' @ [l 0]) = get_points states \<and> 
  l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points states))" in rtranclp.induct, auto)
apply (rule_tac x="[]" in exI, simp)
apply (drule conc_step_increment_path, simp+)
apply (drule conc_steps_safe, simp+)
by (metis append_is_Nil_conv hd_append2 i_append_assoc i_append_nth_Cons_0 not_Cons_self2)
qed

lemma run_prog_path: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>C0 mem0. start_state CFGs C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). \<exists>i. l i = get_points (fst C))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>C0 mem0. start_state CFGs C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). \<exists>i. l i = get_points (fst C))"
apply (clarsimp simp add: run_prog_def)
apply (cut_tac q="get_points (fst C)" in exists_path, clarsimp)
apply (case_tac C, clarsimp)
apply (drule conc_steps_path, simp+)
apply clarsimp
apply (rule conjI, force)
apply (rule_tac x="l' \<frown> l" in bexI, simp_all)
apply (rule_tac x="length l'" in exI, simp)
done
qed

(* The step-star relation as inducing a list of intermediate states. *)
lemma conc_step_star_steps: "(conc_step CFGs)^** C C' \<Longrightarrow> 
 \<exists>l. hd (l @ [C']) = C \<and> (\<forall>i<length l. conc_step CFGs (l ! i) ((l @ [C']) ! Suc i))"
apply (induct rule: rtranclp_induct, auto)
apply (rule_tac x="[]" in exI, simp)
apply (rule_tac x="l @ [(a, b)]" in exI, clarsimp)
apply (rule conjI, case_tac l, simp+)
apply clarsimp
apply (case_tac "i = length l", clarsimp simp add: nth_append)
apply (erule_tac x=i in allE, auto simp add: nth_append)
done

lemma step_star_path: "\<lbrakk>hd (l' @ [C']) = C; \<forall>i<length l'. conc_step CFGs (l' ! i) ((l' @ [C']) ! Suc i);
 l \<in> pre_tCFG.Paths CFGs (get_points (fst C')); safe_points CFGs (get_points (fst C)); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 map (get_points o fst) l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst C))"
apply (induct l' arbitrary: C l, auto)
apply (case_tac l', auto)
apply (drule conc_step_increment_path, simp+)
apply (subgoal_tac "(get_points a # map (get_points \<circ> fst) list) \<frown> l \<in> pre_tCFG.Paths CFGs (get_points a)")
apply (erule_tac x=0 in allE, clarsimp)
apply (drule conc_step_increment_path, simp+)
apply (subgoal_tac "\<forall>i<Suc (length list). conc_step CFGs (((a, b) # list) ! i) ((list @ [C']) ! i)")
apply (subgoal_tac "safe_points CFGs (get_points a)", force)
apply (erule_tac x=0 in allE, clarsimp, rule conc_step_safe, auto)
done

lemma run_prog_steps: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l C0 mem0. start_state CFGs C0 mem0 \<and> 
 (\<forall>i<length l. conc_step CFGs (l ! i) ((l @ [C]) ! Suc i)) \<and>
 (\<exists>l'\<in>pre_tCFG.Paths CFGs (get_points (fst C)). map (get_points o fst) l \<frown> l' \<in> pre_tCFG.Paths CFGs (start_points CFGs))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l C0 mem0. start_state CFGs C0 mem0 \<and> 
 (\<forall>i<length l. conc_step CFGs (l ! i) ((l @ [C]) ! Suc i)) \<and>
 (\<exists>l'\<in>pre_tCFG.Paths CFGs (get_points (fst C)). map (get_points o fst) l \<frown> l' \<in> pre_tCFG.Paths CFGs (start_points CFGs))"
apply (clarsimp simp add: run_prog_def)
apply (drule conc_step_star_steps, clarsimp)
apply (cut_tac q="get_points (fst C)" in exists_path, clarsimp)
apply (frule step_star_path, simp+)
apply (rule conjI, force+)
done
qed

lemma conc_step_star_path2: "\<lbrakk>(conc_step CFGs)^** C C'; l \<in> pre_tCFG.Paths CFGs (get_points (fst C'));
 safe_points CFGs (get_points (fst C)); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points (fst C) \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst C)) \<and>
 (\<forall>i<length l'. \<exists>C''. l' ! i = get_points (fst C'') \<and> (conc_step CFGs)^** C C'' \<and> (conc_step CFGs)^** C'' C')"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>(conc_step CFGs)^** C C'; l \<in> pre_tCFG.Paths CFGs (get_points (fst C'));
 safe_points CFGs (get_points (fst C)); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points (fst C) \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst C)) \<and>
 (\<forall>i<length l'. \<exists>C''. l' ! i = get_points (fst C'') \<and> (conc_step CFGs)^** C C'' \<and> (conc_step CFGs)^** C'' C')"
apply (induct arbitrary: l rule: rtranclp_induct, auto)
apply (rule_tac x="[]" in exI, simp)
apply (frule conc_step_increment_path, simp+)
apply (case_tac C, rule conc_steps_safe, simp+)
apply (subgoal_tac "\<exists>l'. hd (l' @ [get_points a]) = get_points (fst C) \<and> l' \<frown> [get_points a] \<frown> l \<in> 
 pre_tCFG.Paths CFGs (get_points (fst C)) \<and> (\<forall>i<length l'. \<exists>aa. l' ! i = get_points aa \<and> (\<exists>ba. 
 (conc_step CFGs)^** C (aa, ba) \<and> (conc_step CFGs)^** (aa, ba) (a, b)))", clarsimp)
apply (rule_tac x="l' @ [get_points a]" in exI, clarsimp)
apply (rule conjI, case_tac l', simp+)
apply clarsimp
   apply (case_tac "i = length l'", clarsimp)
apply (rule_tac x=a in exI, simp, rule_tac x=b in exI, simp)
apply (erule_tac x=i in allE, clarsimp)
apply (rule_tac x=aaa in exI, simp add: nth_append)
apply (rule_tac x=baa in exI, simp)
by (metis i_append_nth_Cons_0)
qed

lemma run_prog_path2: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>C0 mem0. start_state CFGs C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). 
    \<exists>i. l i = get_points (fst C) \<and> (\<forall>j<i. \<exists>C'. run_prog CFGs C' \<and> l j = get_points (fst C')))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>C0 mem0. start_state CFGs C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). 
    \<exists>i. l i = get_points (fst C) \<and> (\<forall>j<i. \<exists>C'. run_prog CFGs C' \<and> l j = get_points (fst C')))"
apply (clarsimp simp add: run_prog_def)
apply (cut_tac q="get_points (fst C)" in exists_path, clarsimp)
apply (drule conc_step_star_path2, simp+)
apply clarsimp
apply (rule conjI, force)
apply (rule_tac x="l' \<frown> l" in bexI, simp_all)
apply (rule_tac x="length l'" in exI, clarsimp)
by smt
qed

lemma run_prog_rpath: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>l. l \<in> pre_tCFG.RPaths CFGs (get_points (fst C))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>l. l \<in> pre_tCFG.RPaths CFGs (get_points (fst C))"
by (drule run_prog_path, simp, clarsimp, drule_tac i=i in reverse_path, simp, force)
qed

(* simulation relations and lifting *)
definition "lift_reach_sim_rel sim_rel CFGs CFGs' t C C' \<equiv> 
 run_prog CFGs C \<and> run_prog CFGs' C' \<and> (case (C, C') of ((states, mem), (states', mem')) \<Rightarrow>
 (\<exists>s s' G G'. states t = Some s \<and> states' t = Some s' \<and> CFGs t = Some G \<and> CFGs' t = Some G' \<and>
 sim_rel G G' (s, mem) (s', mem')) \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> states t' = states' t'))"

definition "add_reach CFGs CFGs' t sim_rel G G' c c' \<equiv> \<exists>S S'. S t = Some (fst c) \<and> 
 run_prog CFGs (S, snd c) \<and> S' t = Some (fst c') \<and> run_prog CFGs' (S', snd c') \<and> sim_rel G G' c c'"

lemma add_reach_sim_rel: "\<lbrakk>sim_rel G G' c c'; \<exists>S S'. S t = Some (fst c) \<and> run_prog CFGs (S, snd c) \<and> 
  S' t = Some (fst c') \<and> run_prog CFGs' (S', snd c')\<rbrakk> \<Longrightarrow>
 add_reach CFGs CFGs' t sim_rel G G' c c'"
by (simp add: add_reach_def)

end

locale sim_base = step_rel
  where free_set = "free_set :: 'memory \<Rightarrow> 'loc set" 
    and can_read = "can_read :: 'memory \<Rightarrow> 'thread \<Rightarrow> 'loc \<Rightarrow> 'val set"
    and start_state="start_state::('thread \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph) \<Rightarrow> 
  ('thread \<rightharpoonup> 'config) \<Rightarrow> 'memory \<Rightarrow> bool"
    and update_mem=
        "update_mem::'memory \<Rightarrow> ('thread, 'loc, 'val) access set \<Rightarrow> 'memory \<Rightarrow> bool"
    and step_rel = "step_rel ::
          'thread
           \<Rightarrow> ('node, 'edge_type, 'instr) flowgraph
              \<Rightarrow> 'memory \<Rightarrow> 'config \<Rightarrow> ('thread, 'loc, 'val) access set \<Rightarrow> 'config \<Rightarrow> bool"
    and start_mem = "start_mem:: 'memory"
  and get_point="get_point::'config \<Rightarrow> 'node"
  and instr_edges="instr_edges::'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq="Seq::'edge_type"+ 
  tCFG?: tCFG
   where CFGs="CFGs::('thread \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)"
   and instr_edges="instr_edges::'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq="Seq::'edge_type" + 
  tCFG': tCFG
   where CFGs="CFGs'::('thread \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)" 
   and instr_edges="instr_edges::'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq="Seq::'edge_type" 
  for free_set can_read step_rel get_point instr_edges Seq start_state update_mem start_mem CFGs CFGs' +
  assumes step_read_ops: "\<lbrakk>step_rel t G mem C ops C'; CFGs t = Some G; 
    \<forall>l\<in>get_ptrs ops. can_read mem t l = can_read mem' t l; free_set mem = free_set mem'\<rbrakk> \<Longrightarrow> 
    step_rel t G mem' C ops C'"
      and ops_thread: "\<lbrakk>step_rel t G mem state ops state'; CFGs t = Some G; a \<in> ops\<rbrakk> \<Longrightarrow> get_thread a = t"
begin

lemma sim_by_reachable_thread_mem_obs [rule_format]: 
"\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (=) G' G (one_step t) obs (get_mem o snd); 
 CFGs t = Some G; CFGs' t = Some G'; \<forall>t'. t' \<noteq> t \<longrightarrow> CFGs t' = CFGs' t'; \<forall>mem s mem' s'. 
 sim_rel G' G (s, mem) (s', mem') \<longrightarrow> (\<forall>S. run_prog CFGs' (S, mem) \<longrightarrow> (free_set mem = free_set mem' \<and> 
 (\<forall>t' ops s1 s2. run_prog CFGs' (S, mem) \<and> run_prog CFGs (S(t \<mapsto> s'), mem') \<and> S t = Some s \<and> 
 S t' = Some s1 \<and> t' \<noteq> t \<and> t' \<in> dom CFGs \<longrightarrow> (step_rel t' (the (CFGs t')) mem s1 ops s2  \<longrightarrow> 
 (\<forall>l\<in>get_ptrs ops. can_read mem t' l = can_read mem' t' l)) \<and> 
 (step_rel t' (the (CFGs t')) mem' s1 ops s2  \<longrightarrow> (\<forall>mem2. update_mem mem ops mem2 \<and> t \<notin> get_thread ` ops \<longrightarrow> 
 (\<exists>mem2'. update_mem mem' ops mem2' \<and> (\<forall>l\<in>obs. get_mem mem2' l = get_mem mem2 l) \<and> sim_rel G' G (s, mem2) (s', mem2')))))))\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs t) (=) CFGs' CFGs conc_step obs (get_mem o snd)"
apply (simp add: tCFG_sim_def, unfold_locales, clarsimp simp add: trsys_of_tCFG_def)
apply (rule conc_step.cases, simp+, clarsimp simp add: lift_reach_sim_rel_def)
apply (rule conjI, clarsimp)
apply (drule_tac sa="(C, mem)" and sb="(s', ba)" in simulation.simulation)
apply (clarsimp simp add: add_reach_def)
apply (rule_tac x=states in exI, simp, rule_tac x=aa in exI, simp)
apply (clarsimp simp add: trsys_of_tCFG_def)
apply (rule conjI, erule step_single, simp+)
apply (clarsimp simp add: trsys_of_tCFG_def add_reach_def)
apply (erule one_step.cases, clarsimp)
apply ((rule exI)+, rule context_conjI, rule_tac t=t in step_thread, simp add: dom_def, simp+)
apply (rule conjI, erule run_prog_step, simp+)
apply (erule run_prog_step, simp+)
apply clarsimp
apply (subgoal_tac "aa = states(t \<mapsto> s')", thin_tac "\<forall>t'. t' \<noteq> t \<longrightarrow> states t' = aa t'", 
 clarsimp)
   apply (erule_tac x=ta in allE)
   apply (erule_tac x = mem in allE)
   apply (erule_tac x = s in allE)
   apply (erule_tac x = mem' in allE)
  apply (erule_tac x = s' in allE)
  apply (erule impE, simp)
apply (erule_tac x=states in allE, clarsimp)
apply (erule_tac x=ta in allE, erule_tac x=ops in allE, erule_tac x=C in allE, simp, erule impE, 
  simp add: dom_def)
apply (erule_tac x=C' in allE, clarsimp)
apply (drule_tac mem=mem and mem'=ba in step_read_ops, simp+)
apply (erule_tac x=mem' in allE, clarsimp)
apply (erule impE, clarsimp)
apply (cut_tac t=ta in ops_thread, simp_all, simp+)
apply clarsimp
apply (rule exI, rule_tac x=mem2' in exI, rule context_conjI, rule_tac t=ta in step_thread, 
 simp add: dom_def, simp+)
apply (rule conjI, erule run_prog_conc_step, simp+)
apply (rule conjI, erule run_prog_conc_step, simp+)
apply (clarsimp intro!: ext simp add: restrict_map_def)
apply (rule ext, simp)
done

(* Slightly reorganized other-threads hypothesis. *)
lemma sim_by_reachable_thread_obs [rule_format]: 
"\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (=) G' G (one_step t) obs (get_mem o snd); 
 CFGs t = Some G; CFGs' t = Some G'; \<forall>t'. t' \<noteq> t \<longrightarrow> CFGs t' = CFGs' t'; 
 \<forall>mem s mem' s'. sim_rel G' G (s, mem) (s', mem') \<longrightarrow> (free_set mem = free_set mem' \<and> 
 (\<forall>t' ops s1 s2 S. run_prog CFGs' (S, mem) \<and> run_prog CFGs (S(t \<mapsto> s'), mem') \<and> 
 S t = Some s \<and> S t' = Some s1 \<and> t' \<noteq> t \<and> t' \<in> dom CFGs \<longrightarrow> 
 (step_rel t' (the (CFGs t')) mem s1 ops s2  \<longrightarrow> (\<forall>l\<in>get_ptrs ops. can_read mem t' l = can_read mem' t' l)) \<and>
 (step_rel t' (the (CFGs t')) mem' s1 ops s2  \<longrightarrow> (\<forall>mem2. update_mem mem ops mem2 \<and> t \<notin> get_thread ` ops \<longrightarrow> 
 (\<exists> mem2'. update_mem mem' ops mem2' \<and> (\<forall>l\<in>obs. get_mem mem2' l = get_mem mem2 l) \<and> sim_rel G' G (s, mem2) (s', mem2'))))))\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs t) (=) CFGs' CFGs conc_step obs (get_mem o snd)"
apply (rule sim_by_reachable_thread_mem_obs, simp+)
apply clarsimp
apply (erule_tac x=mem in allE, erule_tac x=s in allE, erule_tac x=mem' in allE, 
  erule_tac x=s' in allE, erule impE, assumption, clarsimp)
apply (erule_tac x=t' in allE, erule_tac x=ops in allE, erule_tac x=s1 in allE, erule impE)
apply (rule_tac x=S in exI, force)
apply (erule_tac x=s2 in allE, force)
done

lemma sim_by_reachable_thread [rule_format]: "\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (op =) 
 G' G (one_step t) UNIV (get_mem o snd); CFGs t = Some G; CFGs' t = Some G'; 
 \<forall>t'. t' \<noteq> t \<longrightarrow> CFGs t' = CFGs' t'; \<forall>mem s mem' s'. sim_rel G' G (s, mem) (s', mem') \<longrightarrow> 
 (free_set mem = free_set mem' \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> can_read mem t' = can_read mem' t') \<and>
 (\<forall>ops mem2. update_mem mem ops mem2 \<and> t \<notin> get_thread ` ops \<longrightarrow> 
 (\<exists>mem2'. update_mem mem' ops mem2' \<and> get_mem mem2' = get_mem mem2 \<and> sim_rel G' G (s, mem2) (s', mem2'))))\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs t) (op =) CFGs' CFGs conc_step UNIV (get_mem o snd)"
apply (erule sim_by_reachable_thread_obs, auto simp add: fun_upd_def)
by (smt UNIV_I UNIV_eq_I domD domI)

lemma sim_no_mem [rule_format]: "\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (op =) 
 G' G (one_step t) UNIV (get_mem o snd); CFGs t = Some G; CFGs' t = Some G'; 
 \<forall>t'. t' \<noteq> t \<longrightarrow> CFGs t' = CFGs' t'; \<forall>mem s mem' s'. sim_rel G' G (s, mem) (s', mem') \<longrightarrow> mem = mem';
 \<forall>s s' mem ops mem'. sim_rel G' G (s, mem) (s', mem) \<and> t \<notin> get_thread ` ops \<and> update_mem mem ops mem' \<longrightarrow>
 sim_rel G' G (s, mem') (s', mem')\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs t) (op =) CFGs' CFGs conc_step UNIV (get_mem o snd)"
by (rule sim_by_reachable_thread, simp+, metis)

end

end
