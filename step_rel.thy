theory step_rel
imports memory_model trans_sim
begin

locale step_rel = memory_model
 where actions =  "actions :: (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action set"
    and locations = "locations :: loc_type set"
    and actionIDs = "actionIDs :: aid_type set"
    and times = "times :: time_type set"
    and threads = "threads :: 'tid set"
    and locks = "locks :: 'lock set"
    and names = "names :: 'name set"
    and callIDs = "callIDs :: 'callID set" 
    and free_set = "free_set:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
             \<Rightarrow> time_type \<Rightarrow> loc_type set"
    and can_read = "can_read:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
                 \<Rightarrow> 'tid \<Rightarrow> time_type \<Rightarrow> loc_type \<Rightarrow> 'val set"
    and update_mem = "update_mem:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
                       \<Rightarrow> time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                             (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) set
                        \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool"
    and start_mem = "start_mem:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
  for actions locations actionIDs times threads locks names callIDs 
         free_set can_read update_mem start_mem +
  fixes step_rel::"'tid \<Rightarrow> time_type \<Rightarrow> ('node, 'edge_type, 'instr) flowgraph \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> 'config \<Rightarrow> 
   ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) set \<Rightarrow> 'config \<Rightarrow> bool"
  and start_state::"('tid \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)
                                \<Rightarrow> time_type \<Rightarrow> ('tid \<rightharpoonup> 'config) \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool"
  and get_point::"'config \<Rightarrow> 'node"
  and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq::'edge_type
  assumes start_points [simp]: "start_state CFGs t S m
         \<Longrightarrow> (\<lambda> x . case S x of Some a \<Rightarrow> (\<lambda>C. Some (get_point C)) a 
                              | None \<Rightarrow> None) = start_points CFGs"
      and step_along_edge: "\<lbrakk>step_rel tid t G m C ops C'; is_flowgraph G Seq instr_edges; get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> 
    \<exists>ty. (get_point C, get_point C', ty) \<in> Edges (G::('node, 'edge_type, 'instr) flowgraph)"

begin

lemma step_safe: "\<lbrakk>step_rel tid t G m C ops C'; is_flowgraph G Seq instr_edges; get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> 
    get_point C' \<in> Nodes G"
by (drule step_along_edge, simp+, simp add: is_flowgraph_def flowgraph_def pointed_graph_def)

abbreviation "well_formed G \<equiv> is_flowgraph G Seq instr_edges"

inductive one_step where
step_single [intro!]: "\<lbrakk>step_rel tid t G mem C ops C'; update_mem mem t ops mem'\<rbrakk> \<Longrightarrow> 
  one_step tid G (t,C, mem) (Suc t,C', mem')"

lemma one_step_safe: "\<lbrakk>one_step tid G (t,C, mem) (t',C', mem'); well_formed G; get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  get_point C' \<in> Nodes G"
by (erule one_step.cases, rule step_safe, simp+)

lemma one_step_along_edge: "\<lbrakk>one_step tid G (t,C, m) (t',C', m'); is_flowgraph G Seq instr_edges; 
  get_point C \<in> Nodes G\<rbrakk> \<Longrightarrow> \<exists>ty. (get_point C, get_point C', ty) \<in> Edges G"
by (erule one_step.cases, rule step_along_edge, simp+)

inductive conc_step where
step_thread [intro]: "\<lbrakk>CFGs tid = Some G; states tid = Some C; step_rel tid t G mem C ops C'; 
  update_mem mem t ops mem'\<rbrakk> \<Longrightarrow> conc_step CFGs (t,states, mem) (Suc t,states(tid \<mapsto> C'), mem')"

abbreviation "get_points (S::'tid \<rightharpoonup> 'config) \<equiv>
                  (\<lambda> x . case S x of Some a \<Rightarrow> (\<lambda>C. Some (get_point C)) a 
                              | None \<Rightarrow> None)"

lemma one_step_conc_step: "\<lbrakk>one_step tid G (t,C, m) (t',C', m'); CFGs tid = Some G; states tid = Some C\<rbrakk> \<Longrightarrow> 
  conc_step CFGs (t,states, m) (t',states(tid \<mapsto> C'), m')"
  apply (erule one_step.cases)
  by blast

term "safe_points"

lemma conc_step_safe: "\<lbrakk>conc_step CFGs (t,states, mem) (t',states', mem'); tCFG CFGs instr_edges Seq; 
  safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points states')"
apply (erule conc_step.cases, clarsimp simp add: safe_points_def)
apply (case_tac "t = t", clarsimp)
apply (rule step_safe, simp+)
apply (erule tCFG.CFGs, simp)
apply force
apply (force simp add: map_comp_def)
done

lemma conc_steps_safe: "\<lbrakk>(conc_step CFGs)^** (t,states, mem) (t',states', mem'); tCFG CFGs instr_edges Seq; 
  safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points states')"
by (drule_tac P="\<lambda>(t,states, mem) (t',states', mem'). safe_points CFGs (get_points states) \<longrightarrow> 
  safe_points CFGs (get_points states')" in rtranclp.induct, auto intro: conc_step_safe)

definition "run_prog CFGs C \<equiv> \<exists>t C0 mem0. start_state CFGs t C0 mem0 \<and> (conc_step CFGs)^** (t,C0, mem0) C"

lemma run_progI [intro]: "\<lbrakk>start_state CFGs t C0 mem0; (conc_step CFGs)^** (t,C0, mem0) C\<rbrakk> \<Longrightarrow> 
  run_prog CFGs C"
by (force simp add: run_prog_def)

lemma run_prog_conc_step [intro]: "\<lbrakk>run_prog CFGs C; conc_step CFGs C C'\<rbrakk> \<Longrightarrow> run_prog CFGs C'"
  by (meson rtranclp.rtrancl_into_rtrancl run_prog_def)

lemma run_prog_conc_steps [intro]: "\<lbrakk>run_prog CFGs C; (conc_step CFGs)^** C C'\<rbrakk> \<Longrightarrow> run_prog CFGs C'"
  by (meson rtranclp_trans run_prog_def)

lemma run_prog_induct [elim]: "\<lbrakk>run_prog CFGs C; \<And>t C0 mem0. start_state CFGs t C0 mem0 \<Longrightarrow> P (t,C0, mem0); 
 \<And>C C'. run_prog CFGs C \<Longrightarrow> P C \<Longrightarrow> conc_step CFGs C C' \<Longrightarrow> P C'\<rbrakk> \<Longrightarrow> P C"
apply (clarsimp simp add: run_prog_def)
  by (smt conc_step.cases rtranclp_induct)

lemma run_prog_one_step: "\<lbrakk>run_prog CFGs (t,S, mem); S tid = Some s; CFGs tid = Some G;
 one_step tid G (t,s, mem) (t',s', mem')\<rbrakk> \<Longrightarrow> run_prog CFGs (t',S(tid \<mapsto> s'), mem')"
  apply (erule run_prog_conc_step)
  by (simp add: one_step_conc_step)

lemma run_prog_one_steps: "\<lbrakk>run_prog CFGs (t,S, mem); S tid = Some s; CFGs tid = Some G;
 (one_step tid G)^** (t,s, mem) (t',s', mem')\<rbrakk> \<Longrightarrow> run_prog CFGs (t',S(tid \<mapsto> s'), mem')"
apply (drule_tac P="\<lambda>(t,s, mem) (t',s', mem'). run_prog CFGs (t,S, mem) \<and> S tid = Some s \<and> CFGs tid = Some G \<longrightarrow> 
  run_prog CFGs (t',S(tid \<mapsto> s'), mem')" in rtranclp.induct, auto simp add: map_upd_triv)
apply (drule_tac mem=ba in run_prog_one_step, simp+, force, simp+)
done

lemma run_prog_step: "\<lbrakk>run_prog CFGs (t,S, mem); S tid = Some s; CFGs tid = Some G;
 step_rel tid t G mem s ops s'; update_mem mem t ops mem'\<rbrakk> \<Longrightarrow> run_prog CFGs (Suc t,S(tid \<mapsto> s'), mem')"
  by (erule run_prog_one_step, auto)

lemma run_prog_safe: "\<lbrakk>run_prog CFGs (t,S, mem); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points S)"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs (t,S, mem); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  safe_points CFGs (get_points S)"
by (clarsimp simp add: run_prog_def, rule conc_steps_safe, simp+)
qed

(* paths *)
lemma step_increment_path: "\<lbrakk>step_rel tid t G m C a C'; tCFG CFGs instr_edges Seq; CFGs tid = Some G; 
  l \<in> pre_tCFG.Paths CFGs ps; p = get_point C; p' = get_point C'; ps tid = Some p'; p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  [ps(tid \<mapsto> p)] \<frown> l \<in> pre_tCFG.Paths CFGs (ps(tid \<mapsto> p))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>step_rel tid t G m C a C'; tCFG CFGs instr_edges Seq; CFGs tid = Some G; 
  l \<in> pre_tCFG.Paths CFGs ps; p = get_point C; p' = get_point C'; ps tid = Some p'; p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  [ps(tid \<mapsto> p)] \<frown> l \<in> pre_tCFG.Paths CFGs (ps(tid \<mapsto> p))"
apply (rule pre_tCFG.path_incremental_gen, unfold_locales, simp)
apply (frule step_along_edge)
apply (erule tCFG.CFGs, simp+)
done
qed

lemma step_increment_rpath: "\<lbrakk>step_rel tid t G m C a C'; tCFG CFGs instr_edges Seq; CFGs tid = Some G; 
  l \<in> pre_tCFG.RPaths CFGs ps; p0 = get_point C; p = get_point C'; ps tid = Some p0; p0 \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 [ps(tid \<mapsto> p)] \<frown> l \<in> pre_tCFG.RPaths CFGs (ps(tid \<mapsto> p))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>step_rel tid t G m C a C'; tCFG CFGs instr_edges Seq; CFGs tid = Some G; 
  l \<in> pre_tCFG.RPaths CFGs ps; p0 = get_point C; p = get_point C'; ps tid = Some p0; p0 \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 [ps(tid \<mapsto> p)] \<frown> l \<in> pre_tCFG.RPaths CFGs (ps(tid \<mapsto> p))"
apply (rule rpath_incremental_gen, simp+, clarsimp)
apply (frule step_along_edge)
apply (erule tCFG.CFGs, simp+)
done
qed

lemma one_step_increment_path: "\<lbrakk>one_step tid G (t,C, m) (t',C', m'); tCFG CFGs instr_edges Seq; CFGs tid = Some G; 
  l \<in> pre_tCFG.Paths CFGs ps; p = get_point C; p' = get_point C'; ps tid = Some p'; p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  [ps(tid \<mapsto> p)] \<frown> l \<in> pre_tCFG.Paths CFGs (ps(tid \<mapsto> p))"
by (erule one_step.cases, rule step_increment_path, simp+)

lemma one_step_increment_rpath: "\<lbrakk>one_step tid G (t,C, m) (t',C', m'); tCFG CFGs instr_edges Seq; CFGs tid = Some G; 
  l \<in> pre_tCFG.RPaths CFGs ps; p0 = get_point C; p = get_point C'; ps tid = Some p0; p0 \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 [ps(tid \<mapsto> p)] \<frown> l \<in> pre_tCFG.RPaths CFGs (ps(tid \<mapsto> p))"
by (erule one_step.cases, rule step_increment_rpath, simp+)

lemma conc_step_increment_path: "\<lbrakk>conc_step CFGs C C'; tCFG CFGs instr_edges Seq; 
  l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C'))); safe_points CFGs (get_points (fst (snd C)))\<rbrakk> \<Longrightarrow> 
 [get_points (fst (snd C))] \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C)))"
apply (auto elim!: conc_step.cases)
apply (frule_tac ps="get_points (states(tid \<mapsto> C'a))" in step_increment_path, auto simp add: safe_points_def)
apply force
apply (subgoal_tac "get_points (states(tid \<mapsto> C'a))(tid \<mapsto> get_point Ca) = get_points states", simp)
apply (rule ext, clarsimp simp add: map_comp_def)
done

lemma conc_steps_path: "\<lbrakk>(conc_step CFGs)^** (t,states, mem) (t',states', mem'); tCFG CFGs instr_edges Seq; 
  l \<in> pre_tCFG.Paths CFGs (get_points states'); safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points states \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points states)"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>(conc_step CFGs)^** (t,states, mem) (t',states', mem'); tCFG CFGs instr_edges Seq; 
  l \<in> pre_tCFG.Paths CFGs (get_points states'); safe_points CFGs (get_points states)\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points states \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points states)"
apply (drule_tac P="\<lambda>(t,states, mem) (t',states', mem'). \<forall>l. l \<in> pre_tCFG.Paths CFGs (get_points states') \<and> 
  safe_points CFGs (get_points states) \<longrightarrow> (\<exists>l'. hd (l' @ [l 0]) = get_points states \<and> 
  l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points states))" in rtranclp.induct, auto)
apply (rule_tac x="[]" in exI, simp)
apply (drule conc_step_increment_path, simp+)
apply (drule conc_steps_safe, simp+)
by (metis append_is_Nil_conv hd_append2 i_append_assoc i_append_nth_Cons_0 not_Cons_self2)
qed

lemma run_prog_path: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>t C0 mem0. start_state CFGs t C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). \<exists>i. l i = get_points (fst (snd C)))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>t C0 mem0. start_state CFGs t C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). \<exists>i. l i = get_points (fst (snd C)))"
apply (clarsimp simp add: run_prog_def)
apply (cut_tac q="get_points (fst (snd C))" in exists_path, clarsimp)
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
apply (rule_tac x="l @ [(a,aa, b)]" in exI, clarsimp)
apply (rule conjI, case_tac l, simp+)
apply clarsimp
apply (case_tac "i = length l", clarsimp simp add: nth_append)
apply (erule_tac x=i in allE, auto simp add: nth_append)
done

lemma step_star_path: "\<lbrakk>hd (l' @ [C']) = C; \<forall>i<length l'. conc_step CFGs (l' ! i) ((l' @ [C']) ! Suc i);
 l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C'))); safe_points CFGs (get_points (fst (snd C))); 
          tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 map (get_points o (\<lambda> x . fst (snd x))) l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C)))"
apply (induct l' arbitrary: C l, auto)
apply (case_tac l', auto)
apply (drule conc_step_increment_path, simp+)
apply (subgoal_tac "(get_points aa # map (get_points \<circ> (\<lambda> x . fst (snd x))) list) \<frown> l \<in> pre_tCFG.Paths CFGs (get_points aa)")
   apply (erule_tac x=0 in allE,clarsimp)
apply (drule conc_step_increment_path, simp+)
apply (subgoal_tac "\<forall>i<Suc (length list). conc_step CFGs (((a, aa, b) # list) ! i) ((list @ [C']) ! i)")
apply (subgoal_tac "safe_points CFGs (get_points aa)")
apply (erule_tac x=0 in allE, clarsimp, rule conc_step_safe, auto)
done

lemma run_prog_steps: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l t C0 mem0. start_state CFGs t C0 mem0 \<and> 
 (\<forall>i<length l. conc_step CFGs (l ! i) ((l @ [C]) ! Suc i)) \<and>
 (\<exists>l'\<in>pre_tCFG.Paths CFGs (get_points (fst (snd C))).
                 map (get_points o (\<lambda> x . fst (snd x))) l \<frown> l' \<in> pre_tCFG.Paths CFGs (start_points CFGs))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l t C0 mem0. start_state CFGs t C0 mem0 \<and> 
 (\<forall>i<length l. conc_step CFGs (l ! i) ((l @ [C]) ! Suc i)) \<and>
 (\<exists>l'\<in>pre_tCFG.Paths CFGs (get_points (fst (snd C))).
           map (get_points o (\<lambda> x . fst (snd x))) l \<frown> l' \<in> pre_tCFG.Paths CFGs (start_points CFGs))"
apply (clarsimp simp add: run_prog_def)
apply (drule conc_step_star_steps, clarsimp)
apply (cut_tac q="get_points (fst (snd C))" in exists_path, clarsimp)
apply (frule step_star_path, simp+)
apply (rule conjI, force+)
done
qed

lemma conc_step_star_path2: "\<lbrakk>(conc_step CFGs)^** C C'; l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C')));
 safe_points CFGs (get_points (fst (snd C))); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points (fst (snd C)) \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C))) \<and>
 (\<forall>i<length l'. \<exists>C''. l' ! i = get_points (fst (snd C'')) \<and> (conc_step CFGs)^** C C'' \<and> (conc_step CFGs)^** C'' C')"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>(conc_step CFGs)^** C C'; l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C')));
 safe_points CFGs (get_points (fst (snd C))); tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
 \<exists>l'. hd (l' @ [l 0]) = get_points (fst (snd C)) \<and> l' \<frown> l \<in> pre_tCFG.Paths CFGs (get_points (fst (snd C))) \<and>
 (\<forall>i<length l'. \<exists>C''. l' ! i = get_points (fst (snd C'')) \<and> (conc_step CFGs)^** C C'' \<and> (conc_step CFGs)^** C'' C')"
apply (induct arbitrary: l rule: rtranclp_induct, auto)
apply (rule_tac x="[]" in exI, simp)
apply (frule conc_step_increment_path, simp+)
apply (case_tac C, rule conc_steps_safe, simp+)
apply (subgoal_tac "\<exists>l'. hd (l' @ [get_points aa]) = get_points (fst (snd C)) \<and> l' \<frown> [get_points aa] \<frown> l \<in> 
 pre_tCFG.Paths CFGs (get_points (fst (snd C))) \<and> (\<forall>i<length l'. \<exists>ab ac. l' ! i = get_points ac \<and> (\<exists>ba. 
 (conc_step CFGs)^** C (ab, ac, ba) \<and> (conc_step CFGs)^** (ab, ac, ba) (a,aa, b)))", clarsimp)
apply (rule_tac x="l' @ [get_points aa]" in exI, clarsimp)
apply (rule conjI, case_tac l', simp+)
apply clarsimp
   apply (case_tac "i = length l'", clarsimp)
  apply (rule_tac x =a in exI)
apply (rule_tac x=aa in exI, simp, rule_tac x=b in exI, simp)
   apply (erule_tac x=i in allE, clarsimp)
  apply (rule_tac x = aba in exI)
apply (rule_tac x=aca in exI, simp add: nth_append)
apply (rule_tac x=baa in exI, simp)
  by blast
qed

lemma run_prog_path2: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>t C0 mem0. start_state CFGs t C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). 
    \<exists>i. l i = get_points (fst (snd C)) \<and> (\<forall>j<i. \<exists>C'. run_prog CFGs C' \<and> l j = get_points (fst (snd C'))))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>t C0 mem0. start_state CFGs t C0 mem0 \<and> (\<exists>l\<in>pre_tCFG.Paths CFGs (start_points CFGs). 
    \<exists>i. l i = get_points (fst (snd C)) \<and> (\<forall>j<i. \<exists>C'. run_prog CFGs C' \<and> l j = get_points (fst (snd C'))))"
apply (clarsimp simp add: run_prog_def)
apply (cut_tac q="get_points (fst (snd C))" in exists_path, clarsimp)
apply (drule conc_step_star_path2, simp+)
apply clarsimp
apply (rule conjI, force)
apply (rule_tac x="l' \<frown> l" in bexI, simp_all)
apply (rule_tac x="length l'" in exI, clarsimp)
by smt
qed

lemma run_prog_rpath: "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>l. l \<in> pre_tCFG.RPaths CFGs (get_points (fst (snd C)))"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>run_prog CFGs C; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  \<exists>l. l \<in> pre_tCFG.RPaths CFGs (get_points (fst (snd C)))"
by (drule run_prog_path, simp, clarsimp, drule_tac i=i in reverse_path, simp, force)
qed

(* simulation relations and lifting *)
definition "lift_reach_sim_rel sim_rel CFGs CFGs' tid C C' \<equiv> 
 run_prog CFGs C \<and> run_prog CFGs' C' \<and> (case (C, C') of ((t,states, mem), (t',states', mem')) \<Rightarrow>
 (\<exists>s s' G G'. states tid = Some s \<and> states' tid = Some s' \<and> CFGs tid = Some G \<and> CFGs' tid = Some G' \<and>
 sim_rel G G' (t,s, mem) (t',s', mem')) \<and> (\<forall>tid'. tid' \<noteq> tid \<longrightarrow> states tid' = states' tid'))"

definition "add_reach CFGs CFGs' tid sim_rel G G' c c' \<equiv> \<exists>S S'. S tid = Some (fst (snd c)) \<and> 
 run_prog CFGs (fst c, S, snd (snd c)) \<and> S' tid = Some (fst (snd c'))
         \<and> run_prog CFGs' (fst c', S', snd (snd c')) \<and> sim_rel G G' c c'"

lemma add_reach_sim_rel: "\<lbrakk>sim_rel G G' c c'; \<exists>S S'. S tid = Some (fst (snd c)) \<and> run_prog CFGs (fst c, S, snd (snd c)) \<and> 
  S' tid = Some (fst (snd c')) \<and> run_prog CFGs' (fst c',S', snd (snd c'))\<rbrakk> \<Longrightarrow>
 add_reach CFGs CFGs' tid sim_rel G G' c c'"
by (simp add: add_reach_def)

end

fun acLoc' where
"acLoc' (x,y,z) = (case acLoc z of None \<Rightarrow> 0 | Some v \<Rightarrow> v)"

abbreviation "get_ptrs S \<equiv> acLoc' ` S"
abbreviation "get_thread a \<equiv> (\<lambda> (x,y,z) . x) a"

locale sim_base = step_rel
  where actions =  "actions :: (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action set"
    and locations = "locations :: loc_type set"
    and actionIDs = "actionIDs :: aid_type set"
    and times = "times :: time_type set"
    and threads = "threads :: 'tid set"
    and locks = "locks :: 'lock set"
    and names = "names :: 'name set"
    and callIDs = "callIDs :: 'callID set" 
    and free_set = "free_set:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
             \<Rightarrow> time_type \<Rightarrow> loc_type set"
    and can_read = "can_read:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
                 \<Rightarrow> 'tid \<Rightarrow> time_type \<Rightarrow> loc_type \<Rightarrow> 'val set"
    and update_mem = "update_mem:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
                       \<Rightarrow> time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                             (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) set
                        \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool"
    and start_mem = "start_mem:: (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
  and step_rel = "step_rel::'tid \<Rightarrow> time_type \<Rightarrow> ('node, 'edge_type, 'instr) flowgraph \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> 'config \<Rightarrow> 
   ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) set \<Rightarrow> 'config \<Rightarrow> bool"
  and start_state = "start_state ::
                    ('tid \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)
                                \<Rightarrow> time_type \<Rightarrow> ('tid \<rightharpoonup> 'config) \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool"
  and get_point = "get_point::'config \<Rightarrow> 'node"
  and instr_edges = "instr_edges:: 'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq = "Seq :: 'edge_type"
 +tCFG? : tCFG
   where CFGs="CFGs::('tid \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)"
   and instr_edges="instr_edges::'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq="Seq::'edge_type" + 
  tCFG': tCFG
   where CFGs="CFGs'::('tid \<rightharpoonup> ('node, 'edge_type, 'instr) flowgraph)" 
   and instr_edges="instr_edges::'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
  and Seq="Seq::'edge_type" 
  for actions locations actionIDs times threads locks names callIDs 
         free_set can_read update_mem start_mem step_rel start_state get_point instr_edges Seq
          CFGs CFGs' +
  assumes step_read_ops: "\<lbrakk>step_rel tid t G mem C ops C'; CFGs tid = Some G; 
    \<forall>l\<in>get_ptrs ops. can_read mem tid t l = can_read mem' tid t l; free_set mem = free_set mem'\<rbrakk> \<Longrightarrow> 
    step_rel tid t G mem' C ops C'"
      and ops_thread: "\<lbrakk>step_rel tid t G mem state ops state'; CFGs tid = Some G; a \<in> ops\<rbrakk>
                      \<Longrightarrow> get_thread a = tid"


begin

thm step_thread

lemma sim_by_reachable_thread_mem_obs [rule_format]: 
"\<lbrakk>tCFG_sim (add_reach CFGs' CFGs tid sim_rel G' G) (=) G' G (one_step tid) obs (get_mem o (\<lambda> x . snd (snd x))); 
 CFGs tid = Some G; CFGs' tid = Some G'; \<forall>tid'. tid' \<noteq> tid \<longrightarrow> CFGs tid' = CFGs' tid'; \<forall>t mem s t' mem' s'. 
 sim_rel G' G (t,s, mem) (t',s', mem') \<longrightarrow> (\<forall>S. run_prog CFGs' (t,S, mem) \<longrightarrow> (free_set mem = free_set mem' \<and> 
 (\<forall>tid' ops s1 s2. run_prog CFGs' (t,S, mem) \<and> run_prog CFGs (t',S(tid \<mapsto> s'), mem') \<and> S tid = Some s \<and> 
 S tid' = Some s1 \<and> tid' \<noteq> tid \<and> tid' \<in> dom CFGs \<longrightarrow> (step_rel tid' t' (the (CFGs tid')) mem s1 ops s2  \<longrightarrow> 
 (\<forall>l\<in>get_ptrs ops. can_read mem tid' t l = can_read mem' tid' t' l)) \<and> 
 (step_rel tid' t' (the (CFGs tid')) mem' s1 ops s2  \<longrightarrow> (\<forall>mem2. update_mem mem t ops mem2 \<and> tid \<notin> get_thread ` ops \<longrightarrow> 
 (\<exists>mem2'. update_mem mem' t' ops mem2' \<and> (\<forall>l\<in>obs. get_mem mem2' l = get_mem mem2 l)
       \<and> sim_rel G' G (t,s, mem2) (t',s', mem2')))))))\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs tid) (=) CFGs' CFGs conc_step obs (get_mem o (\<lambda> x . snd (snd x)))"
apply (simp add: tCFG_sim_def, unfold_locales, clarsimp simp add: trsys_of_tCFG_def)
apply (rule conc_step.cases, simp+, clarsimp simp add: lift_reach_sim_rel_def)
apply (rule conjI, clarsimp)
apply (drule_tac sa="(t,C, mem)" and sb="(ab,s', ba)" in simulation.simulation)
     apply (clarsimp simp add: add_reach_def)
apply (rule_tac x=states in exI, simp, rule_tac x=ac in exI, simp)
apply (clarsimp simp add: trsys_of_tCFG_def)
apply (rule conjI, erule step_single, simp+)
apply (clarsimp simp add: trsys_of_tCFG_def add_reach_def)
   apply (erule one_step.cases, clarsimp)
  apply ((rule exI)+, rule context_conjI)
    apply (rule_tac tid=tid in step_thread)
    apply (simp add: dom_def, simp+)
   apply (rule conjI,erule run_prog_step,simp+)
apply (erule run_prog_step, simp+)
apply clarsimp
  apply (subgoal_tac "ac = states(tid \<mapsto> s')")
  apply (thin_tac "\<forall>tid'. tid' \<noteq> tid \<longrightarrow> states tid' = ac tid'", clarsimp)
   apply(erule_tac x = tida in allE)
   apply (erule_tac x = t in allE)
   apply (erule_tac x = mem in allE)
  apply (erule_tac x = s in allE)
   apply (erule_tac x = ab in allE)
   apply (erule_tac x = ba in allE)
  apply (erule_tac x = s' in allE)
   apply (erule impE, simp)
  apply (erule impE,simp)
apply (erule_tac x=states in allE, clarsimp)
apply (erule_tac x=tida in allE, erule_tac x=ops in allE, erule_tac x=C in allE, simp, erule impE, 
  simp add: dom_def)
apply (erule_tac x=C' in allE, clarsimp)
   apply (drule_tac mem=mem and mem'=ba in step_read_ops,simp,clarsimp)
     apply (case_tac "acLoc b",clarsimp)
  sorry
(*apply (erule_tac x=mem' in allE, clarsimp)
apply (erule impE, clarsimp)
apply (cut_tac t=ta in ops_thread, simp_all, simp+)
apply clarsimp
apply (rule exI, rule_tac x=mem2' in exI, rule context_conjI, rule_tac t=ta in step_thread, 
 simp add: dom_def, simp+)
apply (rule conjI, erule run_prog_conc_step, simp+)
apply (rule conjI, erule run_prog_conc_step, simp+)
apply (clarsimp intro!: ext simp add: restrict_map_def)
apply (rule ext, simp)
done*)

(* Slightly reorganized other-threads hypothesis. *)
lemma sim_by_reachable_thread_obs [rule_format]: 
"\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (=) G' G (one_step tid) obs (get_mem o (\<lambda> x . snd (snd x))); 
 CFGs tid = Some G; CFGs' tid = Some G'; \<forall>tid'. tid' \<noteq> tid \<longrightarrow> CFGs tid' = CFGs' tid'; 
 \<forall>t mem s t' mem' s'. sim_rel G' G (t,s, mem) (t',s', mem') \<longrightarrow> (free_set mem = free_set mem' \<and> 
 (\<forall>tid' ops s1 s2 S. run_prog CFGs' (t,S, mem) \<and> run_prog CFGs (t',S(tid \<mapsto> s'), mem') \<and> 
 S tid = Some s \<and> S tid' = Some s1 \<and> tid' \<noteq> tid \<and> tid' \<in> dom CFGs \<longrightarrow> 
 (step_rel tid' t' (the (CFGs tid')) mem s1 ops s2
    \<longrightarrow> (\<forall>l\<in>get_ptrs ops. can_read mem tid' t l = can_read mem' tid' t' l)) \<and>
 (step_rel tid' t' (the (CFGs tid')) mem' s1 ops s2
   \<longrightarrow> (\<forall>mem2. update_mem mem t ops mem2 \<and> tid \<notin> get_thread ` ops \<longrightarrow> 
 (\<exists>mem2'. update_mem mem' t ops mem2'
      \<and> (\<forall>l\<in>obs. get_mem mem2' l = get_mem mem2 l) \<and> sim_rel G' G (t,s, mem2) (t',s', mem2'))))))\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs tid) (=) CFGs' CFGs conc_step obs (get_mem o (\<lambda> x . snd (snd x)))"
  apply (rule sim_by_reachable_thread_mem_obs, simp+)
  sorry

(*
apply clarsimp
apply (erule_tac x=mem in allE, erule_tac x=s in allE, erule_tac x=mem' in allE, 
  erule_tac x=s' in allE, erule impE, assumption, clarsimp)
apply (erule_tac x=t' in allE, erule_tac x=ops in allE, erule_tac x=s1 in allE, erule impE)
apply (rule_tac x=S in exI, force)
apply (erule_tac x=s2 in allE, force)
done

lemma sim_by_reachable_thread [rule_format]: "\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (=) 
 G' G (one_step t) UNIV (get_mem o snd); CFGs t = Some G; CFGs' t = Some G'; 
 \<forall>t'. t' \<noteq> t \<longrightarrow> CFGs t' = CFGs' t'; \<forall>mem s mem' s'. sim_rel G' G (s, mem) (s', mem') \<longrightarrow> 
 (free_set mem = free_set mem' \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> can_read mem t' = can_read mem' t') \<and>
 (\<forall>ops mem2. update_mem mem ops mem2 \<and> t \<notin> get_thread ` ops \<longrightarrow> 
 (\<exists>mem2'. update_mem mem' ops mem2' \<and> get_mem mem2' = get_mem mem2 \<and> sim_rel G' G (s, mem2) (s', mem2'))))\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs t) (=) CFGs' CFGs conc_step UNIV (get_mem o snd)"
apply (erule sim_by_reachable_thread_obs, auto simp add: fun_upd_def)
by (smt UNIV_I UNIV_eq_I domD domI)

lemma sim_no_mem [rule_format]: "\<lbrakk>tCFG_sim (add_reach CFGs' CFGs t sim_rel G' G) (=) 
 G' G (one_step t) UNIV (get_mem o snd); CFGs t = Some G; CFGs' t = Some G'; 
 \<forall>t'. t' \<noteq> t \<longrightarrow> CFGs t' = CFGs' t'; \<forall>mem s mem' s'. sim_rel G' G (s, mem) (s', mem') \<longrightarrow> mem = mem';
 \<forall>s s' mem ops mem'. sim_rel G' G (s, mem) (s', mem) \<and> t \<notin> get_thread ` ops \<and> update_mem mem ops mem' \<longrightarrow>
 sim_rel G' G (s, mem') (s', mem')\<rbrakk> \<Longrightarrow> 
 tCFG_sim (lift_reach_sim_rel sim_rel CFGs' CFGs t) (=) CFGs' CFGs conc_step UNIV (get_mem o snd)"
by (rule sim_by_reachable_thread, simp+, metis)

*)
end

end
