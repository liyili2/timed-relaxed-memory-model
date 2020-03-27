(* trans_semantics.thy *)
(* William Mansky *)
(* Semantics for the revised specification language PTRANS. *)

theory trans_semantics
imports trans_flowgraph
begin

(* matches a total valuation of metavariables with a partial one *)
definition part_matches where "part_matches \<sigma> t \<equiv> \<forall>x y. t x = Some y \<longrightarrow> \<sigma> x = y"

(* extends a partial valuation with another valuation over a given domain *)
definition part_extend where "part_extend t d \<sigma> \<equiv> \<lambda>x. if x\<in>d then Some (\<sigma> x) else t x"

(* The pieces that must be provided by the target language to give semantics to transformations. *) 
locale TRANS_basics = (* give SCEx a type annotation, parameterize by 'valuation? *)
  fixes subst::"(('thread, ('node, 'edge_type, 'instr) flowgraph) map) \<Rightarrow> ('metavar \<Rightarrow> 'object) \<Rightarrow> 'pattern \<rightharpoonup> 'instr"
    and node_subst::"(('thread, ('node, 'edge_type, 'instr) flowgraph) map) \<Rightarrow> ('metavar \<Rightarrow> 'object) \<Rightarrow> 
                     'metavar node_lit \<rightharpoonup> 'node"
    and type_subst::"('metavar \<Rightarrow> 'object) \<Rightarrow> 'edge_type_expr \<rightharpoonup> 'edge_type"
    and pred_fv::"'pred \<Rightarrow> 'metavar set"
    and eval_pred::"(('thread, ('node, 'edge_type, 'instr) flowgraph) map) \<Rightarrow> ('thread, 'node) map \<Rightarrow> 
                    ('metavar \<Rightarrow> 'object) \<Rightarrow> 'pred \<Rightarrow> bool"
    and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set" 
    and Seq::'edge_type
  assumes infinite_nodes [simp]: "\<not>finite (UNIV::'node set)"
      and infinite_mvars [simp]: "\<not>finite (UNIV::'metavar set)"
      and pred_same_subst: "\<lbrakk>\<forall>x\<in>pred_fv p. \<sigma> x = \<sigma>' x; pre_tCFG CFGs\<rbrakk> \<Longrightarrow> 
 eval_pred CFGs q \<sigma> p = eval_pred CFGs q \<sigma>' p"
begin

lemmas fresh_nodes = infinite_nodes [THEN fresh_new]
lemmas fresh_mvars = infinite_mvars [THEN fresh_new]

primrec subst_list where
"subst_list G \<sigma> [] = Some []" | 
"subst_list G \<sigma> (p # rest) = (case (subst G \<sigma> p, subst_list G \<sigma> rest) of 
   (Some i, Some irest) \<Rightarrow> Some (i # irest) | _ \<Rightarrow> None)"

primrec models where
"models _ _ _ SCTrue = True" |
"models CFGs \<sigma> q (SCPred p) = eval_pred CFGs q \<sigma> p" |
"models CFGs \<sigma> q (\<phi>1 \<and>sc \<phi>2) = (models CFGs \<sigma> q \<phi>1 \<and> models CFGs \<sigma> q \<phi>2)" |
"models CFGs \<sigma> q (\<not>sc \<phi>) = (\<not>models CFGs \<sigma> q \<phi>)" |
"models CFGs \<sigma> q (A \<phi>1 \<U> \<phi>2) = (\<forall>l \<in> pre_tCFG.Paths CFGs q. \<exists>i. models CFGs \<sigma> (l i) \<phi>2 \<and>
 (\<forall>j<i. models CFGs \<sigma> (l j) \<phi>1))" |
"models CFGs \<sigma> q (E \<phi>1 \<U> \<phi>2) = (\<exists>l \<in> pre_tCFG.Paths CFGs q. \<exists>i. models CFGs \<sigma> (l i) \<phi>2 \<and>
 (\<forall>j<i. models CFGs \<sigma> (l j) \<phi>1))" |
"models CFGs \<sigma> q (A \<phi>1 \<B> \<phi>2) = (\<forall>l \<in> pre_tCFG.RPaths CFGs q. \<exists>i. models CFGs \<sigma> (l i) \<phi>2 \<and>
 (\<forall>j<i. models CFGs \<sigma> (l j) \<phi>1))" |
"models CFGs \<sigma> q (E \<phi>1 \<B> \<phi>2) = (\<exists>l \<in> pre_tCFG.RPaths CFGs q. \<exists>i. models CFGs \<sigma> (l i) \<phi>2 \<and>
 (\<forall>j<i. models CFGs \<sigma> (l j) \<phi>1))" |
"models CFGs \<sigma> q (SCEx x \<phi>) = (\<exists>obj. models CFGs (\<sigma>(x := obj)) q \<phi>)"

abbreviation "side_cond_sf \<psi> \<sigma> CFGs \<equiv> models CFGs \<sigma> (start_points CFGs) \<psi>"

lemma cond_same_subst: "\<lbrakk>\<forall>x\<in>cond_fv pred_fv P. \<sigma> x = \<sigma>' x; pre_tCFG CFGs\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma> q P = models CFGs \<sigma>' q P"
apply (induct P arbitrary: \<sigma> \<sigma>' q, simp+)
apply (erule pred_same_subst, simp)
apply (metis (lifting, mono_tags) UnI1 UnI2 cond_fv.simps(3) models.simps(3))
apply simp
apply (smt UnI1 UnI2 cond_fv.simps(5) models.simps(5))
apply (smt UnI1 UnI2 cond_fv.simps(6) models.simps(6))
apply (smt UnI1 UnI2 cond_fv.simps(7) models.simps(7))
apply (smt UnI1 UnI2 cond_fv.simps(8) models.simps(8))
apply auto
apply (rule_tac x=obj in exI, smt DiffI fun_upd_def singletonE)+
done

lemma cond_gen: "\<lbrakk>models CFGs \<sigma> q P; \<forall>x\<in>cond_fv pred_fv P. \<sigma> x = \<sigma>' x; pre_tCFG CFGs\<rbrakk> \<Longrightarrow> 
 models CFGs \<sigma>' q P"
by (drule cond_same_subst, simp, force)

end

(* Utility functions for actions. *)
fun update_list where
"update_list f [] = f" |
"update_list f ((x,y) # rest) = update_list (f(x := y)) rest"

lemma update_list_past [simp]: "x \<notin> fst ` set l \<Longrightarrow> update_list f l x = f x"
by (induct l arbitrary: f, auto)

lemma update_list_i: "\<lbrakk>distinct (map fst l); (x, y) \<in> set l\<rbrakk> \<Longrightarrow> update_list f l x = y"
by (induct l arbitrary: f, auto)

definition "remap_succ x y e \<equiv> let (n,s,t) = e in if x = n then (y,s,t) else e"

context TRANS_basics begin

definition "rep_edges es ll \<equiv> if ll = [] then es else
  {remap_succ (hd ll) (last ll) e | e. e\<in>es} \<union>
  {(u,v,Seq) | u v. (\<exists>a. ll!a = u \<and> ll!(a+1) = v \<and> (a+1) < length ll)}"

lemma rep_one_edge [simp]: "rep_edges es [n] = es"
by (auto simp add: rep_edges_def remap_succ_def)

lemma rep_edges_out [simp]: "n \<notin> set ll \<Longrightarrow> ((n, b, c) \<in> rep_edges es ll) = ((n, b, c) \<in> es)"
by (auto simp add: rep_edges_def remap_succ_def, force+)

lemma rep_out_edges_out [simp]: "n \<notin> set ll \<Longrightarrow> out_edges (rep_edges es ll) n = out_edges es n"
by (simp add: out_edges_def)

lemma rep_out_edges_in: "\<lbrakk>n = ll ! i; i < length ll - 1; distinct ll; i = 0 \<or> (\<forall>n' e. (n, n', e) \<notin> es)\<rbrakk> \<Longrightarrow> 
  out_edges (rep_edges es ll) n = {(ll ! (i + 1), Seq)}"
apply (clarsimp simp add: rep_edges_def remap_succ_def out_edges_def)
apply (case_tac "ll = []", simp+)
apply (simp add: last_conv_nth, rule set_eqI, rule iffI, clarsimp)
apply (erule_tac Q=
           "b = Seq \<and> (\<exists>aa. ll ! aa = ll ! i \<and> ll ! Suc aa = a \<and> Suc aa < length ll)"
           in disjE, clarsimp)
(* I think this works in 2015, while the above works in 2014, argh!
apply (erule_tac P="\<exists>aa. _ aa" in disjE, clarsimp)
*)
apply (case_tac "hd ll = aa", simp add: nth_eq_iff_index_eq, force simp add: hd_conv_nth)
apply (clarsimp simp add: nth_eq_iff_index_eq)
apply auto
done

corollary rep_out_edge_in: "\<lbrakk>(n, n', e) \<in> rep_edges es ll; n = ll ! i; i < length ll - 1; distinct ll; 
  i = 0 \<or> (\<forall>n' e. (n, n', e) \<notin> es)\<rbrakk> \<Longrightarrow> n' = ll ! (i + 1) \<and> e = Seq"
apply (frule rep_out_edges_in, simp+)
by (metis out_edge prod.sel(1) prod.sel(2) singletonD)

lemma rep_out_edges_last: "\<lbrakk>n = last ll; ll \<noteq> []; distinct ll; \<forall>n' e. (n, n', e) \<notin> es\<rbrakk> \<Longrightarrow> 
  out_edges (rep_edges es ll) n = out_edges es (hd ll)"
apply (clarsimp simp add: rep_edges_def remap_succ_def out_edges_def)
apply (rule set_eqI, rule iffI, clarsimp)
apply (erule disjE, clarsimp)
apply (case_tac "hd ll = aa", clarsimp+)
apply (simp add: last_conv_nth nth_eq_iff_index_eq)
apply (clarsimp simp add: nth_eq_iff_index_eq)
apply auto
done

lemma rep_out_by_t [simp]: "n \<notin> set ll \<Longrightarrow> out_by_t (rep_edges es ll) t n = out_by_t es t n"
by (simp add: out_edges_by_t)

(* Actions are defined by their effects on one of the CFGs in a tCFG. *)
fun action_sf where
"action_sf (AAddEdge n m e) \<sigma> CFGs = (case (node_subst CFGs \<sigma> n, node_subst CFGs \<sigma> m, type_subst \<sigma> e) of 
   (Some u, Some v, Some ty) \<Rightarrow> if u \<notin> nodes CFGs \<or> u \<in> exits CFGs \<or> v \<in> starts CFGs
    then None else 
   (case CFGs (thread_of u CFGs) of Some G \<Rightarrow> 
    if v \<in> Nodes G then Some (CFGs(thread_of u CFGs \<mapsto> G\<lparr>Edges := Edges G \<union> {(u,v,ty)}\<rparr>)) else None 
 | _ \<Rightarrow> None) | _ \<Rightarrow> None)" |
"action_sf (ARemoveEdge n m e) \<sigma> CFGs = (case (node_subst CFGs \<sigma> n, node_subst CFGs \<sigma> m, type_subst \<sigma> e) of 
   (Some u, Some v, Some ty) \<Rightarrow> if u \<notin> nodes CFGs then None else 
   (case CFGs (thread_of u CFGs) of Some G \<Rightarrow> 
   Some (CFGs(thread_of u CFGs \<mapsto> G\<lparr>Edges := Edges G - {(u,v,ty)}\<rparr>)) | _ \<Rightarrow> None)
 | _ \<Rightarrow> None)" |
"action_sf (AReplace m pl) \<sigma> CFGs = (if pl = [] then (
 case node_subst CFGs \<sigma> m of Some l \<Rightarrow> if l \<notin> nodes CFGs \<or> l \<in> starts CFGs \<or> l \<in> exits CFGs then None 
   else (case CFGs (thread_of l CFGs) of Some G \<Rightarrow> 
   Some (CFGs(thread_of l CFGs \<mapsto> G\<lparr>Nodes := Nodes G - {l}, Edges := {(u,v,t). (u,v,t) \<in> Edges G \<and> u \<noteq> l \<and> v \<noteq> l}\<rparr>)) | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)
 else case (node_subst CFGs \<sigma> m, subst_list CFGs \<sigma> pl) of 
   (Some l, Some il) \<Rightarrow> if l \<notin> nodes CFGs \<or> l \<in> exits CFGs then None else
   (case CFGs (thread_of l CFGs) of Some G \<Rightarrow>
   let ll = new (nodes CFGs) (length il - 1)
    in Some (CFGs(thread_of l CFGs \<mapsto> G\<lparr>Nodes := Nodes G \<union> set ll, Edges := rep_edges (Edges G) (l#ll), 
                        Label := update_list (Label G) (zip (l#ll) il)\<rparr>)) | _ \<Rightarrow> None)
   | _ \<Rightarrow> None)" |
"action_sf (ASplitEdge n m e i) \<sigma> CFGs = (case (node_subst CFGs \<sigma> n,node_subst CFGs \<sigma> m,type_subst \<sigma> e,subst CFGs \<sigma> i) of
   (Some u, Some v, Some ty, Some j) \<Rightarrow>
   (if (u,v,ty) \<in> edges CFGs then (case CFGs (thread_of u CFGs) of Some G \<Rightarrow>
    (let q = hd (new (nodes CFGs) 1)
    in Some (CFGs(thread_of u CFGs \<mapsto> G\<lparr>Nodes := Nodes G \<union> {q}, Edges := (Edges G - {(u,v,ty)}) \<union> {(u,q,ty),(q,v,Seq)}, 
                        Label := (Label G)(q := j)\<rparr>))) | _ \<Rightarrow> None)
    else None) | _ \<Rightarrow> None)"

(* semantics for lists of actions *)
primrec part_comp :: "('a \<rightharpoonup> 'a) list \<Rightarrow> 'a \<rightharpoonup> 'a" where 
"part_comp ([]::('a \<rightharpoonup> 'a) list) x = Some x" |
"part_comp (f#rest) x = (case f x of None \<Rightarrow> None | Some y \<Rightarrow> part_comp rest y)"

definition action_list_sf
where "action_list_sf Al \<sigma> CFGs \<equiv> part_comp (map (\<lambda>a G. action_sf a \<sigma> G) Al) CFGs"

(* Recursive (fixpoint) application of a transformation *)
inductive apply_some::"(('metavar \<rightharpoonup> 'object) \<Rightarrow> 'a \<Rightarrow> 'a set) \<Rightarrow>
 ('metavar \<rightharpoonup> 'object) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
apply_none: "apply_some T \<tau> G G" |
apply_more: "\<lbrakk>G' \<in> T \<tau> G; apply_some T \<tau> G' G''\<rbrakk> \<Longrightarrow> apply_some T \<tau> G G''"

(* Transformations apply actions when their conditions are met. *)
primrec trans_sf where
"trans_sf (TIf al p) \<tau> CFGs = {CFGs' | CFGs' \<sigma>. Some CFGs' = action_list_sf al \<sigma> CFGs \<and>
    side_cond_sf p \<sigma> CFGs \<and> part_matches \<sigma> \<tau>}" |
"trans_sf (TMatch p T) \<tau> CFGs = {CFGs' | CFGs' \<sigma>. side_cond_sf p \<sigma> CFGs \<and> part_matches \<sigma> \<tau> \<and> 
      CFGs' \<in> trans_sf T (part_extend \<tau> (cond_fv pred_fv p) \<sigma>) CFGs}" |
"trans_sf (TChoice T1 T2) \<tau> CFGs = (trans_sf T1 \<tau> CFGs) \<union> (trans_sf T2 \<tau> CFGs)" |
"trans_sf (TThen T1 T2) \<tau> CFGs = {CFGs'' | CFGs' CFGs''. CFGs' \<in> trans_sf T1 \<tau> CFGs \<and> CFGs'' \<in> trans_sf T2 \<tau> CFGs'}" |
"trans_sf (TApplyAll T) \<tau> CFGs = {CFGs'. apply_some (trans_sf T) \<tau> CFGs CFGs'} - 
 {CFGs' | CFGs' CFGs''. CFGs' \<noteq> CFGs'' \<and> CFGs'' \<in> trans_sf T \<tau> CFGs'}"

lemma fst_set_zip [simp]: "length a = length b \<Longrightarrow> fst ` set (zip a b) = set a"
apply (induct a arbitrary: b, clarsimp+)
apply (case_tac b, simp+)
done

lemma subst_last [simp]: "\<lbrakk>subst_list CFGs \<sigma> l = Some l'; l \<noteq> []\<rbrakk> \<Longrightarrow> 
  subst CFGs \<sigma> (last l) = Some (last l')"
apply (induct l arbitrary: l', simp, clarsimp split: option.splits)
apply (case_tac l, simp, clarsimp split: option.splits)
done

lemma subst_nth [simp]: "\<lbrakk>subst_list CFGs \<sigma> l = Some l'; i < length l'\<rbrakk> \<Longrightarrow> 
  subst CFGs \<sigma> (l ! i) = Some (l' ! i)"
apply (induct l arbitrary: l' i, simp, clarsimp split: option.splits)
apply (case_tac i, simp+)
done

lemma subst_length [simp]: "subst_list CFGs \<sigma> l = Some l' \<Longrightarrow> length l = length l'"
by (induct l arbitrary: l', auto split: option.splits)

lemma replace_CFGs: "\<lbrakk>action_sf (AReplace m pl) \<sigma> CFGs = Some CFGs'; pl \<noteq> []; 
  \<forall>p\<in>set (butlast pl). \<forall>i. subst CFGs \<sigma> p = Some i \<longrightarrow> instr_edges i = {no_edges(Seq := 1)};
  \<forall>i n. subst CFGs \<sigma> (last pl) = Some i \<and> node_subst CFGs \<sigma> m = Some n \<longrightarrow> 
    instr_edges i = instr_edges (Label (the (CFGs (thread_of n CFGs))) n);
  tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> tCFG CFGs' instr_edges Seq"
proof - assume "tCFG CFGs instr_edges Seq" then interpret tCFG .
show "\<lbrakk>action_sf (AReplace m pl) \<sigma> CFGs = Some CFGs'; pl \<noteq> []; 
  \<forall>p\<in>set (butlast pl). \<forall>i. subst CFGs \<sigma> p = Some i \<longrightarrow> instr_edges i = {no_edges(Seq := 1)};
  \<forall>i n. subst CFGs \<sigma> (last pl) = Some i \<and> node_subst CFGs \<sigma> m = Some n \<longrightarrow> 
    instr_edges i = instr_edges (Label (the (CFGs (thread_of n CFGs))) n);
  tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> tCFG CFGs' instr_edges Seq"
apply (cut_tac nodes_finite)
apply (clarsimp simp add: Let_def split: option.splits if_splits)
apply (rename_tac l ll g)
apply (unfold_locales, auto)
apply (case_tac "t \<noteq> thread_of l CFGs", simp, erule CFGs)
apply (clarsimp, frule CFGs, clarsimp simp add: is_flowgraph_def flowgraph_def)
apply (rule context_conjI, clarsimp simp add: pointed_graph_def)
apply (rule conjI, clarsimp simp add: rep_edges_def remap_succ_def)
apply (case_tac "new (nodes CFGs) (length ll - Suc 0) = []", clarsimp)
apply (case_tac "length ll - Suc 0", force)
apply (simp add: Let_def)
apply clarsimp
apply (erule disjE, force)
apply clarsimp
apply (case_tac a, simp+)
apply (frule node_of_graph, simp+)
apply (rule conjI, clarsimp simp add: in_edges_def rep_edges_def remap_succ_def)
apply (rule conjI, clarsimp, case_tac "length ll - 1")
apply (metis One_nat_def gr_implies_not0)
apply (simp add: Let_def)
apply (clarsimp, rule conjI, force, clarsimp)
apply (cut_tac S="nodes CFGs" and m="Start g" in new_nodes_are_new, simp+)
apply (simp add: set_conv_nth)
apply (rule_tac x=aa in exI, rule conjI, erule sym, simp+)
apply (metis nodes_by_graph)
apply (clarsimp simp add: out_edges_def rep_edges_def remap_succ_def)
apply (rule conjI, clarsimp, case_tac "length ll - 1")
apply (metis One_nat_def gr_implies_not0)
apply (simp add: Let_def)
apply (clarsimp, rule conjI, clarsimp)
apply (rule conjI, clarsimp)
apply (cut_tac S="nodes CFGs" and m="Exit g" in new_nodes_are_new, simp+)
apply (drule_tac as="new (nodes CFGs) (length ll - Suc 0)" in last_in_set, simp+)
apply (metis nodes_by_graph)
apply metis
apply clarsimp
apply (case_tac aa, clarsimp)
apply (metis exits_by_graph)
apply clarsimp
apply (cut_tac S="nodes CFGs" and m="Exit g" in new_nodes_are_new, simp+)
apply (simp add: set_conv_nth, rule exI, rule conjI, erule sym, simp+)
apply (metis nodes_by_graph)
(* now flowgraph_axioms *)
apply (case_tac "ll = []", clarsimp)
apply (clarsimp simp add: flowgraph_axioms_def)
apply (subgoal_tac "distinct (l # new (nodes CFGs) (length ll - 1))")
apply ((rule conjI, clarsimp)+)
apply (case_tac "u = l", clarsimp)
apply (case_tac "length ll - 1 = 0", simp)
apply (case_tac ll, simp+)
apply (case_tac pl, simp, clarsimp split: option.splits)
apply (case_tac list, simp_all split: option.splits, clarsimp)
apply (rename_tac lrest)
apply (simp add: rep_edges_def remap_succ_def out_edges_def)
apply (rule conjI, clarsimp simp add: Let_def, clarsimp intro!: ext simp add: edge_types_def)
apply (subgoal_tac "l \<noteq> last (let n' = SOME n. n \<notin> nodes CFGs in n' # 
  new (insert n' (nodes CFGs)) (length lrest))", clarsimp)
apply (rule_tac s="{SOME n. n \<notin> nodes CFGs}" in subst, simp_all, rule set_eqI, rule iffI, 
  clarsimp simp add: Let_def)
apply (rule_tac x=0 in exI, simp)
apply clarsimp
apply (case_tac ab, simp+)
apply (cut_tac m=l and S="nodes CFGs" and n="Suc (length lrest)" in new_nodes_are_new2, simp+)
apply (force simp add: Let_def set_conv_nth)
apply (clarsimp simp add: Let_def)
apply (cut_tac S="nodes CFGs" and n="Suc (length lrest)" in new_nodes_are_new, simp+, 
  simp add: set_conv_nth Let_def, rule_tac x=nat in exI, simp+)
apply clarsimp+
apply (subgoal_tac "u \<notin> set (l # new (nodes CFGs) (length ll - Suc 0))", simp, clarsimp)
apply (cut_tac S="nodes CFGs" in new_nodes_are_new, simp+)
apply (metis nodes_by_graph)
apply (clarsimp simp add: set_conv_nth)
apply (cut_tac l="zip (l # new (nodes CFGs) (length ll - Suc 0)) ll" and f="Label g" and
  x="new (nodes CFGs) (length ll - Suc 0) ! i" in update_list_i, simp+)
apply (clarsimp, cut_tac S="nodes CFGs" in new_nodes_are_new, simp+)
apply (simp add: set_zip, rule_tac x="Suc i" in exI, force)
apply simp
apply (case_tac "Suc i = length ll - 1", clarsimp simp add: last_conv_nth)
apply (clarsimp simp add: rep_edges_def remap_succ_def out_edges_def, rule conjI, clarsimp)
apply (case_tac ll, simp+)
apply (case_tac list, simp, simp add: Let_def)
apply clarsimp
apply (erule_tac x=l in allE, simp add: node_of_graph, erule impE)
apply (metis exits_by_graph)
apply (rule_tac s="{(u, t). (l, u, t) \<in> Edges g}" in subst, simp_all)
apply (subgoal_tac "new (nodes CFGs) (length ll - Suc 0) ! i = 
  last (new (nodes CFGs) (length ll - Suc 0))", simp)
apply (rule set_eqI, rule iffI, clarsimp simp add: last_conv_nth, metis)
apply clarsimp
apply (erule disjE, clarsimp)
apply (case_tac "l = aa", simp, clarsimp)
apply (drule pointed_graph.edges_ok, simp, clarsimp)
apply (cut_tac S="nodes CFGs" and m="new (nodes CFGs) (length ll - 1) ! i" in new_nodes_are_new, 
  simp+)
apply (force simp add: set_conv_nth)
apply (metis (hide_lams, no_types) One_nat_def nodes_by_graph)
apply clarsimp
apply (case_tac aa, clarsimp)
apply (cut_tac S="nodes CFGs" and n="length ll - Suc 0" in new_nodes_are_new, simp+, 
  rule last_in_set, clarsimp+)
apply (cut_tac S1="nodes CFGs" and i=i and j=nat and n1="length ll - 1" in 
  nth_eq_iff_index_eq [OF new_nodes_diff], simp+)
apply (simp add: last_conv_nth, case_tac ll, simp+)
apply (case_tac list, simp+)
apply (erule_tac x="pl ! Suc i" in allE, erule impE)
apply (rule_tac x="Suc i" in exI, simp add: nth_butlast)
apply (clarsimp simp add: out_edges_def rep_edges_def remap_succ_def)
apply (rule conjI, clarsimp, case_tac "length ll - 1", simp, simp add: Let_def)
apply (subgoal_tac "new (nodes CFGs) (length ll - Suc 0) ! i \<noteq>
  last (new (nodes CFGs) (length ll - Suc 0))", simp)
apply (clarsimp intro!: ext simp add: edge_types_def, rule conjI, clarsimp)
apply (rule_tac s="{new (nodes CFGs) (length ll - Suc 0) ! Suc i}" in subst, simp_all, rule set_eqI,
  rule iffI, clarsimp)
apply (erule_tac x="Suc i" and P="\<lambda>ab. new (nodes CFGs) (length ll - Suc 0) ! ab = 
  new (nodes CFGs) (length ll - Suc 0) ! Suc i \<longrightarrow> (l # new (nodes CFGs)
       (length ll - Suc 0)) ! ab = new (nodes CFGs) (length ll - Suc 0) ! i 
        \<longrightarrow> \<not> Suc ab < length ll" in allE, clarsimp+)
apply (erule disjE, clarsimp)
apply (drule pointed_graph.edges_ok, simp, clarsimp)
apply (cut_tac S="nodes CFGs" and m="new (nodes CFGs) (length ll - 1) ! i" in new_nodes_are_new, 
  simp+)
apply (force simp add: set_conv_nth)
apply (metis (hide_lams, no_types) One_nat_def nodes_by_graph)
apply clarsimp
apply (case_tac a, simp+)
apply (cut_tac S1="nodes CFGs" and i=nat and j=i and n1="length ll - 1" in 
  nth_eq_iff_index_eq [OF new_nodes_diff], simp+)
apply clarsimp
apply (rule_tac s="{}" in subst, simp_all, clarsimp)
apply (drule pointed_graph.edges_ok, simp, clarsimp)
apply (cut_tac S="nodes CFGs" and m="new (nodes CFGs) (length ll - 1) ! i" in new_nodes_are_new, 
  simp+)
apply (force simp add: set_conv_nth)
apply (metis (hide_lams, no_types) One_nat_def nodes_by_graph)
apply (case_tac "new (nodes CFGs) (length ll - Suc 0) = []", case_tac "length ll - 1", simp, 
  simp add: Let_def)
apply (clarsimp simp add: last_conv_nth)
apply (cut_tac S1="nodes CFGs" and i=i and j="length ll - (Suc (Suc 0))" and n1="length ll - 1" in 
  nth_eq_iff_index_eq [OF new_nodes_diff], simp+)
apply (clarsimp simp add: rep_edges_def remap_succ_def, rule conjI, clarsimp)
apply (case_tac "length ll - 1", simp, simp add: Let_def)
apply (clarsimp, (rule conjI, clarsimp)+)
apply (drule pointed_graph.edges_ok, simp, clarsimp)
apply (cut_tac S="nodes CFGs" and m="last (new (nodes CFGs) (length ll - 1))" in new_nodes_are_new, 
  simp+, rule last_in_set, simp+, force)
apply clarsimp+
apply (case_tac a, clarsimp+)
apply (cut_tac S1="nodes CFGs" and i=nat and j="Suc nat" and n1="length ll - 1" in 
  nth_eq_iff_index_eq [OF new_nodes_diff], simp+)
apply (rule conjI, clarsimp)
apply (cut_tac S="nodes CFGs" in new_nodes_are_new, simp+)
apply (rule new_nodes_diff, simp+)
(* tCFG axioms *)
apply (clarsimp split: if_splits)
apply (erule disjE, cut_tac disjoint, simp_all, simp add: Int_def)
apply (cut_tac S="nodes CFGs" in new_nodes_are_new, simp+, simp add: nodes_by_graph)
apply (erule disjE, cut_tac disjoint, simp_all, simp add: Int_def)
apply (cut_tac S="nodes CFGs" in new_nodes_are_new, simp+, simp add: nodes_by_graph)
apply (cut_tac disjoint, simp_all, simp add: Int_def)
done
qed

lemma apply_some_transfer [rule_format]: "\<lbrakk>P G; \<forall>\<tau> G G'. G' \<in> T \<tau> G \<longrightarrow> P G \<longrightarrow> P G'; apply_some T \<tau> G G'\<rbrakk> \<Longrightarrow>
  P G'"
by (drule_tac P="\<lambda>T' \<tau> G G'. T' = T \<and> P G \<longrightarrow> P G'" in apply_some.induct, auto)

lemma action_disjoint: "\<lbrakk>action_sf a \<sigma> G = Some G'; pre_tCFG G\<rbrakk> \<Longrightarrow> pre_tCFG G'"
apply (frule pre_tCFG.nodes_finite)
apply (case_tac a, auto split: if_splits option.splits simp add: Let_def intro!: pre_tCFG.disjoint_change)
apply (frule pre_tCFG.graphs, simp, clarsimp simp add: pointed_graph_def)
apply (rule conjI, metis)
apply (rule conjI, metis starts_by_graph)
apply (rule conjI, metis exits_by_graph)
apply (simp add: in_edges_def out_edges_def)
apply (cut_tac S="nodes G" in new_nodes_are_new, simp+)
apply (frule pre_tCFG.graphs, simp, clarsimp simp add: pointed_graph_def)
apply (rename_tac m pl l ll g)
apply (rule conjI, clarsimp simp add: rep_edges_def remap_succ_def)
apply (rule conjI, clarsimp)
apply (case_tac "length ll - 1", force, simp add: Let_def)
apply clarsimp
apply (erule disjE, force)
apply clarsimp
apply (case_tac aa, simp add: pre_tCFG.node_of_graph, simp)
apply (simp add: in_edges_def out_edges_def rep_edges_def remap_succ_def)
apply (rule conjI, clarsimp)
apply (case_tac "length ll - 1", force, simp add: Let_def)
apply (clarsimp, (rule conjI, clarsimp+)+)
apply (drule pre_tCFG.graphs, simp)
apply (simp, drule pointed_graph.has_start, cut_tac S="nodes G" and n="length ll - Suc 0" 
  in new_nodes_are_new, simp+)
apply (simp add: set_conv_nth, rule_tac x=aa in exI, simp)
apply (simp add: nodes_by_graph)
apply (clarsimp, (rule conjI, clarsimp+)+)
apply (drule pre_tCFG.graphs, simp+)
apply (drule pointed_graph.has_exit, cut_tac S="nodes G" and n="length ll - Suc 0"
  in new_nodes_are_new, simp+)
apply (rule last_in_set, simp+)
apply (simp add: nodes_by_graph)
apply force
apply clarsimp
apply (case_tac aa, simp add: exits_by_graph)
apply (drule pre_tCFG.graphs, simp+)
apply (drule pointed_graph.has_exit, cut_tac S="nodes G" and n="length ll - Suc 0"
  in new_nodes_are_new, simp+)
apply (simp add: set_conv_nth, rule_tac x=nat in exI, simp)
apply (simp add: nodes_by_graph)
apply (frule pre_tCFG.graphs, simp, clarsimp simp add: pointed_graph_def)
apply (rule conjI, metis)
apply (simp add: in_edges_def out_edges_def)
apply (frule pre_tCFG.graphs, simp, clarsimp simp add: pointed_graph_def)
apply (rule conjI, clarsimp simp add: exits_by_graph)
apply (clarsimp simp add: in_edges_def out_edges_def)
apply (metis pre_tCFG.node_of_graph starts_by_graph)
apply (cut_tac A="nodes G" in fresh_new, simp+)
apply (frule pre_tCFG.graphs, simp, clarsimp simp add: pointed_graph_def)
apply (cut_tac A="nodes G" in fresh_new, simp+)
apply (rule conjI, clarsimp simp add: nodes_by_graph, clarsimp simp add: out_edges_def)
apply (rename_tac n m e i u v ty j g)
apply (rule conjI, clarsimp simp add: edges_def ran_def)
apply (frule_tac t=aa in pre_tCFG.graphs, simp+, drule pointed_graph.edges_ok, simp+)
apply (case_tac "aa = thread_of (Exit g) G", simp+)
apply (drule pre_tCFG.disjoint, simp_all, simp add: Int_def)
apply (clarsimp simp add: edges_def ran_def)
apply (frule_tac t=aa in pre_tCFG.graphs, simp+, drule pointed_graph.edges_ok, simp+)
apply (simp add: pre_tCFG.thread_of_correct)
apply (clarsimp, rule conjI, metis)
apply (clarsimp simp add: in_edges_def)
apply (rule conjI, clarsimp simp add: nodes_by_graph, clarsimp)
done

lemma actions_disjoint: "\<lbrakk>action_list_sf list \<sigma> G = Some G'; pre_tCFG G\<rbrakk> \<Longrightarrow> pre_tCFG G'"
apply (induct list arbitrary: G G', simp_all add: action_list_sf_def split: option.splits)
apply (drule action_disjoint, simp+)
done

lemma trans_disjoint: "\<lbrakk>G' \<in> trans_sf T \<tau> G; pre_tCFG G\<rbrakk> \<Longrightarrow> pre_tCFG G'"
apply (induct T arbitrary: \<tau> G G', simp_all, clarsimp)
apply (drule sym, drule actions_disjoint, simp+)
apply auto
apply (cut_tac P=pre_tCFG and T="trans_sf T" in apply_some_transfer, force, simp+)+
done

end

lemma option_if1 [simp]: "((if P then None else x) = Some y) = (\<not>P \<and> x = Some y)"
by simp

lemma option_if2: "((if P then x else None) = Some y) = (P \<and> x = Some y)"
by simp

lemma part_extend_matches: "\<lbrakk>part_matches \<sigma>' (part_extend \<tau> S \<sigma>); x \<in> S\<rbrakk> \<Longrightarrow> \<sigma>' x = \<sigma> x"
by (simp add: part_matches_def part_extend_def)

lemma option_Some1: "((case a of None \<Rightarrow> None | Some b \<Rightarrow> f b) = Some c) = 
  (\<exists>b. a = Some b \<and> f b = Some c)"
by (auto split: option.splits)

lemma option_Some2: "(Some c = (case a of None \<Rightarrow> None | Some b \<Rightarrow> f b)) = 
  (\<exists>b. a = Some b \<and> f b = Some c)"
by (auto split: option.splits)

end