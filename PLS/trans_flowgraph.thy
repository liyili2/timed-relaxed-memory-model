(* trans_flowgraph.thy *)
(* William Mansky *)
(* Threaded CFGs for transformation. *)

theory trans_flowgraph
imports trans_syntax
begin

type_synonym ('node, 'edge_type) edge = "'node \<times> 'node \<times> 'edge_type"

definition in_edges where "in_edges e m \<equiv> {(u,t)| u t. (u,m,t) \<in> e}"
definition out_edges where "out_edges e m \<equiv> {(u,t)| u t. (m,u,t) \<in> e}"
definition out_by_t where "out_by_t e t m \<equiv> {u. (m,u,t) \<in> e}"

lemma out_edge_iff: "((n, n', t) \<in> e) = ((n', t) \<in> out_edges e n)"
by (simp add: out_edges_def)

lemma out_edge: "(n, n', t) \<in> e \<Longrightarrow> (n', t) \<in> out_edges e n"
by (simp add: out_edges_def)

lemma out_edgeD: "(n', t) \<in> out_edges e n \<Longrightarrow> (n, n', t) \<in> e"
by (simp add: out_edges_def)

lemma out_edges_by_t: "out_by_t e t m = {u. (u,t) \<in> out_edges e m}"
by (simp add: out_by_t_def out_edges_def)

lemma out_edges_Un1: "(\<And>u t. (m, u, t) \<notin> e') \<Longrightarrow> out_edges (e \<union> e') m = out_edges e m"
by (simp add: out_edges_def)

lemma out_edges_Un2: "(\<And>u t. (m, u, t) \<notin> e) \<Longrightarrow> out_edges (e \<union> e') m = out_edges e' m"
by (simp add: out_edges_def)

lemma out_edges_Un [simp]: "out_edges (e \<union> e') m = out_edges e m \<union> out_edges e' m"
by (force simp add: out_edges_def)

lemma out_edges_insert [simp]: "out_edges (insert (a, b, c) e) m = 
  (if m = a then insert (b, c) (out_edges e m) else out_edges e m)"
by (force simp add: out_edges_def)

lemma out_edges_empty [simp]: "out_edges {} m = {}"
by (simp add: out_edges_def)

lemma out_edges_minus [simp]: "out_edges (e - e') m = out_edges e m - out_edges e' m"
by (force simp add: out_edges_def)

(* Unlabeled graphs with start and exit nodes. *)
(* Call them "pointed graphs". *)
locale pointed_graph =
 fixes Nodes::"'node set"
   and Edges::"('node, 'edge_type) edge set"
   and Start::'node
   and Exit::'node
 assumes finite_nodes [simp]: "finite Nodes" 
     and finite_edge_types [simp]: "finite (UNIV::'edge_type set)"
     and edges_ok [simp]: "(u,v,t) \<in> Edges \<Longrightarrow> u \<in> Nodes \<and> v \<in> Nodes"
     and has_start [simp]: "Start \<in> Nodes"
     and has_exit [simp]: "Exit \<in> Nodes"
     and start_not_exit [simp]: "Start \<noteq> Exit"
     and start_first [simp]: "in_edges Edges Start = {}"
     and exit_last [simp]: "out_edges Edges Exit = {}"
begin

(* complete (thus finite) paths from a node in a graph, for use in temporal logic *)
(* Is it okay that these are finite?  Would our properties be just as true on infinite loops? *)
definition CPaths where "CPaths n \<equiv>
  {path. (\<exists>r. path = n#r) \<and> (\<forall>i<(length path - 1). \<exists>t. (path!i, path!(i+1), t) \<in> Edges) \<and>
         \<not>(\<exists>n\<in>Nodes. \<exists>t. (path!(length path - 1), n, t) \<in> Edges)}"

(* infinite paths *)
definition Paths where "Paths n \<equiv>
  {path. path 0 = n \<and> (\<forall>i. \<exists>t. (path i, path (i+1), t) \<in> Edges)}"

lemma finite_edges [simp]: "finite Edges"
by (rule_tac B="Nodes \<times> Nodes \<times> UNIV" in finite_subset, auto)

lemma finite_out_edges [simp]: "finite (out_edges Edges n)"
apply (simp add: out_edges_def)
apply (rule_tac A="{n}" in finite_cartesian_productD2, auto)
apply (rule_tac B=Edges in finite_subset, auto)
done

end

definition "next_node Edges t p \<equiv> SOME p'. (p, p', t) \<in> Edges"
lemma next_in [intro]: "(p, p', t) \<in> Edges \<Longrightarrow> (p, next_node Edges t p, t) \<in> Edges"
apply (simp add: next_node_def)
apply (erule someI)
done

lemma next_only [simp]: "out_edges Edges p = {(p', t)} \<Longrightarrow> next_node Edges t p = p'"
by (auto simp add: out_edges_def next_node_def)

lemma next_only_gen: "\<lbrakk>(p, p', t) \<in> Edges; \<forall>(m, s) \<in> out_edges Edges p. s = t \<longrightarrow> m = p'\<rbrakk> \<Longrightarrow> 
 next_node Edges t p = p'"
by (smt mem_Collect_eq next_in next_node_def out_edges_def split)

lemma next_only2 [simp]: "\<lbrakk>out_edges Edges p = {(p', t), (m, s)}; s \<noteq> t\<rbrakk> \<Longrightarrow> next_node Edges t p = p'"
by (rule next_only_gen, auto simp add: out_edges_def)
                                               
lemma next_only2_2 [simp]: "\<lbrakk>out_edges Edges p = {(m, s), (p', t)}; s \<noteq> t\<rbrakk> \<Longrightarrow> next_node Edges t p = p'"
by (rule next_only_gen, auto simp add: out_edges_def)

lemma next_depends: "out_edges Edges p = out_edges Edges' p' \<Longrightarrow> 
  next_node Edges t p = next_node Edges' t p'"
apply (clarsimp simp add: next_node_def out_edges_def)
by (metis split mem_Collect_eq)

record ('node, 'edge_type) doubly_pointed_graph =
 Nodes::"'node set"
 Edges::"('node, 'edge_type) edge set"
 Start::"'node"
 Exit::"'node"

definition is_doubly_pointed_graph
 :: "('node,'edge_type,'a) doubly_pointed_graph_scheme \<Rightarrow> bool" where
"is_doubly_pointed_graph g \<equiv> pointed_graph (Nodes g) (Edges g) (Start g) (Exit g)"
declare is_doubly_pointed_graph_def [simp]

(* Count the edge types in a (finite) set of edges. *)
definition edge_types where "edge_types e t \<equiv> card {v. (v,t) \<in> e}"

lemma has_edge: "\<lbrakk>finite e; edge_types e t > 0\<rbrakk> \<Longrightarrow> \<exists>v. (v,t) \<in> e"
apply (simp add: edge_types_def)
apply (case_tac "card {v. (v, t) \<in> e}", auto simp add: card_Suc_eq)
done

abbreviation "no_edges \<equiv> \<lambda>e. (0::nat)"

lemma out_one [simp]: "finite (Edges G) \<Longrightarrow> (edge_types (out_edges (Edges G) n) = no_edges(ty := Suc 0)) = 
 (\<exists>m. out_edges (Edges G) n = {(m, ty)})"
apply (rule iffI, frule_tac x=ty in cong, simp, simp (no_asm_use) add: edge_types_def)
apply (clarsimp simp add: card_Suc_eq)
apply (rule_tac x=b in exI, clarsimp simp add: set_eq_iff out_edges_def)
apply (subgoal_tac "finite ((\<lambda>v. (n, v, ba) ) -` Edges G)", simp add: vimage_def)
apply (drule_tac x=ba in cong, simp, clarsimp simp add: edge_types_def split: if_splits)
apply (simp, erule finite_vimageI, simp add: inj_on_def)
apply (rule ext, clarsimp simp add: edge_types_def)
done

corollary out_one' [simp]: "finite (Edges G) \<Longrightarrow> (edge_types {(u, t). (n, u, t) \<in> Edges G} = no_edges(seq := Suc 0)) = 
 (\<exists>m. (n, m, seq) \<in> Edges G \<and> (\<forall>u t. (n, u, t) \<in> Edges G \<longrightarrow> u = m \<and> t = seq))"
by (drule_tac n=n and ty=seq in out_one, auto simp add: out_edges_def)

lemma out_two [simp]: "\<lbrakk>finite (Edges G); t1 \<noteq> t2\<rbrakk> \<Longrightarrow> (edge_types (out_edges (Edges G) n) = 
 no_edges(t1 := Suc 0, t2 := Suc 0)) = 
 (\<exists>m1 m2. out_edges (Edges G) n = {(m1, t1), (m2, t2)})"
apply (rule iffI, frule_tac x=t1 in cong, simp, simp (no_asm_use) add: edge_types_def)
apply (frule_tac x=t2 in cong, simp, simp (no_asm_use) add: edge_types_def)
apply (clarsimp simp add: card_Suc_eq)
apply (rule_tac x=b in exI, rule_tac x=ba in exI, clarsimp simp add: set_eq_iff out_edges_def)
apply (subgoal_tac "finite ((\<lambda>v. (n, v, bb) ) -` Edges G)", simp add: vimage_def)
apply (drule_tac x=bb in cong, simp, clarsimp simp add: edge_types_def split: if_splits)
apply (simp, erule finite_vimageI, simp add: inj_on_def)
apply (rule ext, clarsimp simp add: edge_types_def)
done

(* Flowgraphs label nodes with instructions. *)
locale flowgraph = pointed_graph
 where Nodes = "Nodes::'node set" 
   and Start="Start::'node"
   and Edges="Edges::('node, 'edge_type) edge set"
   and Exit="Exit::'node"
 for Nodes and Start and Exit and Edges + 
 fixes L::"'node \<Rightarrow> 'instr" and Seq::'edge_type
(* The relationship between instruction and out-edges of a node, defined per language. *)
   and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
 assumes instr_edges_ok: "\<lbrakk>u \<in> Nodes; u \<noteq> Exit\<rbrakk> \<Longrightarrow> edge_types (out_edges Edges u) \<in> instr_edges (L u)"
     and no_loop: "(u, u, Seq) \<notin> Edges"
(* Should there be a constraint on call-ret pairs as well? 
   Or maybe we should go full procedural? *)

record ('node, 'edge_type, 'instr) flowgraph =
 "('node, 'edge_type) doubly_pointed_graph" +
 Label :: "'node \<Rightarrow> 'instr"

thm flowgraph_def

definition is_flowgraph where
"is_flowgraph g seq InstrEdges \<equiv> flowgraph (Nodes g) (Start g) (Exit g) (Edges g) (Label g) seq InstrEdges"

(* Extraction functions for tCFGs; don't need to be in the locale. *)
definition nodes where "nodes CFGs \<equiv> \<Union>(Nodes ` ran CFGs)"
definition edges where "edges CFGs \<equiv> \<Union>(Edges ` ran CFGs)"
definition starts where "starts CFGs \<equiv> Start ` ran CFGs"
definition exits where "exits CFGs \<equiv> Exit ` ran CFGs"
definition thread_of where "thread_of n CFGs \<equiv> THE t. \<exists>g. CFGs t = Some g \<and> n \<in> Nodes g"
definition label where "label n CFGs \<equiv> case CFGs (thread_of n CFGs) of Some g \<Rightarrow> Label g n"
definition start_of where "start_of n CFGs \<equiv> case CFGs (thread_of n CFGs) of Some g \<Rightarrow> Start g"
definition exit_of where "exit_of n CFGs \<equiv> case CFGs (thread_of n CFGs) of Some g \<Rightarrow> Exit g"

lemma ran_dom: "f ` dom f = Some ` ran f"
apply (auto simp add: dom_def ran_def)
apply force
done

lemma finite_ran_dom: "finite (dom f) \<Longrightarrow> finite (ran f)"
apply (drule_tac h=f in finite_imageI)
apply (simp add: ran_dom)
apply (drule finite_imageD, simp+)
done

lemma nodes_Union: "nodes CFGs = (\<Union>t\<in>dom CFGs. case CFGs t of Some g \<Rightarrow> Nodes g)"
by (auto simp add: nodes_def ran_def)

lemma nodes_by_graph [intro]: "\<lbrakk>CFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> n \<in> nodes CFGs"
by (auto simp add: nodes_def ran_def)

lemma starts_by_graph [intro]: "CFGs t = Some g \<Longrightarrow> Start g \<in> starts CFGs"
by (auto simp add: starts_def ran_def)

lemma exits_by_graph [intro]: "CFGs t = Some g \<Longrightarrow> Exit g \<in> exits CFGs"
by (auto simp add: exits_def ran_def)

definition safe_points where "safe_points CFGs ps \<equiv> 
 \<forall>t G n. CFGs t = Some G \<and> ps t = Some n \<longrightarrow> n \<in> Nodes G"
definition start_points where "start_points CFGs t \<equiv> case CFGs t of Some G \<Rightarrow> Some (Start G) 
 | _ \<Rightarrow> None"
definition end_points where "end_points CFGs t \<equiv> case CFGs t of Some G \<Rightarrow> Some (Exit G) 
 | _ \<Rightarrow> None"

lemma safe_pointsD: "\<lbrakk>safe_points CFGs ps; CFGs t = Some G; ps t = Some n\<rbrakk> \<Longrightarrow> n \<in> Nodes G"
by (force simp add: safe_points_def)

lemma start_points_one [simp]: "CFGs t = Some G \<Longrightarrow> start_points [t \<mapsto> G] = [t \<mapsto> Start G]"
by (rule ext, simp add: start_points_def)

lemma add_no_nodes [simp]: "\<lbrakk>CFGs t = Some G; Nodes G' = Nodes G\<rbrakk> \<Longrightarrow> 
 nodes (CFGs(t \<mapsto> G')) = nodes CFGs"
apply (auto simp add: nodes_def ran_def)
apply (case_tac "a = t", auto)
done

lemma add_nodes: "\<lbrakk>CFGs t = Some G; Nodes G' = S \<union> Nodes G\<rbrakk> \<Longrightarrow>
  nodes (CFGs(t \<mapsto> G')) = S \<union> nodes CFGs"
apply (auto simp add: nodes_def ran_def)
apply (case_tac "a = t", force, force)
done

definition "default_state CFGs n \<equiv> (start_points CFGs)(thread_of n CFGs \<mapsto> n)"

(* Intermediate results of transformations on tCFGs may not be tCFGs, so we need to be able
   to reason about tCFG-like objects (i.e., collections of graphs that may not be correct CFGs). *)
locale pre_tCFG =
 fixes CFGs::"('thread, ('node, 'edge_type, 'instr) flowgraph) map"
 assumes graphs: "CFGs t = Some G \<Longrightarrow> is_doubly_pointed_graph G"
     and disjoint: "\<lbrakk>CFGs t = Some G; CFGs t' = Some G'; t \<noteq> t'\<rbrakk> \<Longrightarrow> Nodes G \<inter> Nodes G' = {}"
     and finite_threads [simp]: "finite (dom CFGs)"
begin

lemma thread_of_correct: "\<lbrakk>CFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> thread_of n CFGs = t"
apply (simp add: thread_of_def, rule the_equality, auto)
apply (rule ccontr, drule disjoint, simp+, blast)
done

lemma node_of_graph: "\<lbrakk>n \<in> nodes CFGs; CFGs (thread_of n CFGs) = Some G\<rbrakk> \<Longrightarrow>
 n \<in> Nodes G"
by (clarsimp simp add: nodes_def ran_def thread_of_correct)

lemma label_correct: "\<lbrakk>CFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> label n CFGs = Label g n"
by (simp add: label_def thread_of_correct)

lemma start_of_correct: "\<lbrakk>CFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> start_of n CFGs = Start g"
by (simp add: start_of_def thread_of_correct)

lemma exit_of_correct: "\<lbrakk>CFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> exit_of n CFGs = Exit g"
by (simp add: exit_of_def thread_of_correct)

lemma nodes_finite: "finite (nodes CFGs)"
apply (simp add: nodes_Union, rule)
apply (clarsimp simp add: dom_def)
apply (drule graphs, simp add: pointed_graph_def)
done

lemma edges_disjoint: "\<lbrakk>CFGs t = Some g; CFGs t' = Some g'; t \<noteq> t'\<rbrakk> \<Longrightarrow> 
                     Edges g \<inter> Edges g' = {}"
apply (frule graphs, frule_tac t=t' in graphs)
apply (drule disjoint, simp+)
apply (force simp add: pointed_graph_def)
done

lemma starts_and_exits_disjoint: "\<lbrakk>CFGs t = Some g; CFGs t' = Some g'; t \<noteq> t'\<rbrakk> \<Longrightarrow> 
                     Start g \<noteq> Start g' \<and> Start g \<noteq> Exit g' \<and> Exit g \<noteq> Start g' \<and> Exit g \<noteq> Exit g'"
apply (frule graphs, frule_tac t=t' in graphs)
apply (drule disjoint, simp+)
apply (auto simp add: pointed_graph_def)
done

lemma safe_start [simp]: "safe_points CFGs (start_points CFGs)"
apply (clarsimp simp add: safe_points_def start_points_def)
apply (frule graphs, clarsimp simp add: pointed_graph_def)
done

lemma safe_end [simp]: "safe_points CFGs (end_points CFGs)"
apply (clarsimp simp add: safe_points_def end_points_def)
apply (frule graphs, clarsimp simp add: pointed_graph_def)
done

lemma has_start: "CFGs t = Some G \<Longrightarrow> Start G \<in> Nodes G"
by (drule graphs, clarsimp simp add: pointed_graph_def)

lemma edges_ok: "\<lbrakk>CFGs t = Some G; (n, n', e) \<in> Edges G\<rbrakk> \<Longrightarrow> n \<in> Nodes G \<and> n' \<in> Nodes G"
by (drule graphs, force simp add: pointed_graph_def)

lemma edges_ok': "(a, b, c) \<in> edges CFGs \<Longrightarrow> a \<in> nodes CFGs \<and> b \<in> nodes CFGs"
by (clarsimp simp add: edges_def ran_def, frule edges_ok, simp+, simp add: nodes_by_graph)

(* Infinite paths through a tCFG. *)
definition Paths where "Paths q \<equiv>
{path. path 0 = q \<and> (\<forall>i. \<forall>t. path (Suc i) t = path i t \<or> 
 (\<exists>n G n' e. path i t = Some n \<and> CFGs t = Some G \<and> path (Suc i) t = Some n' \<and> (n, n', e) \<in> Edges G))}"

lemma Path_first [simp]: "l \<in> Paths q \<Longrightarrow> l 0 = q"
by (clarsimp simp add: Paths_def)

lemma Path_domain1: "l \<in> Paths q \<Longrightarrow> dom (l i) = dom q"
apply (induct i, simp+)
apply (clarsimp simp only: Paths_def dom_def, rule set_eqI, clarsimp)
apply (erule_tac x=i in allE)
apply ((erule_tac x=x in allE)+, erule disjE, clarsimp, blast, clarsimp, blast)
done

lemma Path_domain: "\<lbrakk>l \<in> Paths q; dom q = dom CFGs\<rbrakk> \<Longrightarrow> dom (l i) = dom CFGs"
by (simp add: Path_domain1)

lemma Path_next [simp]: "\<lbrakk>l \<in> Paths q; l i t = Some n\<rbrakk> \<Longrightarrow>
 \<exists>n'. l (Suc i) t = Some n' \<and> (n' = n \<or> (\<exists>G e. CFGs t = Some G \<and> (n, n', e) \<in> Edges G))"
apply (clarsimp simp only: Paths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
apply (erule disjE, clarsimp+)
done

lemma Path_next_None: "\<lbrakk>l \<in> Paths q; l i t = None\<rbrakk> \<Longrightarrow> l (Suc i) t = None"
apply (clarsimp simp only: Paths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
done

lemma Path_prev [simp]: "\<lbrakk>l \<in> Paths q; l (Suc i) t = Some n\<rbrakk> \<Longrightarrow>
 \<exists>n'. l i t = Some n' \<and> (n' = n \<or> (\<exists>G e. CFGs t = Some G \<and> (n', n, e) \<in> Edges G))"
apply (clarsimp simp only: Paths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
apply (erule disjE, force, clarsimp)
done

lemma Path_prev_None: "\<lbrakk>l \<in> Paths q; l (Suc i) t = None\<rbrakk> \<Longrightarrow> l i t = None"
apply (clarsimp simp only: Paths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
done

lemma Path_safe: "\<lbrakk>l \<in> Paths q; safe_points CFGs q\<rbrakk> \<Longrightarrow> safe_points CFGs (l i)"
apply (induct i, auto)
apply (clarsimp simp add: safe_points_def)
apply (erule_tac x=t in allE, clarsimp)
apply (drule Path_prev, auto)
apply (drule graphs, clarsimp)
apply (drule pointed_graph.edges_ok, simp+)
done

lemma safe_path: "\<lbrakk>safe_points CFGs q; l \<in> Paths q; l i t = Some n; CFGs t = Some G\<rbrakk> \<Longrightarrow> 
  n \<in> Nodes G"
by (frule_tac i=i in Path_safe, simp, force simp add: safe_points_def)

lemma exists_path: "\<exists>l. l \<in> Paths q"
by (rule_tac x="\<lambda>i. q" in exI, simp only: Paths_def, simp)

lemma specify_path: "\<forall>l\<in>Paths q. P l \<Longrightarrow> \<exists>l\<in>Paths q. P l"
by (auto simp add: exists_path)

lemma path_incremental: "\<lbrakk>CFGs t = Some G; \<exists>e. (n, n', e) \<in> Edges G; l \<in> Paths q;
 q t = Some n'\<rbrakk> \<Longrightarrow> [q(t \<mapsto> n)] \<frown> l \<in> Paths (q(t \<mapsto> n))"
apply (clarsimp simp only: Paths_def, clarsimp simp add: i_append_def)
apply (rule conjI, force, force)
done

lemma path_incremental_gen: "\<lbrakk>l \<in> Paths q';
 \<forall>t. q t = q' t \<or> (\<exists>G n n' e. CFGs t = Some G \<and> q t = Some n \<and> q' t = Some n' \<and> (n, n', e) \<in> Edges G)\<rbrakk> \<Longrightarrow> 
 [q] \<frown> l \<in> Paths q"
apply (clarsimp simp only: Paths_def, clarsimp simp add: i_append_def)
apply (rule conjI, clarsimp)
apply (erule_tac x=t in allE, force)
apply clarsimp
apply (erule_tac x="i - 1" in allE, (erule_tac x=t in allE)+, clarsimp)
done

lemma path_incremental_segment: "\<lbrakk>l \<in> Paths q;
 \<forall>i<length l'. \<forall>t. (l' ! i) t = ((l' @ [q]) ! Suc i) t \<or> 
 (\<exists>G n n' e. CFGs t = Some G \<and> (l' ! i) t = Some n \<and> ((l' @ [q]) ! Suc i)  t = Some n' \<and> (n, n', e) \<in> Edges G)\<rbrakk> \<Longrightarrow> 
 l' \<frown> l \<in> Paths ((l' @ [q]) ! 0)"
apply (induct l', auto)
apply (subgoal_tac "l' \<frown> l \<in> Paths ((l' @ [q]) ! 0)", rule_tac P="\<lambda>x. x \<in> Paths a" in i_append_Cons [THEN sym [THEN subst]])
apply (rule path_incremental_gen, simp, force)
apply (subgoal_tac "\<forall>i<length l'. \<forall>t. (l' ! i) t = ((l' @ [q]) ! Suc i) t \<or>
 (\<exists>G. CFGs t = Some G \<and> (\<exists>n. (l' ! i) t = Some n \<and> (\<exists>n'. ((l' @ [q]) ! Suc i) t = Some n' \<and> (\<exists>e. (n, n', e) \<in> Edges G))))", 
 simp, force)
done

lemma path_suffix: "l \<in> Paths q \<Longrightarrow> l \<Up> i \<in> Paths (l i)"
by (simp only: Paths_def, simp)

lemma combine_paths: "\<lbrakk>l \<in> Paths q; l' \<in> Paths (l i)\<rbrakk> \<Longrightarrow>
 (l \<Down> i) \<frown> l' \<in> Paths q"
apply (frule_tac l=l' and l'="l \<Down> i" in path_incremental_segment, simp_all, clarsimp)
apply (case_tac "l ia t", drule Path_next_None, simp+)
apply (clarsimp simp add: nth_append)
apply (case_tac "Suc ia = i", simp+)
apply (drule Path_next, simp+)
apply (clarsimp simp add: nth_append)
apply (case_tac "Suc ia = i", simp+)
apply (erule disjE, clarsimp+)+
apply (simp add: nth_append)
apply (case_tac i, simp+)
done

lemma path_plus_edge: "\<lbrakk>l \<in> Paths q; l i t = Some n; CFGs t = Some G; (n, n', e) \<in> Edges G\<rbrakk> \<Longrightarrow>
 \<exists>l'. (l \<Down> i) \<frown> [l i] \<frown> l' \<in> Paths q \<and> l' 0 = l i(t \<mapsto> n')"
apply (cut_tac q="l i(t \<mapsto> n')" in exists_path, clarsimp)
apply (frule_tac l=la in path_incremental, force, simp+)
apply (simp add: map_upd_triv, drule combine_paths, simp, force)
done

definition RPaths where "RPaths q \<equiv>
{path. path 0 = q \<and> (\<forall>i. \<forall>t. path (Suc i) t = path i t \<or> 
 (\<exists>n G n' e. path i t = Some n \<and> CFGs t = Some G \<and> path (Suc i) t = Some n' \<and> (n', n, e) \<in> Edges G)) \<and>
 (\<forall>t. (\<exists>p. q t = Some p) \<longrightarrow> (\<exists>i. path i t = Some (Start (the (CFGs t)))))}"

lemma RPath_first [simp]: "l \<in> RPaths q \<Longrightarrow> l 0 = q"
by (clarsimp simp add: RPaths_def)

lemma RPath_domain1 [simp]: "l \<in> RPaths q \<Longrightarrow> dom (l i) = dom q"
apply (induct i, simp+)
apply (clarsimp simp only: RPaths_def dom_def, rule set_eqI, clarsimp)
apply (erule_tac x=i in allE)
apply ((erule_tac x=x in allE)+, erule disjE, clarsimp, blast, clarsimp)
apply blast
done

lemma RPath_domain [simp]: "\<lbrakk>l \<in> RPaths q; dom q = dom CFGs\<rbrakk> \<Longrightarrow> dom (l i) = dom CFGs"
by simp

lemma RPath_next [simp]: "\<lbrakk>l \<in> RPaths q; l i t = Some n\<rbrakk> \<Longrightarrow>
 \<exists>n'. l (Suc i) t = Some n' \<and> (n' = n \<or> (\<exists>G e. CFGs t = Some G \<and> (n', n, e) \<in> Edges G))"
apply (clarsimp simp only: RPaths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
apply (erule disjE, clarsimp+)
done

lemma RPath_next_None: "\<lbrakk>l \<in> RPaths q; l i t = None\<rbrakk> \<Longrightarrow> l (Suc i) t = None"
apply (clarsimp simp only: RPaths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
done

lemma RPath_prev [simp]: "\<lbrakk>l \<in> RPaths q; l (Suc i) t = Some n\<rbrakk> \<Longrightarrow>
 \<exists>n'. l i t = Some n' \<and> (n' = n \<or> (\<exists>G e. CFGs t = Some G \<and> (n, n', e) \<in> Edges G))"
apply (clarsimp simp only: RPaths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
apply (erule disjE, force, clarsimp)
done

lemma RPath_prev_None: "\<lbrakk>l \<in> RPaths q; l (Suc i) t = None\<rbrakk> \<Longrightarrow>
 l i t = None"
apply (clarsimp simp only: RPaths_def)
apply (erule_tac x=i in allE, clarsimp, (erule_tac x=t in allE)+, clarsimp)
done

lemma RPath_safe: "\<lbrakk>l \<in> RPaths q; safe_points CFGs q\<rbrakk> \<Longrightarrow> safe_points CFGs (l i)"
apply (induct i, auto)
apply (clarsimp simp add: safe_points_def)
apply (erule_tac x=t in allE, clarsimp)
apply (drule RPath_prev, auto)
apply (drule graphs, clarsimp simp add: is_flowgraph_def flowgraph_def)
apply (drule pointed_graph.edges_ok, simp+)
done

lemma rpath_incremental: "\<lbrakk>CFGs t = Some G; \<exists>e. (n', n, e) \<in> Edges G; l \<in> RPaths q;
 q t = Some n'\<rbrakk> \<Longrightarrow> [q(t \<mapsto> n)] \<frown> l \<in> RPaths (q(t \<mapsto> n))"
apply (clarsimp simp only: RPaths_def, clarsimp simp add: i_append_def)
apply (rule conjI, clarsimp, rule conjI, force, clarsimp)
apply (metis diff_Suc_Suc gr0_conv_Suc minus_nat.diff_0)
by (metis diff_Suc_Suc minus_nat.diff_0 nat.distinct(1) option.sel)

lemma rpath_incremental_gen: "\<lbrakk>l \<in> RPaths q';
 \<forall>t. q t = q' t \<or> (\<exists>G n n' e. CFGs t = Some G \<and> q t = Some n \<and> q' t = Some n' \<and> (n', n, e) \<in> Edges G)\<rbrakk> \<Longrightarrow> 
 [q] \<frown> l \<in> RPaths q"
apply (clarsimp simp only: RPaths_def, clarsimp simp add: i_append_def)
apply (rule conjI, clarsimp, rule conjI, clarsimp)
apply (erule_tac x=t in allE, force)
apply (metis diff_Suc_Suc gr0_conv_Suc minus_nat.diff_0)
apply clarsimp
apply (erule_tac x="ia - 1" in allE, (erule_tac x=t in allE)+, clarsimp)
apply force
done

lemma rpath_incremental_segment: "\<lbrakk>l \<in> RPaths q;
 \<forall>i<length l'. \<forall>t. (l' ! i) t = ((l' @ [q]) ! Suc i) t \<or> 
 (\<exists>G n n' e. CFGs t = Some G \<and> (l' ! i) t = Some n \<and> ((l' @ [q]) ! Suc i)  t = Some n' \<and> (n', n, e) \<in> Edges G)\<rbrakk> \<Longrightarrow> 
 l' \<frown> l \<in> RPaths ((l' @ [q]) ! 0)"
apply (induct l', auto)
apply (subgoal_tac "l' \<frown> l \<in> RPaths ((l' @ [q]) ! 0)", rule_tac P="\<lambda>x. x \<in> RPaths a" in i_append_Cons [THEN sym [THEN subst]])
apply (rule rpath_incremental_gen, simp, force)
apply (subgoal_tac "\<forall>i<length l'. \<forall>t. (l' ! i) t = ((l' @ [q]) ! Suc i) t \<or>
 (\<exists>G. CFGs t = Some G \<and> (\<exists>n. (l' ! i) t = Some n \<and> (\<exists>n'. ((l' @ [q]) ! Suc i) t = Some n' \<and> (\<exists>e. (n', n, e) \<in> Edges G))))", 
 simp, force)
done

lemma combine_rpaths: "\<lbrakk>l \<in> RPaths q; l' \<in> RPaths (l i)\<rbrakk> \<Longrightarrow>
 (l \<Down> i) \<frown> l' \<in> RPaths q"
apply (frule_tac l=l' and l'="l \<Down> i" in rpath_incremental_segment, simp_all, clarsimp)
apply (case_tac "l ia t", drule RPath_next_None, simp+)
apply (clarsimp simp add: nth_append)
apply (case_tac "Suc ia = i", simp+)
apply (drule RPath_next, simp+)
apply (clarsimp simp add: nth_append)
apply (case_tac "Suc ia = i", simp+)
apply (erule disjE, clarsimp+)+
apply (simp add: nth_append)
apply (case_tac i, simp+)
done

lemma start_rpath: "(\<lambda>i. start_points CFGs) \<in> RPaths (start_points CFGs)"
by (simp only: RPaths_def, simp add: start_points_def split: option.splits)

lemma start_one_rpath: "CFGs t = Some G \<Longrightarrow> (\<lambda>i. [t \<mapsto> Start G]) \<in> RPaths [t \<mapsto> Start G]"
by (simp only: RPaths_def, clarsimp)

lemma start_some_rpath: "(\<lambda>i t. if t \<in> T then Some (Start (the (CFGs t))) else None) \<in> 
 RPaths (\<lambda>t. if t \<in> T then Some (Start (the (CFGs t))) else None)"
by (simp only: RPaths_def, clarsimp)

lemma specify_start_rpath: "\<forall>l\<in>RPaths (start_points CFGs). P l \<Longrightarrow> P (\<lambda>i. start_points CFGs)"
by (simp add: start_rpath)

lemma reverse_path: "l \<in> Paths (start_points CFGs) \<Longrightarrow> \<exists>l'\<in>RPaths (l i). \<forall>j\<le>i. l' j = l (i - j)"
apply (cut_tac start_rpath)
apply (drule_tac l'="rev (i_take (Suc i) l)" in rpath_incremental_segment, clarsimp)
apply (clarsimp simp add: rev_nth nth_append)
apply (case_tac i, simp+)
apply (cut_tac n=ia and m=nat in Suc_diff_le, simp+)
apply (case_tac "l (Suc nat - ia) t", simp, drule Path_prev_None, simp+)
apply (drule Path_prev, simp+, force)
apply (rule_tac x="rev (l \<Down> Suc i) \<frown> (\<lambda>i. start_points CFGs)" in bexI, auto simp add: nth_append rev_nth)
done

lemma reverse_path_gen: "l \<in> Paths (\<lambda>t. if t \<in> T then Some (Start (the (CFGs t))) else None) \<Longrightarrow> 
 \<exists>l'\<in>RPaths (l i). \<forall>j\<le>i. l' j = l (i - j)"
apply (cut_tac T=T in start_some_rpath)
apply (drule_tac l'="rev (i_take (Suc i) l)" in rpath_incremental_segment, clarsimp)
apply (clarsimp simp add: rev_nth nth_append)
apply (case_tac i, simp+)
apply (cut_tac n=ia and m=nat in Suc_diff_le, simp+)
apply (case_tac "l (Suc nat - ia) t", simp, drule Path_prev_None, simp+)
apply (drule Path_prev, simp+, force)
apply (rule_tac x="rev (l \<Down> Suc i) \<frown> (\<lambda>i t. if t \<in> T then Some (Start (the (CFGs t))) else None)" 
 in bexI, auto simp add: nth_append rev_nth)
done

lemma path_rpath: "\<lbrakk>l \<in> Paths q; l' \<in> RPaths q\<rbrakk> \<Longrightarrow> \<exists>l''. l'' \<in> RPaths (l i)"
apply (subgoal_tac "rev (l \<Up> 1 \<Down> i) @ [q] = rev (l \<Down> Suc i)")
apply (drule_tac l'="rev (l \<Up> 1 \<Down> i)" in rpath_incremental_segment, clarsimp simp add: rev_nth)
apply (case_tac "l (i - Suc ia) t", drule Path_next_None, simp+, drule Path_next, auto)
apply (clarsimp simp add: rev_nth nth_append, force)
apply (metis Path_first i_take_Suc rev.simps(2))
done

lemma specify_rpath: "\<lbrakk>\<forall>l\<in>RPaths q. P l; l \<in> Paths (start_points CFGs); l i = q\<rbrakk> \<Longrightarrow> 
 \<exists>l'\<in>RPaths q. (\<forall>j\<le>i. l' j = l (i - j)) \<and> P l'"
by (drule_tac i=i in reverse_path, simp+)

lemma reverse_rpath: "l \<in> RPaths q \<Longrightarrow> \<exists>l'\<in>Paths (l i). \<forall>j\<le>i. l' j = l (i - j)"
apply (cut_tac q=q in exists_path, clarsimp)
apply (drule_tac l'="rev (i_take (Suc i) l)" in path_incremental_segment, clarsimp)
apply (clarsimp simp add: rev_nth nth_append)
apply (case_tac i, simp+)
apply (cut_tac n=ia and m=nat in Suc_diff_le, simp+)
apply (case_tac "l (Suc nat - ia) t", simp, drule RPath_prev_None, simp+)
apply (drule RPath_prev, simp+, force)
apply (rule_tac x="rev (l \<Down> Suc i) \<frown> la" in bexI, auto simp add: nth_append rev_nth)
done

lemma after_exit_graph: "\<lbrakk>l \<in> Paths q; CFGs t = Some G; l i t = Some (Exit G); j \<ge> i\<rbrakk> \<Longrightarrow> 
 l j t = Some (Exit G)"
apply (induct j, auto)
apply (case_tac "i = Suc j", auto)
apply (drule_tac i=j in Path_next, simp+, clarsimp)
apply (frule graphs, clarsimp, drule pointed_graph.exit_last, simp add: out_edges_def)
done

lemma after_exit: "\<lbrakk>l \<in> Paths q; l i = end_points CFGs; j \<ge> i\<rbrakk> \<Longrightarrow> l j = end_points CFGs"
apply (induct j, auto)
apply (case_tac "i = Suc j", auto)
apply (subgoal_tac "l j = end_points CFGs", rule ext, case_tac "l j x")
apply (drule_tac i=j in Path_next_None, simp, simp)
apply (drule_tac i=j in Path_next, simp+, clarsimp simp add: end_points_def)
apply (frule graphs, clarsimp, drule pointed_graph.exit_last, simp add: out_edges_def)
apply (case_tac "i = j", auto)
done

lemma rpath_end: "\<lbrakk>l \<in> RPaths q; q t \<noteq> None\<rbrakk> \<Longrightarrow> \<exists>i. l i t = Some (Start (the (CFGs t)))"
by (simp only: RPaths_def, clarsimp)

lemma before_start_thread: "\<lbrakk>l \<in> RPaths q; l i t = Some (Start (the (CFGs t))); j \<ge> i\<rbrakk> \<Longrightarrow> 
 l j t = Some (Start (the (CFGs t)))"
apply (induct j, auto)
apply (case_tac "i = Suc j", auto)
apply (drule_tac i=j in RPath_next, simp+, clarsimp)
apply (frule graphs, clarsimp, drule pointed_graph.start_first, simp add: in_edges_def)
done

lemma before_start_graph: "\<lbrakk>l \<in> RPaths q; CFGs t = Some G; l i t = Some (Start G); j \<ge> i\<rbrakk> \<Longrightarrow> 
 l j t = Some (Start G)"
apply (induct j, auto)
apply (case_tac "i = Suc j", auto)
apply (drule_tac i=j in RPath_next, simp+, clarsimp)
apply (frule graphs, clarsimp, drule pointed_graph.start_first, simp add: in_edges_def)
done

lemma before_start: "\<lbrakk>l \<in> RPaths q; l i = start_points CFGs; j \<ge> i\<rbrakk> \<Longrightarrow> l j = start_points CFGs"
apply (induct j, auto)
apply (case_tac "i = Suc j", auto)
apply (subgoal_tac "l j = start_points CFGs", rule ext, case_tac "l j x")
apply (drule_tac i=j in RPath_next_None, simp, simp)
apply (drule_tac i=j in RPath_next, simp+, clarsimp simp add: start_points_def)
apply (frule graphs, clarsimp, drule pointed_graph.start_first, simp add: in_edges_def)
apply (case_tac "i = j", auto)
done

lemma rpath_suffix: "l \<in> RPaths q \<Longrightarrow> l \<Up> i \<in> RPaths (l i)"
apply (frule_tac i=i in RPath_domain1)
apply (simp only: RPaths_def, clarsimp)
apply (case_tac "l 0 t")
apply (metis domIff option.distinct(1))
apply (rule_tac x=t in allE, simp, erule impE, simp, clarify)
apply (rule_tac x="ia - i" in exI)
apply (case_tac "ia \<ge> i", simp+)
apply (cut_tac l=l and q="l 0" and j=i in before_start_thread, simp only: RPaths_def, simp+)
done

lemma path_by_thread: "\<lbrakk>l \<in> Paths q; q' t = q t\<rbrakk> \<Longrightarrow> \<exists>l'\<in>Paths q'. \<forall>i. l' i t = l i t"
apply (cut_tac q=q' in exists_path, clarsimp)
apply (rule_tac x="\<lambda>i t'. if t' = t then l i t else la i t'" in bexI, simp)
apply (simp only: Paths_def, clarsimp)
apply (rule ext, simp)
done

lemma path_one_thread: "\<lbrakk>l \<in> Paths q; q t = Some n\<rbrakk> \<Longrightarrow> 
 (\<lambda>i t'. if t = t' then l i t else None) \<in> Paths [t \<mapsto> n]"
by (simp only: Paths_def, clarsimp intro!: ext)

lemma rpath_by_thread: "\<lbrakk>l \<in> RPaths q; l' \<in> RPaths q'; q' t = q t\<rbrakk> \<Longrightarrow> \<exists>l'\<in>RPaths q'. \<forall>i. l' i t = l i t"
apply (rule_tac x="\<lambda>i t'. if t' = t then l i t else l' i t'" in bexI, simp)
apply (simp only: RPaths_def, clarsimp)
apply (rule conjI, rule ext, simp, clarsimp)
by metis

lemma rpath_one_thread: "\<lbrakk>l \<in> RPaths q; q t = Some n\<rbrakk> \<Longrightarrow> 
 (\<lambda>i t'. if t = t' then l i t else None) \<in> RPaths [t \<mapsto> n]"
by (simp only: RPaths_def, clarsimp intro!: ext)

lemma rpath_start: "\<lbrakk>l \<in> RPaths q; finite (dom q)\<rbrakk> \<Longrightarrow> 
 \<exists>l'\<in>Paths (\<lambda>t. if t \<in> dom q then Some (Start (the (CFGs t))) else None). \<exists>i'. l i = l' i'"
apply (frule_tac i="SOME i. l i = (\<lambda>t. if t \<in> dom q then Some (Start (the (CFGs t))) else None)" 
 in reverse_rpath, clarsimp)
apply (cut_tac P="\<lambda>i. l i = (\<lambda>t. if t \<in> dom q then Some (Start (the (CFGs t))) else None)" 
 in someI_ex)
apply (rule_tac x="Max {LEAST i. l i t = Some (Start (the (CFGs t))) | t. t \<in> dom q}" in exI,
 rule ext, clarsimp)
apply (rule conjI, clarsimp)
apply (frule_tac t=t in rpath_end, simp+, clarsimp)
apply (drule_tac P="\<lambda>i. l i t = Some (Start (the (CFGs t)))" in LeastI)
apply (rule before_start_thread, simp+)
apply (cut_tac A="{LEAST i. l i t = Some (Start (the (CFGs t))) |t. t \<in> dom q}" and 
 k="LEAST x. l x t = Some (Start (the (CFGs t)))" in wellorder_Max_lemma, force, simp+)
apply (drule_tac i="Max {LEAST i. l i t = Some (Start (the (CFGs t))) |t. t \<in> dom q}" in 
 RPath_domain1,force simp add: domIff)
apply clarsimp
apply (rule bexI, simp_all, rule_tac x="(SOME i. l i = (\<lambda>t. if t \<in> dom q then 
 Some (Start (the (CFGs t))) else None)) - i" in exI, clarsimp)
apply (case_tac "i < (SOME i. l i = (\<lambda>t. if t \<in> dom q then Some (Start (the (CFGs t))) else None))", 
 simp+)
apply (rule ext, simp, rule conjI, clarsimp)
apply (rule_tac i="SOME x. l x = (\<lambda>t. if t \<in> dom q then Some (Start (the (CFGs t))) else None)" 
 in before_start_thread, simp+, simp_all)
apply (simp add: dom_def)
apply (drule_tac i=i in RPath_domain1, force simp add: domIff)
done

(* Transferring paths to other CFGs with the same structure *)
lemma path_by_thread_gen: "\<lbrakk>l \<in> Paths q; pre_tCFG CFGs'; CFGs' t = CFGs t; q' t = q t\<rbrakk> \<Longrightarrow> 
 \<exists>l'\<in>pre_tCFG.Paths CFGs' q'. \<forall>i. l' i t = l i t"
apply (frule_tac q=q' in pre_tCFG.exists_path, clarsimp)
apply (rule_tac x="\<lambda>i t'. if t' = t then l i t else la i t'" in bexI, simp)
apply (simp only: pre_tCFG.Paths_def, clarsimp)
apply (rule conjI, rule ext, simp)
apply clarsimp
apply (case_tac "l i t", auto)
apply (drule Path_next_None, simp+)
apply (drule Path_next, simp+, clarsimp)
done

lemma rpath_by_thread_gen: "\<lbrakk>l \<in> RPaths q; pre_tCFG CFGs'; CFGs' t = CFGs t; 
 l' \<in> pre_tCFG.RPaths CFGs' q'; q' t = q t; start_points CFGs' t = start_points CFGs t\<rbrakk> \<Longrightarrow> 
 \<exists>l'\<in>pre_tCFG.RPaths CFGs' q'. \<forall>i. l' i t = l i t"
apply (rule_tac x="\<lambda>i t'. if t' = t then l i t else l' i t'" in bexI, simp)
apply (simp only: pre_tCFG.RPaths_def, clarsimp)
apply (rule conjI, rule ext, simp)
apply (rule conjI, clarsimp)
apply (case_tac "l i t", auto)
apply (drule RPath_next_None, simp+)
apply (drule RPath_next, simp+, clarsimp)
apply (clarsimp simp only: RPaths_def, clarsimp)
by metis

lemma path_G': "\<lbrakk>CFGs t = Some G; CFGs' t = Some (G\<lparr>Label := L'\<rparr>); l \<in> Paths q; q' t = q t;
 pre_tCFG CFGs'\<rbrakk> \<Longrightarrow> \<exists>l'\<in>pre_tCFG.Paths CFGs' q'. \<forall>i. l' i t = l i t"
apply (frule_tac q=q' in pre_tCFG.exists_path, clarsimp)
apply (rule_tac x="\<lambda>i t'. if t' = t then l i t else la i t'" in bexI, simp)
apply (simp only: pre_tCFG.Paths_def, clarsimp)
apply (rule conjI, rule ext, simp)
apply clarsimp
apply (case_tac "l i t", auto)
apply (drule Path_next_None, simp+)
apply (drule Path_next, simp+, clarsimp)
done

lemma path_CFGs': "\<lbrakk>\<forall>t G. CFGs t = Some G \<longrightarrow> (\<exists>L'. CFGs' t = Some (G\<lparr>Label := L'\<rparr>)); l \<in> Paths q;
 pre_tCFG CFGs'\<rbrakk> \<Longrightarrow> l \<in> pre_tCFG.Paths CFGs' q"
by (simp only: pre_tCFG.Paths_def Paths_def, force)

lemma rpath_CFGs': "\<lbrakk>\<forall>t G. CFGs t = Some G \<longrightarrow> (\<exists>L'. CFGs' t = Some (G\<lparr>Label := L'\<rparr>)); l \<in> RPaths q;
 pre_tCFG CFGs'; dom q \<subseteq> dom CFGs\<rbrakk> \<Longrightarrow> l \<in> pre_tCFG.RPaths CFGs' q"
apply (simp only: pre_tCFG.RPaths_def RPaths_def, auto)
apply force
apply (case_tac "CFGs t", auto)
apply (erule_tac x=t in allE, force)
done

lemma thread_of_path: "\<lbrakk>CFGs t = Some G; l i t = Some n; l \<in> Paths (start_points CFGs)\<rbrakk> \<Longrightarrow>
  thread_of n CFGs = t"
apply (frule_tac i=i in Path_safe, simp)
apply (force simp add: safe_points_def thread_of_correct)
done

lemma one_CFG: "CFGs t = Some G \<Longrightarrow> pre_tCFG [t \<mapsto> G]"
apply (unfold_locales, auto split: if_splits)
apply (drule graphs, simp)
done

lemma narrow_path [simp]: "CFGs t = Some G \<Longrightarrow> Paths [t \<mapsto> n] = 
  pre_tCFG.Paths [t \<mapsto> G] [t \<mapsto> n]"
apply (frule one_CFG)
apply (rule set_eqI, rule iffI)
apply (simp add: pre_tCFG.Paths_def)
apply (rule conjI, simp add: fun_upd_def, clarsimp)
apply (frule_tac i=i in Path_domain1, simp add: dom_def set_eq_iff)
apply (clarsimp simp only: Paths_def, clarsimp)
apply (erule_tac x=ta in allE)
apply (erule_tac x=i in allE, erule_tac x=ta in allE, clarsimp split: if_splits)
apply (clarsimp simp only: pre_tCFG.Paths_def Paths_def, clarsimp)
apply (erule_tac x=i in allE, erule_tac x=ta in allE, clarsimp split: if_splits)
done

lemma narrow_rpath [simp]: "CFGs t = Some G \<Longrightarrow> RPaths [t \<mapsto> n] = 
  pre_tCFG.RPaths [t \<mapsto> G] [t \<mapsto> n]"
apply (frule one_CFG)
apply (rule set_eqI, rule iffI)
apply (simp add: pre_tCFG.RPaths_def)
apply (rule conjI, simp add: fun_upd_def)
apply (rule conjI, clarsimp)
apply (frule_tac i=i in RPath_domain1, simp add: dom_def set_eq_iff)
apply (clarsimp simp only: RPaths_def, clarsimp)
apply (erule_tac x=ta in allE)
apply (erule_tac x=i in allE, (erule_tac x=ta in allE)+, rule conjI, clarsimp+)
apply (frule rpath_end, simp+)
apply (simp only: RPaths_def, clarsimp)
apply (frule pre_tCFG.RPath_first, simp+)
apply (rule conjI, clarsimp simp only: pre_tCFG.RPaths_def RPaths_def, clarsimp)
apply (erule_tac x=i in allE, (erule_tac x=ta in allE)+, clarsimp split: if_splits)
apply (frule pre_tCFG.rpath_end, simp+)
done

lemma remove_CFG: "pre_tCFG (CFGs(t := None))"
apply (unfold_locales, auto split: if_splits simp del: is_doubly_pointed_graph_def)
apply (erule graphs)
apply (drule_tac t'=t' in disjoint, simp+, blast)
done

lemma disjoint_one: "\<lbrakk>\<forall>t' G'. CFGs t' = Some G' \<and> t \<noteq> t' \<longrightarrow> Nodes G \<inter> Nodes G' = {};
  is_doubly_pointed_graph G\<rbrakk> \<Longrightarrow> pre_tCFG (CFGs(t \<mapsto> G))"
apply (unfold_locales, auto split: if_splits)
apply (drule graphs, simp)
apply (drule disjoint, simp_all, blast)
done

lemma disjoint_change: "\<lbrakk>CFGs t = Some G; Nodes G' \<inter> nodes CFGs \<subseteq> Nodes G; 
  is_doubly_pointed_graph G'\<rbrakk> \<Longrightarrow> pre_tCFG (CFGs(t \<mapsto> G'))"
apply (unfold_locales, auto split: if_splits)
apply (drule_tac t=ta in graphs, simp)
apply (drule_tac t=t and t=t' in disjoint, simp_all, blast)
apply (drule_tac t=t and t=ta in disjoint, simp_all, simp, blast)
apply (drule_tac t=ta and t=t' in disjoint, simp_all, blast)
done

end

(* A tCFG has one CFG per thread name. *)
locale tCFG =
 fixes CFGs::"('thread, ('node, 'edge_type, 'instr) flowgraph) map"
   and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
   and Seq::'edge_type
 assumes CFGs: "CFGs t = Some g \<Longrightarrow> is_flowgraph g Seq instr_edges"
     and disjoint: "\<lbrakk>CFGs t = Some g; CFGs t' = Some g'; t \<noteq> t'\<rbrakk> \<Longrightarrow> 
                     Nodes g \<inter> Nodes g' = {}"
     and finite_threads [simp]: "finite (dom CFGs)"
begin

lemma one_CFG: "CFGs t = Some G \<Longrightarrow> tCFG [t \<mapsto> G] instr_edges Seq"
apply (unfold_locales, auto split: if_splits)
apply (erule CFGs)
done

lemma remove_CFG: "tCFG (CFGs(t := None)) instr_edges Seq"
apply (unfold_locales, auto split: if_splits)
apply (erule CFGs)
apply (drule_tac t'=t' in disjoint, simp+, blast)
done

end

sublocale tCFG \<subseteq> pre_tCFG
apply (unfold_locales, auto)
apply (drule CFGs, simp add: is_flowgraph_def flowgraph_def)
apply (drule disjoint, simp+, blast)
done

(* Infinite types and fresh objects. *)
primrec new::"'a set \<Rightarrow> nat \<Rightarrow> 'a list" where
"new S 0 = []" |
"new S (Suc n) = (let n' = SOME n. n \<notin> S in n' # new (S \<union> {n'}) n)"

lemmas fresh_new = ex_new_if_finite [THEN someI_ex]
lemma new_nodes_are_new: "\<lbrakk>\<not>finite (UNIV::'a set); finite (S::'a set); m \<in> set (new S n)\<rbrakk> \<Longrightarrow> m \<notin> S"
apply (induct n arbitrary: S, simp)
apply (simp add: Let_def)
apply (erule disjE, simp add: fresh_new)
apply (subgoal_tac "m \<notin> insert (SOME n. n \<notin> S) S", blast+)
done

lemma new_nodes_are_new2: "\<lbrakk>\<not>finite (UNIV::'a set); finite (S::'a set); m \<in> S\<rbrakk> \<Longrightarrow> m \<notin> set (new S n)"
by (clarsimp simp add: new_nodes_are_new)

lemma new_nodes_are_new3: "\<lbrakk>\<not>finite (UNIV::'a set); finite (S::'a set)\<rbrakk> \<Longrightarrow> set (new S n) \<inter> S = {}"
by (metis disjoint_iff_in_not_in2 new_nodes_are_new2)

lemma new_nodes_count [simp]: "length (new S n) = n"
by (induct n arbitrary: S, auto simp add: Let_def)

lemma new_nodes_diff: "\<lbrakk>\<not>finite (UNIV::'a set); finite (S::'a set)\<rbrakk> \<Longrightarrow> distinct (new S n)"
apply (induct n arbitrary: S, simp)
apply (clarsimp simp add: Let_def)
apply (cut_tac S="insert (SOME n. n \<notin> S) S" in new_nodes_are_new, simp+)
done

lemma bij_betw_vimage_singleton: "\<lbrakk>bij_betw f X Y; a \<in> Y\<rbrakk> \<Longrightarrow> \<exists>!x. f -` {a} \<inter> X = {x}"
apply (clarsimp simp add: bij_betw_def inj_on_def)
apply (rule_tac a=x in ex1I, auto)
done

definition "inv_on f X x \<equiv> THE x'. f -` {x} \<inter> X = {x'}"
lemma inv_on_ok: "\<lbrakk>bij_betw f X Y; x \<in> X\<rbrakk> \<Longrightarrow> inv_on f X (f x) = x"
apply (frule_tac a="f x" in bij_betw_vimage_singleton, force simp add: bij_betw_def image_def)
apply (clarsimp simp add: inv_on_def vimage_def Int_def)
by (metis (mono_tags) mem_Collect_eq singleton_iff)

lemma inv_on_ok2: "\<lbrakk>bij_betw f X Y; x \<in> Y\<rbrakk> \<Longrightarrow> f (inv_on f X x) = x"
apply (frule_tac a=x in bij_betw_vimage_singleton, force simp add: bij_betw_def image_def)
apply (clarsimp simp add: inv_on_def vimage_def Int_def)
by (metis (mono_tags) mem_Collect_eq singleton_iff)

lemma inv_on_in: "\<lbrakk>bij_betw f X Y; x \<in> Y\<rbrakk> \<Longrightarrow> inv_on f X x \<in> X"
apply (frule_tac a=x in bij_betw_vimage_singleton, force simp add: bij_betw_def)
apply (clarsimp simp add: inv_on_def Int_def, blast)
done

locale tCFG_nodes = tCFG
 where CFGs="CFGs::('thread, ('node, 'edge_type, 'instr) flowgraph) map"
   and instr_edges="instr_edges::'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
   and Seq="Seq::'edge_type"
 for CFGs and instr_edges and Seq +
 assumes infinite_nodes: "infinite (UNIV::'node set)"
 begin

(* duplicating a CFG in a tCFG *)
definition "dup (G::('node, 'edge_type, 'instr) flowgraph) \<equiv> 
  let f = SOME f. bij_betw f (Nodes G) (set (new (nodes CFGs) (card (Nodes G)))) in
  (f, \<lparr>Nodes = f ` Nodes G, Edges = (\<lambda>(n, n', e). (f n, f n', e)) ` Edges G, 
   Start = f (Start G), Exit = f (Exit G), Label = Label G o inv_on f (Nodes G)\<rparr>)"

lemma dup_ok: "finite (Nodes G) \<Longrightarrow> \<exists>f. bij_betw f (Nodes G) (set (new (nodes CFGs) (card (Nodes G))))"
apply (rule finite_same_card_bij, auto)
apply (cut_tac S="nodes CFGs" and n="card (Nodes G)" in new_nodes_diff)
apply (rule infinite_nodes, rule nodes_finite)
apply (simp add: distinct_card)
done

lemma dup_nodes: "dup G = (f, G') \<Longrightarrow> Nodes G' = f ` Nodes G"
by (clarsimp simp add: dup_def Let_def)

lemma dup_edges: "dup G = (f, G') \<Longrightarrow> Edges G' = (\<lambda>(n, n', e). (f n, f n', e)) ` Edges G"
by (clarsimp simp add: dup_def Let_def)

lemma dup_start: "dup G = (f, G') \<Longrightarrow> Start G' = f (Start G)"
by (clarsimp simp add: dup_def Let_def)

lemma dup_exit: "dup G = (f, G') \<Longrightarrow> Exit G' = f (Exit G)" 
by (clarsimp simp add: dup_def Let_def)

lemma dup_labels: "dup G = (f, G') \<Longrightarrow> Label G' = Label G o inv_on f (Nodes G)"
by (clarsimp simp add: dup_def Let_def)

lemma dup_bij: "\<lbrakk>dup G = (f, G'); finite (Nodes G)\<rbrakk> \<Longrightarrow> bij_betw f (Nodes G) (Nodes G')"
apply (clarsimp simp add: dup_def Let_def)
apply (cut_tac someI_ex [OF dup_ok], simp_all)
apply (simp add: bij_betw_def)
done

lemma dup_node: "\<lbrakk>dup G = (f, G'); n \<in> Nodes G\<rbrakk> \<Longrightarrow> f n \<in> Nodes G'"
by (simp add: dup_nodes)

lemma dup_node': "\<lbrakk>dup G = (f, G'); n \<in> Nodes G'; finite (Nodes G)\<rbrakk> \<Longrightarrow> inv_on f (Nodes G) n \<in> Nodes G"
apply (simp add: dup_nodes, frule dup_bij, simp)
apply (rule inv_on_in, simp+)
apply (simp add: bij_betw_def)
done

lemma dup_edge: "\<lbrakk>dup G = (f, G'); (n, n', e) \<in> Edges G; n \<in> Nodes G; n' \<in> Nodes G\<rbrakk> \<Longrightarrow>
  (f n, f n', e) \<in> Edges G'"
by (force simp add: dup_edges image_def)

lemma dup_edge': "\<lbrakk>dup G = (f, G'); (n, n', e) \<in> Edges G'; n \<in> Nodes G'; n' \<in> Nodes G'; 
  is_doubly_pointed_graph G\<rbrakk> \<Longrightarrow> (inv_on f (Nodes G) n, inv_on f (Nodes G) n', e) \<in> Edges G"
apply (cut_tac f=f in dup_bij, simp+)
apply (erule pointed_graph.finite_nodes)
apply (clarsimp simp add: dup_edges)
apply (drule pointed_graph.edges_ok, simp)
apply (simp add: inv_on_ok)
done

lemma dup_in_edges: "\<lbrakk>dup G = (f, G'); is_doubly_pointed_graph G; n \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  in_edges (Edges G') (f n) = (\<lambda>(n, e). (f n, e)) ` in_edges (Edges G) n"
apply (cut_tac f=f in dup_bij, simp)
apply (simp, erule pointed_graph.finite_nodes)
apply (auto simp add: dup_edges image_def in_edges_def)
apply (clarsimp simp add: bij_betw_def, drule_tac y=ab in inj_on_eq_iff, simp)
apply (drule pointed_graph.edges_ok, simp+)
apply force+
done

lemma dup_out_edges: "\<lbrakk>dup G = (f, G'); is_doubly_pointed_graph G; n \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  out_edges (Edges G') (f n) = (\<lambda>(n, e). (f n, e)) ` out_edges (Edges G) n"
apply (cut_tac f=f in dup_bij, simp)
apply (simp, erule pointed_graph.finite_nodes)
apply (auto simp add: dup_edges image_def out_edges_def)
apply (clarsimp simp add: bij_betw_def, drule_tac y=aa in inj_on_eq_iff, simp)
apply (drule pointed_graph.edges_ok, simp+)
apply force+
done

lemma dup_start': "\<lbrakk>dup G = (f, G'); finite (Nodes G); Start G \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  Start G = inv_on f (Nodes G) (Start G')"
apply (simp add: dup_start, frule dup_bij, simp)
apply (simp add: inv_on_ok)
done

lemma dup_exit': "\<lbrakk>dup G = (f, G'); finite (Nodes G); Exit G \<in> Nodes G\<rbrakk> \<Longrightarrow> 
  Exit G = inv_on f (Nodes G) (Exit G')"
apply (simp add: dup_exit, frule dup_bij, simp)
apply (simp add: inv_on_ok)
done

lemma dup_label: "\<lbrakk>dup G = (f, G'); finite (Nodes G); n \<in> Nodes G\<rbrakk> \<Longrightarrow> Label G' (f n) = Label G n"
apply (frule dup_bij, simp)
apply (simp add: dup_labels inv_on_ok)
done

lemma dup_label': "dup G = (f, G') \<Longrightarrow> Label G' n = Label G (inv_on f (Nodes G) n)"
by (simp add: dup_labels)

lemma dup_edge_types: "\<lbrakk>dup G = (f, G'); is_doubly_pointed_graph G; n \<in> Nodes G\<rbrakk> \<Longrightarrow>
  edge_types ((\<lambda>(n, e). (f n, e)) ` out_edges (Edges G) n) = edge_types (out_edges (Edges G) n)"
apply (cut_tac f=f in dup_bij, simp)
apply (simp, erule pointed_graph.finite_nodes)
apply (rule ext, simp add: edge_types_def)
apply (rule sym, rule_tac f=f in bij_betw_same_card, clarsimp simp add: bij_betw_def)
apply (rule conjI, rule subset_inj_on, simp)
apply (clarsimp simp add: out_edges_def image_def)
apply (drule pointed_graph.edges_ok, simp+)
apply (force simp add: image_def)
done

lemma dup_CFG: "\<lbrakk>is_flowgraph G Seq instr_edges; dup G = (f, G')\<rbrakk> \<Longrightarrow> is_flowgraph G' Seq instr_edges"
apply (simp add: is_flowgraph_def)
apply (cut_tac f=f in dup_bij, simp)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.finite_nodes)
apply unfold_locales
apply (simp add: dup_nodes)
apply (rule finite_imageI)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.finite_nodes)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.finite_edge_types)
apply (clarsimp simp add: dup_nodes dup_edges image_def flowgraph_def)
apply (drule pointed_graph.edges_ok, simp+, force)
apply (clarsimp simp add: dup_start dup_nodes image_def flowgraph_def)
apply (drule pointed_graph.has_start, force)
apply (clarsimp simp add: dup_exit dup_nodes image_def flowgraph_def)
apply (drule pointed_graph.has_exit, force)
apply (clarsimp simp add: dup_start dup_exit flowgraph_def bij_betw_def pointed_graph_def)
apply (drule_tac y="Exit G" in inj_on_eq_iff, simp+)
apply (simp add: dup_start)
apply (frule dup_in_edges)
apply (simp add: flowgraph_def)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.has_start)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.start_first)
apply (simp add: dup_exit)
apply (frule dup_out_edges)
apply (simp add: flowgraph_def)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.has_exit)
apply (clarsimp simp add: flowgraph_def, erule pointed_graph.exit_last)
apply (simp add: dup_label')
apply (frule inv_on_in, simp+)
apply (frule dup_out_edges)
apply (simp add: flowgraph_def, simp+)
apply (simp add: inv_on_ok2)
apply (frule dup_edge_types)
apply (simp add: flowgraph_def, simp+)
apply (erule flowgraph.instr_edges_ok, simp+)
apply (clarsimp simp add: dup_exit)
apply (metis inv_on_ok2)
apply (clarsimp simp add: dup_edges bij_betw_def)
apply (clarsimp simp add: flowgraph_def, drule pointed_graph.edges_ok, simp+)
apply clarsimp
apply (drule_tac y=aa in inj_on_eq_iff, simp+)
apply (simp add: flowgraph_axioms_def)
done

lemma dup_disjoint: "\<lbrakk>CFGs t = Some G; finite (Nodes G'); dup G' = (f, G'')\<rbrakk> \<Longrightarrow> 
  Nodes G \<inter> Nodes G'' = {}"
apply (clarsimp simp add: dup_def Let_def)
apply (cut_tac P="\<lambda>f. bij_betw f (Nodes G') (set (new (nodes CFGs) (card (Nodes G'))))" in someI_ex, 
  erule dup_ok, clarsimp simp add: bij_betw_def)
apply (rule ccontr, drule not_empty_imp_ex, clarsimp)
apply (cut_tac new_nodes_are_new, simp_all)
apply (drule_tac CFGs=CFGs in nodes_by_graph, simp+)
apply (rule infinite_nodes, rule nodes_finite)
done

lemma dup_CFGs: "\<lbrakk>CFGs t = Some G; dup G = (f, G')\<rbrakk> \<Longrightarrow> tCFG (CFGs(t' \<mapsto> G')) instr_edges Seq"
apply (unfold_locales, simp_all split: if_splits)
apply (clarsimp, rule dup_CFG, erule CFGs, simp)
apply (erule CFGs)
apply (drule_tac t=g in sym, simp add: Int_commute, rule dup_disjoint, simp+)
apply (drule_tac t=t in CFGs, clarsimp simp add: is_flowgraph_def flowgraph_def, 
  erule pointed_graph.finite_nodes, simp)
apply (drule_tac t=g' in sym, simp, rule dup_disjoint, simp+)
apply (drule_tac t=t in CFGs, clarsimp simp add: is_flowgraph_def flowgraph_def, 
  erule pointed_graph.finite_nodes, simp)
apply (rule disjoint, auto)
done

lemma safe_points_rem: "safe_points CFGs q \<Longrightarrow> safe_points (CFGs(t := None)) (q(t := None))"
by (clarsimp simp add: safe_points_def)

lemma safe_points_dup: "\<lbrakk>safe_points CFGs q; CFGs t = Some G; q t = Some n; dup G = (f, G')\<rbrakk> \<Longrightarrow>
  safe_points (CFGs(t' \<mapsto> G')) (q(t' \<mapsto> f n))"
by (force simp add: safe_points_def dup_nodes)

end

(* Interprocedural CFGs *)
locale ICFG = pointed_graph where Edges="Edges::('node, 'edge_type) edge set" for Edges + 
 fixes L::"'node \<Rightarrow> 'instr" and Seq::'edge_type
   and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
   and Starts::"('proc, 'node) map"
   and Exits::"('proc, 'node) map"
   and main::'proc
(* do we need to partition nodes by procedure? *)
 assumes instr_edges_ok: "\<lbrakk>u \<in> Nodes; u \<notin> ran Starts; u \<notin> ran Exits\<rbrakk> \<Longrightarrow> 
                          edge_types (out_edges Edges u) \<in> instr_edges (L u)"
     and has_start: "\<exists>v. (Start, v, Seq) \<in> Edges"
     and no_loop: "(u, u, Seq) \<notin> Edges"
     and main_Start [simp]: "Starts main = Some Start"
     and main_Exit [simp]: "Exits main = Some Exit"
(* How do we handle call/return edges?  Closed world assumption?  
   Do we enforce correct call destinations? *)

record ('proc, 'node, 'edge_type, 'instr) ICFG =
 "('node, 'edge_type, 'instr) flowgraph" +
 Starts :: "('proc, 'node) map"
 Exits :: "('proc, 'node) map"
 main :: "'proc"

definition "is_ICFG G seq InstrEdges \<equiv>
 is_doubly_pointed_graph G \<and>
 ICFG_axioms (Nodes G) (Start G) (Exit G) (Edges G) (Label G) seq InstrEdges (Starts G) (Exits G) (main G)"

(* Is it worth unifying this with the above, instead of duplicating it?  ICFGs are technically
   not CFGs, because they have many start and exit nodes with no instructions on them. 
   It might be worth preserving the distinction, though, because paths in a tICFG are a bit tricky,
   thanks to the call stack. *)

(* A tCFG has one CFG per thread name. *)
locale tICFG =
 fixes ICFGs::"('thread, ('proc, 'node, 'edge_type, 'instr) ICFG) map"
   and instr_edges::"'instr \<Rightarrow> ('edge_type \<Rightarrow> nat) set"
   and Seq::'edge_type
 assumes ICFGs: "ICFGs t = Some g \<Longrightarrow> is_ICFG g Seq instr_edges"
     and disjoint: "\<lbrakk>ICFGs t = Some g; ICFGs t' = Some g'; t \<noteq> t'\<rbrakk> \<Longrightarrow> 
                     Nodes g \<inter> Nodes g' = {}"
     and finite_threads [simp]: "finite (dom ICFGs)"
begin

lemma thread_of_correct: "\<lbrakk>ICFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> thread_of n ICFGs = t"
apply (simp add: thread_of_def, rule the_equality, auto)
apply (rule ccontr, drule disjoint, simp+, blast)
done

lemma node_of_graph: "\<lbrakk>n \<in> nodes ICFGs; ICFGs (thread_of n ICFGs) = Some G\<rbrakk> \<Longrightarrow> n \<in> Nodes G"
by (clarsimp simp add: nodes_def ran_def thread_of_correct)

lemma label_correct: "\<lbrakk>ICFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> label n ICFGs = Label g n"
by (simp add: label_def thread_of_correct)

lemma start_of_correct: "\<lbrakk>ICFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> start_of n ICFGs = Start g"
by (simp add: start_of_def thread_of_correct)

lemma exit_of_correct: "\<lbrakk>ICFGs t = Some g; n \<in> Nodes g\<rbrakk> \<Longrightarrow> exit_of n ICFGs = Exit g"
by (simp add: exit_of_def thread_of_correct)

lemma nodes_finite: "finite (nodes ICFGs)"
apply (simp add: nodes_Union, rule) (* rule? *)
apply (clarsimp simp add: dom_def)
apply (drule ICFGs, simp add: is_ICFG_def pointed_graph_def)
done

lemma edges_disjoint: "\<lbrakk>ICFGs t = Some g; ICFGs t' = Some g'; t \<noteq> t'\<rbrakk> \<Longrightarrow> 
                     Edges g \<inter> Edges g' = {}"
apply (frule ICFGs, frule_tac t=t' in ICFGs)
apply (drule disjoint, simp+)
apply (clarsimp simp add: is_ICFG_def pointed_graph_def)
apply force
done

lemma safe_start [simp]: "safe_points ICFGs (start_points ICFGs)"
apply (clarsimp simp add: safe_points_def start_points_def)
apply (frule ICFGs, simp add: is_ICFG_def pointed_graph_def)
done

lemma safe_end [simp]: "safe_points ICFGs (end_points ICFGs)"
apply (clarsimp simp add: safe_points_def end_points_def)
apply (frule ICFGs, simp add: is_ICFG_def pointed_graph_def)
done

end

end
