(* simple_bisim.thy *)
(* William Mansky *)
(* Proof of correctness for reordering by bisimulation. *)

theory simple_bisim
imports simple_opt "AFP/JinjaThreads/Framework/Bisimulation"
begin

definition trsys_of_tCFG where 
"trsys_of_tCFG CFGs step_rel obs C l C' \<equiv> step_rel CFGs C C' \<and> dom l = obs \<and>
 (\<forall>x\<in>obs. fst C' x = update_map (fst C) l x)"

locale tCFG_bisim = bisimulation where trsys1 = "trsys_of_tCFG CFGs step_rel obs"
 and trsys2 = "trsys_of_tCFG CFGs' step_rel obs" for CFGs CFGs' step_rel obs
(* Prove: if bisim, then bisim for any subset of obs *)

definition "reorder_bisim_rel CFGs CFGs' t n2 x1 e1 x2 e2 C C' \<equiv> 
 snd C = snd C' \<and> reorder_sim_rel t n2 x1 e1 x2 e2 (snd C) (fst C') (fst C) \<and>
 TRANS_simple.reachable CFGs C \<and> TRANS_simple.reachable CFGs' C'"


context TRANS_simple begin

lemma reorder_bisim: "\<lbrakk>Some CFGs' = action_list_sf reorder_actions \<sigma> CFGs; part_matches \<sigma> \<tau>;
 side_cond_sf reorder_sc \<sigma> CFGs; \<sigma> ''t'' = OThread t; \<sigma> ''n2'' = ONode n2; \<sigma> ''x1'' = OExpr (Var x1); 
 \<sigma> ''e1'' = OExpr e1; \<sigma> ''x2'' = OExpr (Var x2); \<sigma> ''e2'' = OExpr e2\<rbrakk> \<Longrightarrow>
 tCFG_bisim (reorder_bisim_rel CFGs CFGs' t n2 x1 e1 x2 e2) (op =) CFGs CFGs' step (UNIV - {x1, x2})"
apply (subgoal_tac "CFGs' \<in> trans_sf reorder \<tau> CFGs")
apply (subgoal_tac "TRANS_simple CFGs'")
defer
apply (simp add: TRANS_simple_def TRANS_basics_def)
apply (erule reorder_preserves_tCFGs)
apply (simp add: reorder_def, force)
apply unfold_locales
apply (clarsimp simp add: trsys_of_tCFG_def reorder_bisim_rel_def)
apply (frule reorder_simulates_step2, simp_all, clarsimp)
apply (rule_tac x=env' in exI, simp)
apply (frule reachable_step, simp+)
apply (frule TRANS_simple.reachable_step, simp+, clarsimp)
apply ((erule step.cases)+, clarsimp)
apply (clarsimp simp add: reorder_sim_rel_def)
apply (rule ccontr, erule_tac x=x in ballE, simp_all)
apply (clarsimp split: if_splits)
apply ((erule_tac x=x in allE)+, clarsimp)+
apply (clarsimp simp add: trsys_of_tCFG_def reorder_bisim_rel_def)
apply (frule reorder_simulates_step1, simp_all, clarsimp)
apply (rule_tac x=env' in exI, simp)
apply (frule reachable_step, simp+)
apply (frule TRANS_simple.reachable_step, simp+, clarsimp)
apply ((erule step.cases)+, clarsimp)
apply (clarsimp simp add: reorder_sim_rel_def)
apply (rule ccontr, erule_tac x=x in ballE, simp_all)
apply (clarsimp split: if_splits)
apply ((erule_tac x=x in allE)+, clarsimp)
apply (drule_tac s="update_map env change_map x" in sym, simp)
apply (drule_tac ?m1.0=tl2 and m'=enva in update_same_x, simp+)
apply ((erule_tac x=x in allE)+, clarsimp)+
done

(* By lemmas in bisimulation, this implies that for each (possibly infinite) run in the original
   program, there exists an observationally equivalent run in the new system and vice versa. *)

end

end
