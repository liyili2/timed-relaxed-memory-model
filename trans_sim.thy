(* trans_sim.thy *)
(* William Mansky *)
(* The basics of simulation relations on tCFGs. *)

theory trans_sim
imports trans_semantics "$AFP/JinjaThreads/Framework/Bisimulation"
begin

lemmas zero_enat_def [simp del] option.splits [split del]

definition trsys_of_tCFG where 
"trsys_of_tCFG       CFGs     step_rel      obs       get_mem C l C' \<equiv> 
step_rel CFGs C C' \<and> l = get_mem C' |` obs" 
(* This needs to reflect the actual changes made! *)

abbreviation "trsys_of_tCFG_full CFGs step_rel \<equiv> trsys_of_tCFG CFGs step_rel UNIV"
lemma dom_UNIV [simp]: "dom l = UNIV \<Longrightarrow> m ++ l = l"
by (rule ext, case_tac "l x", auto)

(* One-directional simulation, modified from the bisimulation theory of JinjaThreads *)
locale simulation = bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
assumes simulation: "\<lbrakk>sa \<approx> sb; sa -1-tl1\<rightarrow> sa'\<rbrakk> \<Longrightarrow> \<exists>sb' tl2. sb -2-tl2\<rightarrow> sb' \<and> sa' \<approx> sb' \<and> tl1 \<sim> tl2"
begin

lemma simulation_rtrancl:
  "[|s1 -1-tls1\<rightarrow>* s1'; s1 \<approx> s2|]
  ==> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by(auto intro: rtrancl3p.rtrancl3p_refl)
next
  case (rtrancl3p_step s1 tls1 s1' tl1 s1'')
  from `s1 \<approx> s2 ==> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2` `s1 \<approx> s2`
  obtain s2' tls2 where "s2 -2-tls2\<rightarrow>* s2'" "s1' \<approx> s2'" "tls1 [\<sim>] tls2" by blast
  moreover from `s1' -1-tl1\<rightarrow> s1''` `s1' \<approx> s2'`
  obtain s2'' tl2 where "s2' -2-tl2\<rightarrow> s2''" "s1'' \<approx> s2''" "tl1 \<sim> tl2" by(auto dest: simulation)
  ultimately have "s2 -2-tls2 @ [tl2]\<rightarrow>* s2''" "tls1 @ [tl1] [\<sim>] tls2 @ [tl2]"
    by(auto intro: rtrancl3p.rtrancl3p_step list_all2_appendI)
  with `s1'' \<approx> s2''` show ?case by(blast)
qed

definition tl1_to_tl2 where
"tl1_to_tl2 = (\<lambda>(s2 :: 's2) (stls1 :: ('s1 \<times> 'tl1 \<times> 's1) llist). unfold_llist
     (\<lambda>(s2, stls1). lnull stls1)
     (\<lambda>(s2, stls1). let (s1, tl1, s1') = lhd stls1;
                        (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
                    in (s2, tl2, s2'))
     (\<lambda>(s2, stls1). let (s1, tl1, s1') = lhd stls1;
                        (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
                    in (s2', ltl stls1))
     (s2, stls1))"

lemma simulation_inf_step:
  assumes red1: "s1 -1-tls1\<rightarrow>* \<infinity>" and bisim: "s1 \<approx> s2"
  shows "\<exists>tls2. s2 -2-tls2\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
proof -
  from r1.inf_step_imp_inf_step_table[OF red1]
  obtain stls1 where red1': "s1 -1-stls1\<rightarrow>*t \<infinity>" 
    and tls1: "tls1 = lmap (fst \<circ> snd) stls1" by blast
  have tl1_to_tl2_simps [simp]:
    "\<And>s2 stls1. lnull (tl1_to_tl2 s2 stls1) \<longleftrightarrow> lnull stls1"
    "\<And>s2 stls1. \<not> lnull stls1 \<Longrightarrow> lhd (tl1_to_tl2 s2 stls1) =
    (let (s1, tl1, s1') = lhd stls1;
         (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
     in (s2, tl2, s2'))"
    "\<And>s2 stls1. \<not> lnull stls1 \<Longrightarrow> ltl (tl1_to_tl2 s2 stls1) =
    (let (s1, tl1, s1') = lhd stls1;
         (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
     in tl1_to_tl2 s2' (ltl stls1))"
    "\<And>s2. tl1_to_tl2 s2 LNil = LNil"
    "\<And>s2 s1 tl1 s1' stls1'. tl1_to_tl2 s2 (LCons (s1, tl1, s1') stls1') =
        LCons (s2, SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) 
              (tl1_to_tl2 (snd (SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2)) stls1')"
    by(simp_all add: tl1_to_tl2_def split_beta)

  have [simp]: "llength (tl1_to_tl2 s2 stls1) = llength stls1"
    by(coinduction arbitrary: s2 stls1 rule: enat_coinduct)(auto simp add: epred_llength split_beta)

  from red1' bisim have "s2 -2-tl1_to_tl2 s2 stls1\<rightarrow>*t \<infinity>"
  proof(coinduction arbitrary: s2 s1 stls1)
    case (inf_step_table s2 s1 stls1)
    note red1' = `s1 -1-stls1\<rightarrow>*t \<infinity>` and bisim = `s1 \<approx> s2`
    from red1' show ?case
    proof(cases)
      case (inf_step_tableI s1' stls1' tl1)
      hence stls1: "stls1 = LCons (s1, tl1, s1') stls1'"
        and r: "s1 -1-tl1\<rightarrow> s1'" and reds1: "s1' -1-stls1'\<rightarrow>*t \<infinity>" by simp_all
      let ?tl2s2' = "SOME (tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
      let ?tl2 = "fst ?tl2s2'" let ?s2' = "snd ?tl2s2'"
      from simulation[OF bisim r] obtain s2' tl2
        where "s2 -2-tl2\<rightarrow> s2'" "s1' \<approx> s2'" "tl1 \<sim> tl2" by blast
      hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) (tl2, s2')" by simp
      hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) ?tl2s2'" by(rule someI)
      hence "s2 -2-?tl2\<rightarrow> ?s2'" "s1' \<approx> ?s2'" "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
      then show ?thesis using reds1 stls1 by(fastforce intro: prod_eqI)
    qed
  qed
  hence "s2 -2-lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)\<rightarrow>* \<infinity>"
    by(rule r2.inf_step_table_imp_inf_step)
  moreover have "tls1 [[\<sim>]] lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)"
  proof(rule llist_all2_all_lnthI)
    show "llength tls1 = llength (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1))"
      using tls1 by simp
  next
    fix n
    assume "enat n < llength tls1"
    thus "lnth tls1 n \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)) n"
      using red1' bisim unfolding tls1
    proof(induct n arbitrary: s1 s2 stls1 rule: nat_less_induct)
      case (1 n)
      hence IH: "\<And>m s1 s2 stls1. \<lbrakk> m < n; enat m < llength (lmap (fst \<circ> snd) stls1);
                                   s1 -1-stls1\<rightarrow>*t \<infinity>; s1 \<approx> s2 \<rbrakk>
                 \<Longrightarrow> lnth (lmap (fst \<circ> snd) stls1) m \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)) m"
        by blast
      from `s1 -1-stls1\<rightarrow>*t \<infinity>` show ?case
      proof cases
        case (inf_step_tableI s1' stls1' tl1)
        hence  stls1: "stls1 = LCons (s1, tl1, s1') stls1'"
          and r: "s1 -1-tl1\<rightarrow> s1'" and reds: "s1' -1-stls1'\<rightarrow>*t \<infinity>" by simp_all
        let ?tl2s2' = "SOME (tl2, s2').  s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
        let ?tl2 = "fst ?tl2s2'" let ?s2' = "snd ?tl2s2'"
        from simulation[OF `s1 \<approx> s2` r] obtain s2' tl2
          where "s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2" by blast
        hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) (tl2, s2')" by simp
        hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) ?tl2s2'" by(rule someI)
        hence bisim': "s1' \<approx> ?s2'" and tlsim: "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
        show ?thesis
        proof(cases n)
          case 0
          with stls1 tlsim show ?thesis by simp
        next
          case (Suc m)
          hence "m < n" by simp
          moreover have "enat m < llength (lmap (fst \<circ> snd) stls1')"
            using stls1 `enat n < llength (lmap (fst \<circ> snd) stls1)` Suc by(simp add: Suc_ile_eq)
          ultimately have "lnth (lmap (fst \<circ> snd) stls1') m \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 ?s2' stls1')) m"
            using reds bisim' by(rule IH)
          with Suc stls1 show ?thesis by(simp del: o_apply)
        qed
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed

end

sublocale bisimulation \<subseteq> simulation
by (unfold_locales, simp add: simulation1)

locale tCFG_bisim = bisimulation where trsys1 = "trsys_of_tCFG CFGs step_rel obs get_mem"
 and trsys2 = "trsys_of_tCFG CFGs' step_rel obs get_mem" for CFGs CFGs' step_rel obs get_mem

locale tCFG_sim = simulation where
 trsys1 = "trsys_of_tCFG CFGs step_rel obs get_mem" and 
 trsys2 = "trsys_of_tCFG CFGs' step_rel obs get_mem"
 for CFGs CFGs' step_rel obs get_mem

definition (in TRANS_basics) "opt_sim T sim tlsim step_rel obs get_mem \<equiv> 
  \<forall>\<tau> CFGs. tCFG CFGs instr_edges Seq \<longrightarrow> (\<forall>CFGs' \<in> trans_sf T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and>
    tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem)"

(* composition *)
lemma sim_comp: "\<lbrakk>tCFG_sim sim tlsim CFGs CFGs' step_rel obs get_mem; 
  tCFG_sim sim' tlsim' CFGs' CFGs'' step_rel obs get_mem\<rbrakk> \<Longrightarrow>
tCFG_sim (sim \<circ>\<^sub>B sim') (tlsim \<circ>\<^sub>B tlsim') CFGs CFGs'' step_rel obs get_mem"
apply (clarsimp simp add: tCFG_sim_def simulation_def bisim_compose_def trsys_of_tCFG_def)
by (metis (hide_lams, mono_tags))

context TRANS_basics begin

lemma then_sim [intro]: "\<lbrakk>opt_sim T1 sim1 tlsim1 step_rel obs get_mem; opt_sim T2 sim2 tlsim2 step_rel obs get_mem\<rbrakk> \<Longrightarrow>
  opt_sim (TThen T1 T2) (sim2 \<circ>\<^sub>B sim1) (tlsim2 \<circ>\<^sub>B tlsim1) step_rel obs get_mem"
unfolding opt_sim_def
apply clarify
apply (erule_tac x=\<tau> in allE, erule_tac x=CFGs in allE, erule impE, simp, clarsimp)
apply (erule_tac x=CFGs'a in ballE, simp_all)
apply (erule_tac x=\<tau> in allE, erule_tac x=CFGs'a in allE, erule impE, simp, 
  erule_tac x=CFGs' in ballE, simp_all, clarsimp)
apply (rule sim_comp, simp_all)
done

lemma applysome_sim: "\<lbrakk>opt_sim T sim tlsim step_rel obs get_mem; apply_some (trans_sf T) \<tau> CFGs CFGs';
  tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  tCFG CFGs' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_sim sim' tlsim' CFGs' CFGs step_rel obs get_mem)"
apply (clarsimp simp add: opt_sim_def, drule_tac P="\<lambda>t \<tau> G G'. t = trans_sf T \<and> tCFG G instr_edges Seq \<longrightarrow> 
  (tCFG G' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_sim sim' tlsim' G' G step_rel obs get_mem))" 
  in apply_some.induct, auto)
apply (rule_tac x="(=)" in exI, rule_tac x="(=)" in exI, unfold_locales, force)
apply (erule_tac x=\<tau> in allE, erule_tac x=G in allE, simp, erule_tac x=G' in ballE, simp_all, clarsimp)
apply (rule exI, rule exI, rule sim_comp, simp+)
done

(* is this sufficient? *)
definition "trans_sim T step_rel obs get_mem \<equiv> 
  \<forall>\<tau> CFGs. tCFG CFGs instr_edges Seq \<longrightarrow> (\<forall>CFGs' \<in> trans_sf T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and>
    (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem))"

lemma opt_sim_trans [intro]: "opt_sim T sim tlsim step_rel obs get_mem \<Longrightarrow> trans_sim T step_rel obs get_mem"
by (force simp add: opt_sim_def trans_sim_def)

definition "cond_sim P T step_rel obs get_mem \<equiv> \<forall>\<tau> CFGs. P \<tau> CFGs \<and> tCFG CFGs instr_edges Seq \<longrightarrow> 
  (\<forall>CFGs' \<in> trans_sf T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and> 
    (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem))"

lemma cond_simI [intro]: "(\<And>\<tau> CFGs CFGs'. \<lbrakk>P \<tau> CFGs; tCFG CFGs instr_edges Seq; CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow>
  tCFG CFGs' instr_edges Seq \<and> (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem))
  \<Longrightarrow> cond_sim P T step_rel obs get_mem"
by (force simp add: cond_sim_def)

lemma applyall_sim [intro]: "opt_sim T sim tlsim step_rel obs get_mem \<Longrightarrow> trans_sim (TApplyAll T) step_rel obs get_mem"
apply (clarsimp simp add: trans_sim_def)
by (metis applysome_sim)

lemma match_cond_sim [intro]: "cond_sim (\<lambda>\<tau> CFGs. \<exists>\<sigma> \<tau>'. side_cond_sf \<phi> \<sigma> CFGs \<and> part_matches \<sigma> \<tau>' \<and> 
  \<tau> = part_extend \<tau>' (cond_fv pred_fv \<phi>) \<sigma>) T step_rel obs get_mem \<Longrightarrow>
  trans_sim (TMatch \<phi> T) step_rel obs get_mem"
apply (clarsimp simp add: trans_sim_def cond_sim_def)
by metis

lemma then_cond_sim [intro]: "\<lbrakk>cond_sim P T1 step_rel obs get_mem; cond_sim P T2 step_rel obs get_mem;
  \<forall>\<tau> CFGs CFGs'. P \<tau> CFGs \<and> CFGs' \<in> trans_sf T1 \<tau> CFGs \<longrightarrow> P \<tau> CFGs'\<rbrakk> \<Longrightarrow>
  cond_sim P (TThen T1 T2) step_rel obs get_mem"
unfolding cond_sim_def proof clarify
  fix CFGs \<tau> CFGs' assume "CFGs' \<in> trans_sf (TThen T1 T2) \<tau> CFGs"
  hence "\<exists>CFGs''. CFGs'' \<in> trans_sf T1 \<tau> CFGs \<and> CFGs' \<in> trans_sf T2 \<tau> CFGs''" by simp
  then obtain CFGs'' where A: "CFGs'' \<in> trans_sf T1 \<tau> CFGs \<and> CFGs' \<in> trans_sf T2 \<tau> CFGs''" ..
  assume P: "P \<tau> CFGs" "tCFG CFGs instr_edges Seq" "\<forall>\<tau> CFGs. P \<tau> CFGs \<and> tCFG CFGs instr_edges Seq \<longrightarrow> 
  (\<forall>CFGs'\<in>trans_sf T1 \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and> (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem))"
  from this A have tCFG'': "tCFG CFGs'' instr_edges Seq" "\<exists>sim tlsim. tCFG_sim sim tlsim CFGs'' CFGs step_rel obs get_mem" by auto
  then obtain sim tlsim where sim: "tCFG_sim sim tlsim CFGs'' CFGs step_rel obs get_mem" by auto
  assume "\<forall>\<tau> CFGs CFGs'. P \<tau> CFGs \<and> CFGs' \<in> trans_sf T1 \<tau> CFGs \<longrightarrow> P \<tau> CFGs'"
  from this P A have P'': "P \<tau> CFGs''" by metis
  assume "\<forall>\<tau> CFGs. P \<tau> CFGs \<and> tCFG CFGs instr_edges Seq \<longrightarrow> (\<forall>CFGs'\<in>trans_sf T2 \<tau> CFGs. tCFG CFGs' 
  instr_edges Seq \<and> (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem))"
  from this P'' tCFG'' A have tCFG': "tCFG CFGs' instr_edges Seq" 
    "\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs'' step_rel obs get_mem" by auto
  then obtain sim' tlsim' where sim': "tCFG_sim sim' tlsim' CFGs' CFGs'' step_rel obs get_mem" by auto
  show "tCFG CFGs' instr_edges Seq \<and> (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem)"
  proof
    from tCFG' show "tCFG CFGs' instr_edges Seq" by simp
    next show "\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem"
    proof ((rule exI)+, rule sim_comp)
      from sim show "tCFG_sim sim tlsim CFGs'' CFGs step_rel obs get_mem" .
      from sim' show "tCFG_sim sim' tlsim' CFGs' CFGs'' step_rel obs get_mem" .
    qed
  qed
qed

(* Why is this so slow in apply-style? *)

lemma applysome_cond_sim: "\<lbrakk>apply_some (trans_sf T) \<tau> CFGs CFGs'; cond_sim P T step_rel obs get_mem;
  \<forall>\<tau> CFGs CFGs'. (P \<tau> CFGs \<and> CFGs' \<in> trans_sf T \<tau> CFGs) \<longrightarrow> P \<tau> CFGs'; P \<tau> CFGs; tCFG CFGs instr_edges Seq\<rbrakk> \<Longrightarrow> 
  tCFG CFGs' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_sim sim' tlsim' CFGs' CFGs step_rel obs get_mem)"
unfolding cond_sim_def proof (induct rule: apply_some.induct)
  fix G::"'thread \<Rightarrow> ('node, 'edge_type, 'instr) flowgraph option" assume "tCFG G instr_edges Seq"
  thus "tCFG G instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_sim sim' tlsim' G G step_rel obs get_mem)"
  proof
    have "tCFG_sim (=) (=) G G step_rel obs get_mem" by (unfold_locales, simp)
    thus "\<exists>sim' tlsim'. tCFG_sim sim' tlsim' G G step_rel obs get_mem" by force
  qed
next
  case (apply_more G' T \<tau> G G'') hence G'': "tCFG G'' instr_edges Seq \<and> 
  (\<exists>sim' tlsim'. tCFG_sim sim' tlsim' G'' G' step_rel obs get_mem)" by metis
  then obtain sim' tlsim' where sim': "tCFG_sim sim' tlsim' G'' G' step_rel obs get_mem" by force
  moreover assume "G' \<in> T \<tau> G" "P \<tau> G" "tCFG G instr_edges Seq" 
  "\<forall>\<tau> CFGs. P \<tau> CFGs \<and> tCFG CFGs instr_edges Seq \<longrightarrow> (\<forall>CFGs'\<in>T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and> 
  (\<exists>sim tlsim. tCFG_sim sim tlsim CFGs' CFGs step_rel obs get_mem))"
  then obtain sim tlsim where sim: "tCFG_sim sim tlsim G' G step_rel obs get_mem" by force
  have "\<exists>sim' tlsim'. tCFG_sim sim' tlsim' G'' G step_rel obs get_mem"
    proof ((rule exI)+, rule sim_comp)
      show "tCFG_sim sim' tlsim' G'' G' step_rel obs get_mem" by (rule sim')
      next show "tCFG_sim sim tlsim G' G step_rel obs get_mem" by (rule sim)
    qed
  from this G'' show ?case by simp
qed

lemma applyall_cond_sim [intro]: "\<lbrakk>cond_sim P T step_rel obs get_mem; 
  \<forall>\<tau> CFGs CFGs'. P \<tau> CFGs \<and> CFGs' \<in> trans_sf T \<tau> CFGs \<longrightarrow> P \<tau> CFGs'\<rbrakk> \<Longrightarrow>
  cond_sim P (TApplyAll T) step_rel obs get_mem"
by (clarsimp intro!: cond_simI simp add: applysome_cond_sim)

end

(* stuttering bisimulation *)
locale delay_bisimulation_base =
  bisimulation_base +
  trsys1: \<tau>trsys trsys1 \<tau>move1 +
  trsys2: \<tau>trsys trsys2 \<tau>move2 
  for \<tau>move1 \<tau>move2 +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
begin

notation
  trsys1.silent_move ("_/ -\<tau>1\<rightarrow> _" [50, 50] 60) and
  trsys2.silent_move ("_/ -\<tau>2\<rightarrow> _" [50, 50] 60)

notation
  trsys1.silent_moves ("_/ -\<tau>1\<rightarrow>* _" [50, 50] 60) and
  trsys2.silent_moves ("_/ -\<tau>2\<rightarrow>* _" [50, 50] 60)

notation
  trsys1.silent_movet ("_/ -\<tau>1\<rightarrow>+ _" [50, 50] 60) and
  trsys2.silent_movet ("_/ -\<tau>2\<rightarrow>+ _" [50, 50] 60)

notation
  trsys1.\<tau>rtrancl3p ("_ -\<tau>1-_\<rightarrow>* _" [50, 0, 50] 60) and
  trsys2.\<tau>rtrancl3p ("_ -\<tau>2-_\<rightarrow>* _" [50, 0, 50] 60)

notation
  trsys1.\<tau>inf_step ("_ -\<tau>1-_\<rightarrow>* \<infinity>" [50, 0] 80) and
  trsys2.\<tau>inf_step ("_ -\<tau>2-_\<rightarrow>* \<infinity>" [50, 0] 80)

notation
  trsys1.\<tau>diverge ("_ -\<tau>1\<rightarrow> \<infinity>" [50] 80) and
  trsys2.\<tau>diverge ("_ -\<tau>2\<rightarrow> \<infinity>" [50] 80)

notation
  trsys1.\<tau>inf_step_table ("_ -\<tau>1-_\<rightarrow>*t \<infinity>" [50, 0] 80) and
  trsys2.\<tau>inf_step_table ("_ -\<tau>2-_\<rightarrow>*t \<infinity>" [50, 0] 80)

notation
  trsys1.\<tau>Runs ("_ \<Down>1 _" [50, 50] 51) and
  trsys2.\<tau>Runs ("_ \<Down>2 _" [50, 50] 51)

lemma simulation_silent1I':
  assumes "\<exists>s2'. (if \<mu>1 s1' s1 then trsys2.silent_moves else trsys2.silent_movet) s2 s2' \<and> s1' \<approx> s2'"
  shows "s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
proof -
  from assms obtain s2' where red: "(if \<mu>1 s1' s1 then trsys2.silent_moves else trsys2.silent_movet) s2 s2'" 
    and bisim: "s1' \<approx> s2'" by blast
  show ?thesis
  proof(cases "\<mu>1 s1' s1")
    case True
    with red have "s2 -\<tau>2\<rightarrow>* s2'" by simp
    thus ?thesis using bisim True by cases(blast intro: rtranclp_into_tranclp1)+
  next
    case False
    with red bisim show ?thesis by auto
  qed
qed

lemma simulation_silent2I':
  assumes "\<exists>s1'. (if \<mu>2 s2' s2 then trsys1.silent_moves else trsys1.silent_movet) s1 s1' \<and> s1' \<approx> s2'"
  shows "s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using assms
by(rule delay_bisimulation_base.simulation_silent1I')

end

locale delay_simulation_obs = delay_bisimulation_base _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 => 'tl1 => 's1 => bool"
  and \<tau>move2 :: "'s2 => 'tl2 => 's2 => bool" +
  assumes simulation:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; \<not> \<tau>move1 s1 tl1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"

locale delay_simulation_diverge = delay_simulation_obs _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 => 'tl1 => 's1 => bool"
  and \<tau>move2 :: "'s2 => 'tl2 => 's2 => bool" +
  assumes simulation_silent:
  "[| s1 \<approx> s2; s1 -\<tau>1\<rightarrow> s1' |] ==> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
  and \<tau>diverge_sim_inv: "s1 \<approx> s2 ==> s1 -\<tau>1\<rightarrow> \<infinity> ==> s2 -\<tau>2\<rightarrow> \<infinity>"
begin

lemma simulation_silents:
  assumes bisim: "s1 \<approx> s2" and moves: "s1 -\<tau>1\<rightarrow>* s1'"
  shows "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
using moves bisim
proof induct
  case base thus ?case by(blast)
next
  case (step s1' s1'')
  from `s1 \<approx> s2 ==> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'` `s1 \<approx> s2`
  obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
  from simulation_silent[OF `s1' \<approx> s2'` `s1' -\<tau>1\<rightarrow> s1''`]
  obtain s2'' where "s2' -\<tau>2\<rightarrow>* s2''" "s1'' \<approx> s2''" by blast
  from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
  with `s1'' \<approx> s2''` show ?case by blast
qed

lemma simulation_\<tau>rtrancl3p:
  "[| s1 -\<tau>1-tls1\<rightarrow>* s1'; s1 \<approx> s2 |]
  ==> \<exists>tls2 s2'. s2 -\<tau>2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct arbitrary: s2 rule: trsys1.\<tau>rtrancl3p.induct)
  case (\<tau>rtrancl3p_refl s)
  thus ?case by(auto intro: \<tau>trsys.\<tau>rtrancl3p.intros)
next
  case (\<tau>rtrancl3p_step s1 s1' tls1 s1'' tl1)
  from simulation[OF `s1 \<approx> s2` `s1 -1-tl1\<rightarrow> s1'` `\<not> \<tau>move1 s1 tl1 s1'`]
  obtain s2' s2'' tl2 where \<tau>red: "s2 -\<tau>2\<rightarrow>* s2'"
    and red: "s2' -2-tl2\<rightarrow> s2''" and n\<tau>: "\<not> \<tau>move2 s2' tl2 s2''"
    and bisim': "s1' \<approx> s2''" and tlsim: "tl1 \<sim> tl2" by blast
  from bisim' `s1' \<approx> s2'' ==> \<exists>tls2 s2'. s2'' -\<tau>2-tls2\<rightarrow>* s2' \<and> s1'' \<approx> s2' \<and> tls1 [\<sim>] tls2`
  obtain tls2 s2''' where IH: "s2'' -\<tau>2-tls2\<rightarrow>* s2'''" "s1'' \<approx> s2'''" "tls1 [\<sim>] tls2" by blast
  from \<tau>red have "s2 -\<tau>2-[]\<rightarrow>* s2'" by(rule trsys2.silent_moves_into_\<tau>rtrancl3p)
  also from red n\<tau> IH(1) have "s2' -\<tau>2-tl2 # tls2\<rightarrow>* s2'''"
    using trsys2.\<tau>rtrancl3p_step by auto
  finally show ?case using IH tlsim by fastforce
next
  case (\<tau>rtrancl3p_\<tau>step s1 s1' tls1 s1'' tl1)
  from `s1 -1-tl1\<rightarrow> s1'` `\<tau>move1 s1 tl1 s1'` have "s1 -\<tau>1\<rightarrow> s1'" .. 
  from simulation_silent[OF `s1 \<approx> s2` this]
  obtain s2' where \<tau>red: "s2 -\<tau>2\<rightarrow>* s2'" and bisim': "s1' \<approx> s2'" by blast
  from \<tau>red have "s2 -\<tau>2-[]\<rightarrow>* s2'" by(rule trsys2.silent_moves_into_\<tau>rtrancl3p)
  also from bisim' `s1' \<approx> s2' ==> \<exists>tls2 s2''. s2' -\<tau>2-tls2\<rightarrow>* s2'' \<and> s1'' \<approx> s2'' \<and> tls1 [\<sim>] tls2`
  obtain tls2 s2'' where IH: "s2' -\<tau>2-tls2\<rightarrow>* s2''" "s1'' \<approx> s2''" "tls1 [\<sim>] tls2" by blast
  note `s2' -\<tau>2-tls2\<rightarrow>* s2''`
  finally show ?case using IH by auto
qed

definition tl1_to_tl2 where
"tl1_to_tl2 = (\<lambda>(s2 :: 's2) (sstls1 :: ('s1 \<times> 's1 \<times> 'tl1 \<times> 's1) llist). unfold_llist
     (\<lambda>(s2, sstls1). lnull sstls1)
     (\<lambda>(s2, sstls1).
        let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in (s2, s2', tl2, s2''))
     (\<lambda>(s2, sstls1). 
        let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in (s2'', ltl sstls1))
     (s2, sstls1))"

lemma simulation_\<tau>inf_step:
  assumes \<tau>inf1: "s1 -\<tau>1-tls1\<rightarrow>* \<infinity>" and bisim: "s1 \<approx> s2"
  shows "\<exists>tls2. s2 -\<tau>2-tls2\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
proof -
  from trsys1.\<tau>inf_step_imp_\<tau>inf_step_table[OF \<tau>inf1]
  obtain sstls1 where \<tau>inf1': "s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>" 
    and tls1: "tls1 = lmap (fst \<circ> snd \<circ> snd) sstls1" by blast
  have [simp]:
    "\<And>s2 sstls1. lnull (tl1_to_tl2 s2 sstls1) \<longleftrightarrow> lnull sstls1"
    "\<And>s2 sstls1. \<not> lnull sstls1 \<Longrightarrow> lhd (tl1_to_tl2 s2 sstls1) =
        (let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in (s2, s2', tl2, s2''))"
    "\<And>s2 sstls1. \<not> lnull sstls1 \<Longrightarrow> ltl (tl1_to_tl2 s2 sstls1) =
        (let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in tl1_to_tl2 s2'' (ltl sstls1))"
    "\<And>s2. tl1_to_tl2 s2 LNil = LNil"
    "\<And>s2 s1 s1' tl1 s1'' stls1'. tl1_to_tl2 s2 (LCons (s1, s1', tl1, s1'') stls1') =
        LCons (s2, SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> 
                                          \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2) 
              (tl1_to_tl2 (snd (snd (SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                                            \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2)))
                           stls1')"
    by(simp_all add: tl1_to_tl2_def split_beta)

  have [simp]: "llength (tl1_to_tl2 s2 sstls1) = llength sstls1"
    by(coinduction arbitrary: s2 sstls1 rule: enat_coinduct)(auto simp add: epred_llength split_beta)
  define sstls2 where "sstls2 = tl1_to_tl2 s2 sstls1"
  with \<tau>inf1' bisim have "\<exists>s1 sstls1. s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity> \<and> sstls2 = tl1_to_tl2 s2 sstls1 \<and> s1 \<approx> s2" by blast
  from \<tau>inf1' bisim have "s2 -\<tau>2-tl1_to_tl2 s2 sstls1\<rightarrow>*t \<infinity>"
  proof(coinduction arbitrary: s2 s1 sstls1)
    case (\<tau>inf_step_table s2 s1 sstls1)
    note \<tau>inf' = `s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>` and bisim = `s1 \<approx> s2`
    from \<tau>inf' show ?case
    proof(cases)
      case (\<tau>inf_step_table_Cons s1' s1'' sstls1' tl1)
      hence sstls1: "sstls1 = LCons (s1, s1', tl1, s1'') sstls1'"
        and \<tau>s: "s1 -\<tau>1\<rightarrow>* s1'" and r: "s1' -1-tl1\<rightarrow> s1''" and n\<tau>: "\<not> \<tau>move1 s1' tl1 s1''"
        and reds1: "s1'' -\<tau>1-sstls1'\<rightarrow>*t \<infinity>" by simp_all
      let ?P = "\<lambda>(s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
      let ?s2tl2s2' = "Eps ?P"
      let ?s2'' = "snd (snd ?s2tl2s2')"
      from simulation_silents[OF `s1 \<approx> s2` \<tau>s]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
      from simulation[OF `s1' \<approx> s2'` r n\<tau>] obtain s2'' s2''' tl2
        where "s2' -\<tau>2\<rightarrow>* s2''" 
        and rest: "s2'' -2-tl2\<rightarrow> s2'''" "\<not> \<tau>move2 s2'' tl2 s2'''" "s1'' \<approx> s2'''" "tl1 \<sim> tl2" by blast
      from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
      with rest have "?P (s2'', tl2, s2''')" by simp
      hence "?P ?s2tl2s2'" by(rule someI)
      then show ?thesis using reds1 sstls1 by fastforce
    next
      case \<tau>inf_step_table_Nil
      hence [simp]: "sstls1 = LNil" and "s1 -\<tau>1\<rightarrow> \<infinity>" by simp_all
      from `s1 -\<tau>1\<rightarrow> \<infinity>` `s1 \<approx> s2` have "s2 -\<tau>2\<rightarrow> \<infinity>" by(simp add: \<tau>diverge_sim_inv)
      thus ?thesis by simp
    qed
  qed
  hence "s2 -\<tau>2-lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)\<rightarrow>* \<infinity>"
    by(rule trsys2.\<tau>inf_step_table_into_\<tau>inf_step)
  moreover have "tls1 [[\<sim>]] lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)"
  proof(rule llist_all2_all_lnthI)
    show "llength tls1 = llength (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1))"
      using tls1 by simp
  next
    fix n
    assume "enat n < llength tls1"
    thus "lnth tls1 n \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)) n"
      using \<tau>inf1' bisim unfolding tls1
    proof(induct n arbitrary: s1 s2 sstls1 rule: less_induct)
      case (less n)
      note IH = `\<And>m s1 s2 sstls1. \<lbrakk> m < n; enat m < llength (lmap (fst \<circ> snd \<circ> snd) sstls1);
                                   s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>; s1 \<approx> s2 \<rbrakk>
                 \<Longrightarrow> lnth (lmap (fst \<circ> snd \<circ> snd) sstls1) m \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)) m`
      from `s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>` show ?case
      proof cases
        case (\<tau>inf_step_table_Cons s1' s1'' sstls1' tl1)
        hence sstls1: "sstls1 = LCons (s1, s1', tl1, s1'') sstls1'"
          and \<tau>s: "s1 -\<tau>1\<rightarrow>* s1'" and r: "s1' -1-tl1\<rightarrow> s1''"
          and n\<tau>: "\<not> \<tau>move1 s1' tl1 s1''" and reds: "s1'' -\<tau>1-sstls1'\<rightarrow>*t \<infinity>" by simp_all
        let ?P = "\<lambda>(s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
        let ?s2tl2s2' = "Eps ?P" let ?tl2 = "fst (snd ?s2tl2s2')" let ?s2'' = "snd (snd ?s2tl2s2')"
        from simulation_silents[OF `s1 \<approx> s2` \<tau>s] obtain s2'
          where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
        from simulation[OF `s1' \<approx> s2'` r n\<tau>] obtain s2'' s2''' tl2
          where "s2' -\<tau>2\<rightarrow>* s2''"
          and rest: "s2'' -2-tl2\<rightarrow> s2'''" "\<not> \<tau>move2 s2'' tl2 s2'''" "s1'' \<approx> s2'''" "tl1 \<sim> tl2" by blast
        from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
        with rest have "?P (s2'', tl2, s2''')" by auto
        hence "?P ?s2tl2s2'" by(rule someI)
        hence "s1'' \<approx> ?s2''" "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
        show ?thesis
        proof(cases n)
          case 0
          with sstls1 `tl1 \<sim> ?tl2` show ?thesis by simp
        next
          case (Suc m)
          hence "m < n" by simp
          moreover have "enat m < llength (lmap (fst \<circ> snd \<circ> snd) sstls1')"
            using sstls1 `enat n < llength (lmap (fst \<circ> snd \<circ> snd) sstls1)` Suc by(simp add: Suc_ile_eq)
          ultimately have "lnth (lmap (fst \<circ> snd \<circ> snd) sstls1') m \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 ?s2'' sstls1')) m"
            using reds `s1'' \<approx> ?s2''` by(rule IH)
          with Suc sstls1 show ?thesis by(simp del: o_apply)
        qed
      next
        case \<tau>inf_step_table_Nil
        with `enat n < llength (lmap (fst \<circ> snd \<circ> snd) sstls1)` have False by simp
        thus ?thesis ..
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed

(* is this enough? *)
end

sublocale delay_bisimulation_diverge \<subseteq> delay_simulation_diverge
by (unfold_locales, rule simulation1, auto simp add: simulation1 simulation_silent1 \<tau>diverge_bisim_inv)

definition \<tau>moves_of_tCFG where 
"\<tau>moves_of_tCFG CFGs step_rel obs get_mem C l C' \<equiv> step_rel CFGs C C' \<and> get_mem C' |` obs = l
  \<and> get_mem C |` obs = l" 

locale tCFG_delay_bisim = delay_bisimulation_diverge where trsys1 = "trsys_of_tCFG CFGs step_rel obs get_mem"
 and trsys2 = "trsys_of_tCFG CFGs' step_rel obs get_mem" 
 and \<tau>move1 = "\<tau>moves_of_tCFG CFGs step_rel obs get_mem" 
 and \<tau>move2 = "\<tau>moves_of_tCFG CFGs' step_rel obs get_mem" for CFGs CFGs' step_rel obs get_mem

locale tCFG_delay_sim = delay_simulation_diverge where trsys1 = "trsys_of_tCFG CFGs step_rel obs get_mem"
 and trsys2 = "trsys_of_tCFG CFGs' step_rel obs get_mem" 
 and \<tau>move1 = "\<tau>moves_of_tCFG CFGs step_rel obs get_mem" 
 and \<tau>move2 = "\<tau>moves_of_tCFG CFGs' step_rel obs get_mem" for CFGs CFGs' step_rel obs get_mem

lemma delay_sim_comp: "\<lbrakk>tCFG_delay_sim sim tlsim CFGs CFGs' step_rel obs get_mem; 
  tCFG_delay_sim sim' tlsim' CFGs' CFGs'' step_rel obs get_mem\<rbrakk> \<Longrightarrow>
tCFG_delay_sim (sim \<circ>\<^sub>B sim') (tlsim \<circ>\<^sub>B tlsim') CFGs CFGs'' step_rel obs get_mem"
apply (clarsimp simp add: tCFG_delay_sim_def, unfold_locales)
apply (clarsimp simp add: bisim_compose_def)
apply (drule delay_simulation_diverge.simulation_\<tau>rtrancl3p)
apply (rule \<tau>trsys.\<tau>rtrancl3p_step, simp+)
apply (rule \<tau>trsys.\<tau>rtrancl3p_refl, simp+)
apply clarsimp
apply (drule delay_simulation_diverge.simulation_\<tau>rtrancl3p, simp+, clarsimp)
(* overshot? *)
oops

lemma delay_bisim_comp: "\<lbrakk>tCFG_delay_bisim sim tlsim CFGs CFGs' step_rel obs get_mem; 
  tCFG_delay_bisim sim' tlsim' CFGs' CFGs'' step_rel obs get_mem\<rbrakk> \<Longrightarrow>
tCFG_delay_bisim (sim \<circ>\<^sub>B sim') (tlsim \<circ>\<^sub>B tlsim') CFGs CFGs'' step_rel obs get_mem"
by (simp add: tCFG_delay_bisim_def delay_bisimulation_diverge_compose)

context TRANS_basics begin

definition (in TRANS_basics) "opt_delay_bisim T sim tlsim step_rel obs get_mem \<equiv> 
  \<forall>\<tau> CFGs. tCFG CFGs instr_edges Seq \<longrightarrow> (\<forall>CFGs'\<in>trans_sf T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and> 
  tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem)"

lemma opt_delay_bisimI [intro]: "(\<And>\<tau> CFGs CFGs'. \<lbrakk>tCFG CFGs instr_edges Seq; CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow>
  tCFG CFGs' instr_edges Seq \<and> tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem) \<Longrightarrow>
  opt_delay_bisim T sim tlsim step_rel obs get_mem"
by (simp add: opt_delay_bisim_def)

lemma opt_delay_bisimD [dest]: "\<lbrakk>opt_delay_bisim T sim tlsim step_rel obs get_mem; 
  tCFG CFGs instr_edges Seq; CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow> tCFG CFGs' instr_edges Seq \<and>
  tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem"
by (simp add: opt_delay_bisim_def)

lemma then_delay_bisim [intro]: "\<lbrakk>opt_delay_bisim T1 sim1 tlsim1 step_rel obs get_mem; 
  opt_delay_bisim T2 sim2 tlsim2 step_rel obs get_mem\<rbrakk> \<Longrightarrow>
  opt_delay_bisim (TThen T1 T2) (sim2 \<circ>\<^sub>B sim1) (tlsim2 \<circ>\<^sub>B tlsim1) step_rel obs get_mem"
apply (clarsimp intro!: opt_delay_bisimI)
apply (drule opt_delay_bisimD, simp+, clarsimp)+
apply (rule delay_bisim_comp, simp_all)
done
(* These work much better than just unfolding the definition. *)

lemma applysome_delay_bisim: "\<lbrakk>opt_delay_bisim T sim tlsim step_rel obs get_mem; 
  tCFG CFGs instr_edges Seq; apply_some (trans_sf T) \<tau> CFGs CFGs'\<rbrakk> \<Longrightarrow> 
  tCFG CFGs' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_delay_bisim sim' tlsim' CFGs' CFGs step_rel obs get_mem)"
apply (drule_tac P="\<lambda>t \<tau> G G'. t = trans_sf T \<and> tCFG G instr_edges Seq \<longrightarrow> 
  (tCFG G' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_delay_bisim sim' tlsim' G' G step_rel obs get_mem))" 
  in apply_some.induct, auto)
apply (rule_tac x="(=)" in exI, rule_tac x="(=)" in exI, unfold_locales, force+)
apply (drule opt_delay_bisimD, simp+, clarsimp)
apply (rule exI, rule exI, rule delay_bisim_comp, simp+)
done

definition "trans_delay_bisim T step_rel obs get_mem \<equiv> 
  \<forall>\<tau> CFGs. tCFG CFGs instr_edges Seq \<longrightarrow> (\<forall>CFGs' \<in> trans_sf T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and> 
  (\<exists>sim tlsim. tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem))"

lemma trans_delay_bisimI [intro]: "(\<And>\<tau> CFGs CFGs'. \<lbrakk>tCFG CFGs instr_edges Seq; CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow>
  tCFG CFGs' instr_edges Seq \<and> (\<exists>sim tlsim. tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem)) \<Longrightarrow>
  trans_delay_bisim T step_rel obs get_mem"
by (simp add: trans_delay_bisim_def)

lemma trans_delay_bisimD [dest]: "\<lbrakk>trans_delay_bisim T step_rel obs get_mem; 
  tCFG CFGs instr_edges Seq; CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow> tCFG CFGs' instr_edges Seq \<and>
  (\<exists>sim tlsim. tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem)"
by (simp add: trans_delay_bisim_def)

lemma opt_delay_bisim_trans [intro]: "opt_delay_bisim T sim tlsim step_rel obs get_mem \<Longrightarrow> 
  trans_delay_bisim T step_rel obs get_mem"
by (force simp add: opt_delay_bisim_def trans_delay_bisim_def)

definition "cond_delay_bisim P T step_rel obs get_mem \<equiv> \<forall>\<tau> CFGs. P \<tau> CFGs \<and> tCFG CFGs instr_edges Seq \<longrightarrow> 
  (\<forall>CFGs' \<in> trans_sf T \<tau> CFGs. tCFG CFGs' instr_edges Seq \<and> 
  (\<exists>sim tlsim. tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem))"

lemma cond_delay_bisimI [intro]: "(\<And>\<tau> CFGs CFGs'. \<lbrakk>P \<tau> CFGs; tCFG CFGs instr_edges Seq; 
  CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow> tCFG CFGs' instr_edges Seq \<and> 
  (\<exists>sim tlsim. tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem)) \<Longrightarrow>
  cond_delay_bisim P T step_rel obs get_mem"
by (force simp add: cond_delay_bisim_def)

lemma cond_delay_bisimD [dest]: "\<lbrakk>cond_delay_bisim P T step_rel obs get_mem; P \<tau> CFGs;
  tCFG CFGs instr_edges Seq; CFGs' \<in> trans_sf T \<tau> CFGs\<rbrakk> \<Longrightarrow> tCFG CFGs' instr_edges Seq \<and>
  (\<exists>sim tlsim. tCFG_delay_bisim sim tlsim CFGs' CFGs step_rel obs get_mem)"
by (force simp add: cond_delay_bisim_def)

lemma applyall_delay_bisim [intro]: "opt_delay_bisim T sim tlsim step_rel obs get_mem \<Longrightarrow> 
  trans_delay_bisim (TApplyAll T) step_rel obs get_mem"
apply (clarsimp simp add: trans_delay_bisim_def)
by (metis applysome_delay_bisim)

lemma match_cond_delay_bisim [intro]: "cond_delay_bisim (\<lambda>\<tau> CFGs. \<exists>\<sigma> \<tau>'. side_cond_sf \<phi> \<sigma> CFGs \<and> 
  part_matches \<sigma> \<tau>' \<and> \<tau> = part_extend \<tau>' (cond_fv pred_fv \<phi>) \<sigma>) T step_rel obs get_mem \<Longrightarrow>
  trans_delay_bisim (TMatch \<phi> T) step_rel obs get_mem"
apply (clarsimp simp add: trans_delay_bisim_def cond_delay_bisim_def)
by metis

lemma then_cond_delay_bisim [intro]: "\<lbrakk>cond_delay_bisim P T1 step_rel obs get_mem; 
  cond_delay_bisim P T2 step_rel obs get_mem;
  \<forall>\<tau> CFGs CFGs'. P \<tau> CFGs \<and> CFGs' \<in> trans_sf T1 \<tau> CFGs \<longrightarrow> P \<tau> CFGs'\<rbrakk> \<Longrightarrow>
  cond_delay_bisim P (TThen T1 T2) step_rel obs get_mem"
apply (clarsimp intro!: cond_delay_bisimI)
apply (drule cond_delay_bisimD, simp+, clarsimp)
apply (erule_tac x=\<tau> in allE, erule_tac x=CFGs in allE, erule_tac x=CFGs'a in allE, simp)
apply (drule cond_delay_bisimD, simp+, clarsimp)
apply (rule exI, rule exI, rule delay_bisim_comp, simp+)
done

lemma applysome_cond_delay_bisim: "\<lbrakk>apply_some (trans_sf T) \<tau> CFGs CFGs'; 
  tCFG CFGs instr_edges Seq; cond_delay_bisim P T step_rel obs get_mem;
  \<forall>\<tau> CFGs CFGs'. P \<tau> CFGs \<and> CFGs' \<in> trans_sf T \<tau> CFGs \<longrightarrow> P \<tau> CFGs'; P \<tau> CFGs\<rbrakk> \<Longrightarrow> 
  tCFG CFGs' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_delay_bisim sim' tlsim' CFGs' CFGs step_rel obs get_mem)"
apply (drule_tac P="\<lambda>t \<tau> G G'. t = trans_sf T \<and> P \<tau> G \<and> tCFG G instr_edges Seq \<longrightarrow> 
  (tCFG G' instr_edges Seq \<and> (\<exists>sim' tlsim'. tCFG_delay_bisim sim' tlsim' G' G step_rel obs get_mem))" 
  in apply_some.induct, simp_all)
apply clarsimp
apply (rule_tac x="(=)" in exI, rule_tac x="(=)" in exI, unfold_locales, force, force, force, force,
  force)
apply clarsimp
apply (erule_tac x=\<tau>' in allE, erule_tac x=G in allE, erule_tac x=G' in allE, simp)
apply (drule_tac CFGs=G in cond_delay_bisimD, simp+, clarsimp)
apply (rule exI, rule exI, rule delay_bisim_comp, simp+)
done

lemma applyall_cond_delay_bisim [intro]: "\<lbrakk>cond_delay_bisim P T step_rel obs get_mem; 
  \<forall>\<tau> CFGs CFGs'. P \<tau> CFGs \<and> CFGs' \<in> trans_sf T \<tau> CFGs \<longrightarrow> P \<tau> CFGs'\<rbrakk> \<Longrightarrow>
  cond_delay_bisim P (TApplyAll T) step_rel obs get_mem"
apply (clarsimp intro!: cond_delay_bisimI)
apply (drule applysome_cond_delay_bisim, force simp add: cond_delay_bisim_def)
apply simp+
done

end

end
