theory simple_memory_machine
imports "branches/Morpheus/generalized_control_flow_graph" loc_can_do
begin

datatype 'val simp_mem_state = FreeSMM | UninitSMM | StoredSMM "'val"

datatype simp_mem_state_finite = FreeSMMf | UninitSMMf | StoredSMMf

type_synonym ('loc,'val) node = "'loc \<Rightarrow> 'val simp_mem_state"

type_synonym 'loc node_finite = "'loc \<Rightarrow> simp_mem_state_finite"

locale one_loc_locale =
  fixes loc :: "'loc"

declare[[show_types = false]]
declare[[show_sorts = false]]

locale simple_location_machine_one_loc_locale =
       one_loc_locale where loc = "loc :: 'loc" for loc

context simple_location_machine_one_loc_locale
begin
definition SMM_loc where
 "SMM_loc ::
   ('val simp_mem_state,('thread, 'loc,'val) access,'val simp_mem_state)
   generalized_control_flow_graph \<equiv>
 \<lparr>Instructions = (UNIV :: 'val simp_mem_state set),
  Directions = (UNIV :: ('thread, 'loc,'val) access set),
  edgeTyping =  (\<lambda> n. case n of FreeSMM \<Rightarrow>
                      {\<lambda> p. (case p of (Alloc t l) \<Rightarrow> (if l = loc then 1 else 0)
                          | _ \<Rightarrow> 0) }
                    | UninitSMM \<Rightarrow> 
                      {\<lambda>p. case p of (Free t l) \<Rightarrow> (if l = loc then 1 else 0)
                          | (Write t l v) \<Rightarrow> (if l = loc then 1 else 0)
                          | _ \<Rightarrow> 0 }
                    | StoredSMM v \<Rightarrow>
                      {\<lambda>p. case p of (Free t l) \<Rightarrow> (if l = loc then 1 else 0)
                          | (Read t l v') \<Rightarrow> (if (l = loc) \<and> (v = v') then 1 else 0)
                          | (Write t l v') \<Rightarrow> (if l = loc then 1 else 0)
                          | (ARW t l v' v'') \<Rightarrow> (if l = loc then 1 else 0)
                          | _ \<Rightarrow> 0 }),
  Nodes = (UNIV :: 'val simp_mem_state set),
  Edges = (\<lambda> n. case n of FreeSMM \<Rightarrow>
                      {p. (case p of (Alloc t l,m) \<Rightarrow> ((m = UninitSMM) \<and> l = loc)
                          | _ \<Rightarrow> False) }
                    | UninitSMM \<Rightarrow> 
                      {p. case p of (Free t l,m) \<Rightarrow> ((m = FreeSMM) \<and> l = loc)
                          | (Write t l v,m) \<Rightarrow> ((m = StoredSMM v) \<and> l = loc)
                          | _ \<Rightarrow> False }
                    | StoredSMM v \<Rightarrow>
                      {p. case p of (Free t l,m) \<Rightarrow> ((m = FreeSMM) \<and> l = loc)
                          | (Read t l v',m) \<Rightarrow> (v' = v \<and> m = n \<and> l = loc)
                          | (Write t l v',m) \<Rightarrow> ((m = StoredSMM v') \<and> l = loc)
                          | (ARW t l v' v'',m) \<Rightarrow> ((*(v' = v) \<and>*) (m = StoredSMM v'') \<and> l = loc)
                          | _ \<Rightarrow> False }),
  labeling = \<lambda> l. l
    \<rparr>"

lemma SMM_Loc_UnboundedGeneralizedControlFlowGraph: 
"UnboundedGeneralizedControlFlowGraph (Instructions SMM_loc) (Directions SMM_loc)
     (edgeTyping SMM_loc) (Nodes SMM_loc) (Edges SMM_loc) (labeling SMM_loc)"
apply (auto simp add: SMM_loc_def UnboundedGeneralizedControlFlowGraph_def)
apply (case_tac n,auto)
apply (rule ext)
apply (case_tac d)
apply (simp_all)
apply (rule ext)
apply (case_tac d)
apply (simp_all)
apply (rule ext)
apply (case_tac d)
apply (auto)
done
    
interpretation UnboundedGeneralizedControlFlowGraph
 where Nodes = "Nodes SMM_loc" 
 and Instructions = "Instructions SMM_loc"
 and Directions = "Directions SMM_loc"
 and Edges = "Edges SMM_loc"
 and edgeTyping = "edgeTyping SMM_loc"
 and labeling = "labeling SMM_loc"
by (rule SMM_Loc_UnboundedGeneralizedControlFlowGraph)

end
(*
locale simple_location_machine_one_loc_finite_locale =
        one_loc_locale where loc = "loc :: 'loc" for loc

context simple_location_machine_one_loc_finite_locale
begin
print_context
(* Why can't we do sublocale simple_location_machine_locale  in 2015 but can in 2016? *)
*)

definition SMM_loc_finite where
  "SMM_loc_finite ::
    (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph \<equiv>
   \<lparr>Instructions = (UNIV :: simp_mem_state_finite set),
  Directions = (UNIV :: ('thread, 'loc,'val) access set),
  edgeTyping =  (\<lambda> n. case n of FreeSMMf \<Rightarrow>
                      {\<lambda> p. (case p of (Alloc t l) \<Rightarrow> 1 
                          | _ \<Rightarrow> 0) }
                    | UninitSMMf \<Rightarrow> 
                      {\<lambda>p. case p of (Free t l) \<Rightarrow> 1 
                          | (Write t l v) \<Rightarrow> 1 
                          | _ \<Rightarrow> 0 }
                    | StoredSMMf \<Rightarrow>
                      {\<lambda>p. case p of (Free t l) \<Rightarrow> 1 
                          | (Read t l v') \<Rightarrow> 1 
                          | (Write t l v') \<Rightarrow> 1 
                          | (ARW t l v' v'') \<Rightarrow> 1
                          | _ \<Rightarrow> 0 }),
  Nodes = (UNIV :: simp_mem_state_finite set),
  Edges = (\<lambda> n. case n of FreeSMMf \<Rightarrow>
                      {p. (case p of (Alloc t l,m) \<Rightarrow> (m = UninitSMMf)
                          | _ \<Rightarrow> False) }
                    | UninitSMMf \<Rightarrow> 
                      {p. case p of (Free t l,m) \<Rightarrow> (m = FreeSMMf)
                          | (Write t l v,m) \<Rightarrow> (m = StoredSMMf )
                          | _ \<Rightarrow> False }
                    | StoredSMMf \<Rightarrow>
                      {p. case p of (Free t l,m) \<Rightarrow> (m = FreeSMMf)
                          | (Read t l v',m) \<Rightarrow> (m = n)
                          | (Write t l v',m) \<Rightarrow> (m = StoredSMMf)
                          | (ARW t l v' v'', m) \<Rightarrow> (m = StoredSMMf)
                          | _ \<Rightarrow> False }),
  labeling = \<lambda> l. l
    \<rparr>" 

lemma SMM_loc_finite_UnboundedGeneralizedControlFlowGraph:
"UnboundedGeneralizedControlFlowGraph (Instructions SMM_loc_finite)
     (Directions SMM_loc_finite) (edgeTyping SMM_loc_finite) (Nodes SMM_loc_finite)
     (Edges SMM_loc_finite) (labeling SMM_loc_finite)"
apply (auto simp add: SMM_loc_finite_def UnboundedGeneralizedControlFlowGraph_def)
apply (case_tac n,auto)
apply (rule ext)
apply (case_tac d)
apply (simp_all)
apply (rule ext)
apply (case_tac d)
apply (simp_all)
apply (rule ext)
apply (case_tac d)
apply (auto)
done

(*  I need to learn what the limitations on multiple interpretations are. --ELG *)
interpretation UnboundedGeneralizedControlFlowGraph
 where Nodes = "Nodes SMM_loc_finite" 
 and Instructions = "Instructions SMM_loc_finite"
 and Directions = "Directions SMM_loc_finite"
 and Edges = "Edges SMM_loc_finite"
 and edgeTyping = "edgeTyping SMM_loc_finite"
 and labeling = "labeling SMM_loc_finite"
apply  (rule SMM_loc_finite_UnboundedGeneralizedControlFlowGraph)
done


term SMM_loc_finite
term "get_loc (a::('thread, 'loc,'val) access)"
(*
term "more_update SMM_loc_finite"

term  "generalized_control_flow_graph.more_update \<lparr> Participants = (UNIV :: 'loc set),
Interpretation = 
  (\<lambda> ((n::'loc \<Rightarrow> simp_mem_state_finite),(s::'loc \<Rightarrow> 'val option)).
   \<lambda> (a::('thread, 'loc,'val) access).
   \<lambda> ((m::'loc \<Rightarrow> simp_mem_state_finite),(t::'loc \<Rightarrow> 'val option)). 
     (\<forall> (thisloc::'loc). 
               (case n thisloc of FreeSMMf \<Rightarrow>
                 (case (a::('thread, 'loc,'val) access) of Alloc th loc \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = UninitSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)
                 | UninitSMMf \<Rightarrow>
                  (case (a::('thread, 'loc,'val) access) of Free th loc \<Rightarrow> 
                     ((loc = thisloc) \<and> (m loc = FreeSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Write th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)
                 | StoredSMMf \<Rightarrow>
                  (case (a::('thread, 'loc,'val) access) of Free th loc \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = FreeSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Write th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Read th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and>
                                        (s loc = Some v) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)))) \<rparr>"

term "SMM_loc_finite \<lparr> Participants = (UNIV :: 'loc set),
Interpretation = 
  (\<lambda> ((n::'loc \<Rightarrow> simp_mem_state_finite),(s::'loc \<Rightarrow> 'val option)).
   \<lambda> (a::('thread, 'loc,'val) access).
   \<lambda> ((m::'loc \<Rightarrow> simp_mem_state_finite),(t::'loc \<Rightarrow> 'val option)). 
     (\<forall> (thisloc::'loc). 
               (case n thisloc of FreeSMMf \<Rightarrow>
                 (case (a::('thread, 'loc,'val) access) of Alloc th loc \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = UninitSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)
                 | UninitSMMf \<Rightarrow>
                  (case (a::('thread, 'loc,'val) access) of Free th loc \<Rightarrow> 
                     ((loc = thisloc) \<and> (m loc = FreeSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Write th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)
                 | StoredSMMf \<Rightarrow>
                  (case (a::('thread, 'loc,'val) access) of Free th loc \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = FreeSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Write th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Read th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and>
                                        (s loc = Some v) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)))) \<rparr>"
*)
definition SMM_loc_finite_interp where
(* 
'instr = simp_mem_state_finite
'dir = ('thread, 'loc,'val option) access
'node = simp_mem_state_finite
'participant = 'loc
'state = 'loc \<Rightarrow> 'val option
*)
  "SMM_loc_finite_interp  ::
    (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite,'loc,'loc \<Rightarrow> 'val option)
    generalized_control_flow_graph_interpretation \<equiv>
\<lparr> Instructions = Instructions (SMM_loc_finite :: (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph),
Directions = Directions (SMM_loc_finite :: (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph),
edgeTyping = edgeTyping (SMM_loc_finite :: (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph),
Nodes = Nodes (SMM_loc_finite :: (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph),
Edges = Edges (SMM_loc_finite :: (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph),
labeling = labeling (SMM_loc_finite :: (simp_mem_state_finite,('thread, 'loc,'val) access,simp_mem_state_finite)
    generalized_control_flow_graph),
Participants = (UNIV :: 'loc set),
Interpretation = 
  (\<lambda> ((n::'loc \<Rightarrow> simp_mem_state_finite),(s::'loc \<Rightarrow> 'val option)).
   \<lambda> (a::('thread, 'loc,'val) access).
   \<lambda> ((m::'loc \<Rightarrow> simp_mem_state_finite),(t::'loc \<Rightarrow> 'val option)).
     case a of Alloc th loc \<Rightarrow>
         ((\<forall> otherloc. (otherloc \<noteq> loc) \<longrightarrow>
             ((n otherloc = m otherloc) \<and> (s otherloc = t otherloc))) \<and>
          (n loc = FreeSMMf) \<and> (m loc = UninitSMMf) \<and> (t loc = None))
      | Free th loc \<Rightarrow>
        ((\<forall> otherloc. (otherloc \<noteq> loc) \<longrightarrow>
            ((n otherloc = m otherloc) \<and> (s otherloc = t otherloc))) \<and>
         ((n loc = UninitSMMf) \<or> (n loc = StoredSMMf)) \<and> (m loc = FreeSMMf) \<and>
         (t loc = None))
      | Read th loc v \<Rightarrow>
        ((\<forall> otherloc. (otherloc \<noteq> loc) \<longrightarrow>
            ((n otherloc = m otherloc) \<and> (s otherloc = t otherloc))) \<and>
         (n loc = StoredSMMf) \<and> (m loc = StoredSMMf) \<and>
         (s loc = Some v) \<and> (t loc = Some v))
      | Write th loc v \<Rightarrow>
        ((\<forall> otherloc. (otherloc \<noteq> loc) \<longrightarrow>
            ((n otherloc = m otherloc) \<and> (s otherloc = t otherloc))) \<and>
         ((n loc = StoredSMMf) \<or> (n loc = UninitSMMf)) \<and> (m loc = StoredSMMf) \<and>
         (t loc = Some v))
      | ARW th loc v v' \<Rightarrow>
        ((\<forall> otherloc. (otherloc \<noteq> loc) \<longrightarrow>
            ((n otherloc = m otherloc) \<and> (s otherloc = t otherloc))) \<and>
         (n loc = StoredSMMf) \<and> (m loc = StoredSMMf) \<and>
         (s loc = Some v) \<and> (t loc = Some v'))
(*
     (\<forall> (thisloc::'loc). 
               (case n thisloc of FreeSMMf \<Rightarrow>
                 (case (a::('thread, 'loc,'val) access) of Alloc th loc \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = UninitSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)
                 | UninitSMMf \<Rightarrow>
                  (case (a::('thread, 'loc,'val) access) of Free th loc \<Rightarrow> 
                     ((loc = thisloc) \<and> (m loc = FreeSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Write th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)
                 | StoredSMMf \<Rightarrow>
                  (case (a::('thread, 'loc,'val) access) of Free th loc \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = FreeSMMf) \<and> (t loc = None)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Write th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | Read th loc v \<Rightarrow>
                     ((loc = thisloc) \<and> (m loc = StoredSMMf) \<and>
                                        (s loc = Some v) \<and> (t loc = Some v)) \<or>
                     ((loc \<noteq> thisloc) \<and> (m loc = n loc) \<and> (t loc = s loc))
                   | _ \<Rightarrow> False)))
*)
)
                \<rparr>"

lemma SMM_loc_finite_interp_UnboundedGeneralizedControlFlowGraphInterpretation:
"UnboundedGeneralizedControlFlowGraphInterpretation (Instructions SMM_loc_finite_interp)
     (Directions SMM_loc_finite_interp) (edgeTyping SMM_loc_finite_interp)
     (Nodes SMM_loc_finite_interp) (Edges SMM_loc_finite_interp)
     (labeling SMM_loc_finite_interp) (Participants SMM_loc_finite_interp)
     (Interpretation SMM_loc_finite_interp)"
apply (simp add: UnboundedGeneralizedControlFlowGraphInterpretation_def
                 SMM_loc_finite_interp_def)
apply (rule conjI)
 apply (rule SMM_loc_finite_UnboundedGeneralizedControlFlowGraph)
apply (simp add: UnboundedGeneralizedControlFlowGraphInterpretation_axioms_def
                      SMM_loc_finite_def)
apply (rule conjI)
 apply clarify
 apply (case_tac "d", simp_all)
apply clarsimp
apply (case_tac "d", simp_all)
    apply (case_tac "n p", simp_all)
      apply (case_tac "p = x12", simp_all)
     apply (case_tac "p = x12", simp_all)
    apply (case_tac "p = x12", simp_all)
   apply (case_tac "n p", simp_all)
     apply (case_tac "p = x22", simp_all)
    apply (case_tac "p = x22", simp_all)
   apply (case_tac "p = x22", simp_all)
  apply (case_tac "n p", simp_all)
    apply (case_tac "p = x32", simp_all)
   apply (case_tac "p = x32", simp_all)
  apply (case_tac "p = x32", simp_all)
 apply (case_tac "n p", simp_all)
    apply (case_tac "p = x42", simp_all)
   apply (case_tac "p = x42", simp_all)
  apply (case_tac "p = x42", simp_all)
apply (case_tac "n p", simp_all)
  apply (case_tac "p = x52", simp_all)
 apply (case_tac "p = x52", simp_all)
apply (case_tac "p = x52", simp_all)
done

interpretation UnboundedGeneralizedControlFlowGraphInterpretation
 where Nodes = "Nodes SMM_loc_finite_interp" 
 and Instructions = "Instructions SMM_loc_finite_interp"
 and Directions = "Directions SMM_loc_finite_interp"
 and Edges = "Edges SMM_loc_finite_interp"
 and edgeTyping = "edgeTyping SMM_loc_finite_interp"
 and labeling = "labeling SMM_loc_finite_interp"
 and Participants = "Participants SMM_loc_finite_interp"
 and Interpretation = "Interpretation SMM_loc_finite_interp"
apply (rule SMM_loc_finite_interp_UnboundedGeneralizedControlFlowGraphInterpretation)
done

(* end (* context *) *)


(*
definition SMM_locs_finite :: "('loc \<Rightarrow> simp_mem_state_finite,('thread, 'loc,'val) access,
                         'loc \<Rightarrow> simp_mem_state_finite) generalized_control_flow_graph" where
 "SMM_locs_finite \<equiv> \<lparr> Instructions = (UNIV :: 'loc node_finite set),
  Directions = (UNIV :: ('thread, 'loc,'val) access set),
  edgeTyping = 
 (\<lambda> i:: ('loc \<Rightarrow> simp_mem_state_finite).
   (\<Union>l\<in>UNIV. (edgeTyping((simple_location_machine_one_loc_finite_locale.SMM_loc_finite l)) (i l)))),
  Nodes = (UNIV :: 'loc node_finite set),
  Edges = ((\<lambda> n. \<Union> loc\<in>UNIV. (\<lambda> (a,m). (a,(\<lambda> l. (if l = loc then m else n l)))) `
           (Edges(simple_location_machine_one_loc_finite_locale.SMM_loc_finite loc) (n loc)))
          ::('loc \<Rightarrow> simp_mem_state_finite) \<Rightarrow>
           (('thread, 'loc, 'val) access \<times> ('loc \<Rightarrow> simp_mem_state_finite)) set),
  labeling = \<lambda> l. l
    \<rparr>"
    
interpretation UnboundedGeneralizedControlFlowGraph
 where Nodes = "Nodes SMM_locs_finite"
 and Instructions = "Instructions SMM_locs_finite"
 and Directions = "Directions SMM_locs_finite"
 and Edges = "Edges SMM_locs_finite"
 and edgeTyping = "edgeTyping SMM_locs_finite"
 and labeling = "labeling SMM_locs_finite"
apply (unfold_locales)
apply (clarsimp  simp add: SMM_locs_finite_def)
apply (clarsimp  simp add: SMM_locs_finite_def)
prefer 2
apply (clarsimp  simp add: SMM_locs_finite_def)
apply (simp only: SMM_locs_finite_def)
apply (subgoal_tac "(\<lambda>d. card {m \<in> UNIV.
                    (d, m)
                    \<in> (\<Union>loc. (\<lambda>(a, m). (a, \<lambda>l. if l = loc then m else n l)) `
                       Edges (simple_location_machine_one_loc_finite_locale.SMM_loc_finite loc) (n loc))
                        })
         \<in> (\<lambda>i. \<Union>l. edgeTyping (simple_location_machine_one_loc_finite_locale.SMM_loc_finite l) (i l)) n")
apply simp

apply simp

(* New, from Elsa *)
apply (simp only: simple_location_machine_one_loc_finite_locale.SMM_loc_finite_def)
oops


definition SMM_locs :: "('loc \<Rightarrow> 'val simp_mem_state,('thread, 'loc,'val) access,
                         'loc \<Rightarrow> 'val simp_mem_state) generalized_control_flow_graph" where
 "SMM_locs \<equiv> \<lparr> Instructions = (UNIV :: ('loc,'val) node set),
  Directions = (UNIV :: ('thread, 'loc,'val) access set),
  edgeTyping =  (\<lambda> i:: ('loc \<Rightarrow> 'val simp_mem_state).
   (\<Union>l\<in>UNIV. (edgeTyping((simple_location_machine_one_loc_locale.SMM_loc l)) (i l))))
(* (\<lambda> i:: ('loc \<Rightarrow> 'val simp_mem_state).{dn.
       (\<exists> loc::'loc. (dn::(('thread, 'loc, 'val) access \<Rightarrow> nat)) \<in>
          (edgeTyping((simple_location_machine_one_loc_locale.SMM_loc loc)*),
  (*  
  case a of acc\<Rightarrow>num | (\<forall> loc. (if loc = get_loc(acc) then a
    \<in> edgeTyping(SMM_loc loc) (n loc) else m loc = n loc))})
    *)
  Nodes = (UNIV :: ('loc,'val) node set),
  Edges = ((\<lambda> n. \<Union> loc\<in>UNIV. (\<lambda> (a,m). (a,(\<lambda> l. (if l = loc then m else n l)))) `
           (Edges(simple_location_machine_one_loc_locale.SMM_loc loc) (n loc)))
          ::('loc \<Rightarrow> 'val simp_mem_state) \<Rightarrow>
           (('thread, 'loc, 'val) access \<times> ('loc \<Rightarrow>'val simp_mem_state)) set
(* {(a,m) . (\<exists> loc . ((a,m loc) \<in> 
    Edges(simple_location_machine_one_loc_locale.SMM_loc loc) (n loc)) \<and> 
    (\<forall> loc' . (loc' \<noteq> loc) \<longrightarrow> (m loc' = n loc')))}
*)
          ),
  labeling = \<lambda> l. l
    \<rparr>"


interpretation UnboundedGeneralizedControlFlowGraph
 where Nodes = "Nodes SMM_locs" 
 and Instructions = "Instructions SMM_locs"
 and Directions = "Directions SMM_locs"
 and Edges = "Edges SMM_locs"
 and edgeTyping = "edgeTyping SMM_locs"
 and labeling = "labeling SMM_locs"
apply (unfold_locales)
apply (clarsimp  simp add: SMM_locs_def)
apply (clarsimp  simp add: SMM_locs_def)
prefer 2
apply (clarsimp  simp add: SMM_locs_def)
apply (simp only: SMM_locs_def)
apply (subgoal_tac "(\<lambda>d. card {m \<in> UNIV.
                    (d, m)
                    \<in> (\<Union>loc. (\<lambda>(a, m). (a, \<lambda>l. if l = loc then m else n l)) `
                       Edges (simple_location_machine_one_loc_locale.SMM_loc loc) (n loc))
                        })
         \<in> (\<lambda>i. \<Union>l. edgeTyping (simple_location_machine_one_loc_locale.SMM_loc l) (i l)) n")
apply simp

apply simp

(* New, from Elsa *)
apply (simp only: simple_location_machine_one_loc_locale.SMM_loc_def)
oops
*)
term "Trsys"

term "Edges (simple_location_machine_one_loc_locale.SMM_loc loc)"
term "(Edges SMM_loc_finite_interp)"
         

lemma "\<exists>s. rtrancl3p (\<lambda>n d m. (d, m) \<in> Edges SMM_loc_finite n) FreeSMMf [Alloc t l] s"
apply (rule_tac ?r = "(\<lambda>n d m. (d, m) \<in> Edges SMM_loc_finite n)" 
             and ?x1.0 = "FreeSMMf" in rtrancl3p.induct)


apply (rule_tac x = "" in exI)
thm exI
sorry
definition l_can_do_SMM where
  "l_can_do_SMM l a =
   (\<exists> s. (*Trsys*) Auxiliary.rtrancl3p 
         (\<lambda> (n::simp_mem_state_finite). \<lambda> d. \<lambda> m. ((d::('thread, 'loc,'val) access),m) \<in>
          (Edges SMM_loc_finite_interp) n)
         FreeSMMf
         (List.rev (a#l)) s)"
         
interpretation loc_can_do where
  l_can_do = "l_can_do_SMM"
apply (unfold_locales)
apply (simp add: l_can_do_SMM_def SMM_loc_finite_interp_def)
apply (erule rtrancl3p.induct)

prefer 2
apply (simp add: l_can_do_SMM_def)
oops
         
(*
interpretation loc_can_do where
  l_can_do = "l_can_do_SMM"
proof
 fix t::"'thread" and l::"'loc" 
 show "l_can_do_SMM [] (Alloc t l)"
 proof (simp add: l_can_do_SMM_def Edges_def SMM_loc_def del: List.append.simps, simp)
  show " \<exists>s. rtrancl3p
         (\<lambda>n d m.
             (d, m)
             \<in> (case n of
                 FreeSMM \<Rightarrow>
                   {p. case p of (Alloc t l, m) \<Rightarrow> m = UninitSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
                 | UninitSMM \<Rightarrow>
                     {p. case p of (Write t l v, m) \<Rightarrow> m = StoredSMM v(*  \<and> l = loc *)
                         | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
                 | StoredSMM v \<Rightarrow>
                     {p. case p of (Read t l v', m) \<Rightarrow> v' = v \<and> m = n(*  \<and> l = loc *)
                         | (Write t l v', m) \<Rightarrow> m = StoredSMM v'(*  \<and> l = loc *)
                         | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}))
         FreeSMM ([] @ [Alloc t l]) s"
  proof (rule_tac x="UninitSMM" in exI)
  show "rtrancl3p
     (\<lambda>n d m.
         (d, m)
         \<in> (case n of
             FreeSMM \<Rightarrow>
               {p. case p of (Alloc t l, m) \<Rightarrow> m = UninitSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
             | UninitSMM \<Rightarrow>
                 {p. case p of (Write t l v, m) \<Rightarrow> m = StoredSMM v(*  \<and> l = loc *)
                     | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
             | StoredSMM v \<Rightarrow>
                 {p. case p of (Read t l v', m) \<Rightarrow> v' = v \<and> m = n(*  \<and> l = loc *)
                     | (Write t l v', m) \<Rightarrow> m = StoredSMM v'(*  \<and> l = loc *)
                     | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}))
     FreeSMM ([] @ [Alloc t l]) UninitSMM "
  proof (rule_tac a' = "FreeSMM" in rtrancl3p_step)
   show 
   "rtrancl3p
     (\<lambda>n d m.
         (d, m)
         \<in> (case n of
             FreeSMM \<Rightarrow>
               {p. case p of (Alloc t l, m) \<Rightarrow> m = UninitSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
             | UninitSMM \<Rightarrow>
                 {p. case p of (Write t l v, m) \<Rightarrow> m = StoredSMM v(*  \<and> l = loc *)
                     | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
             | StoredSMM v \<Rightarrow>
                 {p. case p of (Read t l v', m) \<Rightarrow> v' = v \<and> m = n(*  \<and> l = loc *)
                     | (Write t l v', m) \<Rightarrow> m = StoredSMM v'(*  \<and> l = loc *)
                     | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}))
     FreeSMM [] FreeSMM"
     by simp
     next
     show "(Alloc t l, UninitSMM)
    \<in> (case FreeSMM of
        FreeSMM \<Rightarrow> {p. case p of (Alloc t l, m) \<Rightarrow> m = UninitSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
        | UninitSMM \<Rightarrow>
            {p. case p of (Write t l v, m) \<Rightarrow> m = StoredSMM v(*  \<and> l = loc *)
                | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False}
        | StoredSMM v \<Rightarrow>
            {p. case p of (Read t l v', m) \<Rightarrow> v' = v \<and> m = FreeSMM(*  \<and> l = loc *)
                | (Write t l v', m) \<Rightarrow> m = StoredSMM v'(*  \<and> l = loc *)
                | (Free t l, m) \<Rightarrow> m = FreeSMM(*  \<and> l = loc *) | (_, m) \<Rightarrow> False})"
     proof simp

     *)
end


