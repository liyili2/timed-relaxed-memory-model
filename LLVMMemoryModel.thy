theory LLVMConcurrencyModel
imports Main Map LLVMExecutionModel
begin

locale memoryModel = executionModel =
      fixes programs :: "'id \<Rightarrow> ('id,'a) program option"
        and counter :: "nat \<Rightarrow> nat"
        and findInSpecReg :: "((nat \<times> 'id) \<Rightarrow> 'id element option)
                           \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'id \<Rightarrow> 'id element option"
        and findPathToFather :: "(nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list option"
        and isFather :: "(nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" (* pre is fater of later*)
        and usesInAllDefs :: "('id,'a) program \<Rightarrow> 'id set \<Rightarrow> 'id set \<Rightarrow> bool"
        and rewriteMap :: "((nat \<times> 'id) \<Rightarrow> 'id element option) \<Rightarrow> ('id \<Rightarrow> 'id element option)"
        and getChildren :: "(nat \<Rightarrow> nat set option) \<Rightarrow> nat \<Rightarrow> nat set"
      assumes counterProperty : "\<forall> a x . a = counter x \<longrightarrow> a > x"
          (* define wellform and SSA check *)
          and programProperty : "\<forall> a b . programs a = Some b \<longrightarrow> wellform b"
          and programHasEntry : "\<forall> x y u v w l . (Prog x y ((BasicBlock u v w)#l)) \<in> ran programs
                                           \<longrightarrow> findAllInEdges (((BasicBlock u v w)#l)) u = []"
          (* define all function names should be valid programs *)
          and functionVarsProperty : "\<forall> a x y z . programs a = Some (Prog x y z)
                     \<longrightarrow> (x = a) \<and> allFunVarsInProg (Prog x y z) \<subseteq> dom programs"
         (* define dominace property *)
          and dominanceProperty1 : "\<forall> p S label s Us . p \<in> ran programs \<and>
                  allInstsInProg p = S \<and> (label,s) \<in> S \<and> getUseVars s = Us \<and> \<not> isPhi s
                \<longrightarrow> Us \<subseteq> (getAllPreDefsInProg p)
                      \<or>  Us \<subseteq> (getAllDefsInInsts (the (getInstsBeforeInstProg p label)))
                \<or> usesInAllDefs p Us (set (findAllInEdgesProg p (the (findBlockNameByInstProg p label))))"
          and dominanceProperty2 : "\<forall> p S label s t . p \<in> ran programs \<and>
                  allInstsInProg p = S \<and> (label,Phi s t) \<in> S
               \<longrightarrow> (\<forall> a b . (Local a, b) \<in> set t \<longrightarrow> 
                    a \<in> (getAllPreDefsInProg p) \<or> usesInAllDefs p {a} {b})"
         and usesInAllDefsRule : "\<forall> p Us S . usesInAllDefs p Us S \<longrightarrow>
                 (\<forall> s \<in> S . Us \<subseteq> getAllUsesInInsts (the (findInstsByBlockNameProg p s))
                     \<or> usesInAllDefs p (Us - getAllUsesInInsts (the (findInstsByBlockNameProg p s)))
                                 (set (findAllInEdgesProg p s)))"
         (* defining a reachable node check in antiMap*)
        and isFatherRule1 : "\<forall> anti a b . b \<notin> dom anti \<longrightarrow> \<not> isFather anti a b"
        and isFatherRule2 : "\<forall> anti a b c . anti b = Some c
                                  \<longrightarrow> isFather anti a b = (c = a \<or> isFather anti a c)"
         (* findInSpecReg find a correct value in a register or spec-register for a variable *)
          and findInSpecRegRule1 :
                  "\<forall> specReg antiMap currNum n x . n \<le> currnum
                             \<longrightarrow> findInSpecReg specReg antiMap currNum n x = None"
          and findInSpecRegRule2 :
                  "\<forall> specReg antiMap currNum n x . n > currNum \<and> antiMap n = None \<and> specReg (n,x) = None
                           \<longrightarrow> findInSpecReg specReg antiMap currNum n x = None"
          and findInSpecRegRule3 :
                  "\<forall> specReg antiMap currNum n x n' . n > currNum \<and> antiMap n = Some n' \<and> specReg (n,x) = None
                           \<longrightarrow> findInSpecReg specReg antiMap currNum n x = findInSpecReg specReg antiMap currNum n' x"
          and findInSpecRegRule4 :
                  "\<forall> specReg antiMap currNum n x v . n > currNum \<and> specReg (n,x) = Some v
                           \<longrightarrow> findInSpecReg specReg antiMap currNum n x = Some v"
         (* definie a map construct to write a specReg to a reg*)
         and rewriteMapProperty : "\<forall> a b spec . (a,b) \<in> dom spec \<longrightarrow> spec (a,b) = (rewriteMap spec) b"
         (* define a graph function to get all subcessors of a block num*)
         and getChildrenRule1 : "\<forall> choice a . choice a = None \<longrightarrow> getChildren choice a = {}"
         and getChildrenRule2 : "\<forall> choice a S . choice a = Some S
                        \<longrightarrow> getChildren choice a = (S \<union> {x . \<exists> b \<in> S . x \<in> getChildren choice b})"
         (* a function to get a path from one node to another *)
         and findPathToFatherRule1 : "\<forall> antiMap a b l . a = b \<longrightarrow>
                                                findPathToFather antiMap a b l = Some (l@[a])"
         and findPathToFatherRule2 :
                     "\<forall> antiMap a b c l . a \<noteq> b \<and> (antiMap a = Some c) \<longrightarrow>
                              findPathToFather antiMap a b l = (findPathToFather antiMap c b (l@[a]))"
         and findPathToFatherRule3 :
                     "\<forall> antiMap a b l . a \<noteq> b \<and> (antiMap a = None) \<longrightarrow> findPathToFather antiMap a b l = None"
begin

end