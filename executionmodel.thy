theory executionmodel
imports Main elements
begin

(* assuming variables are in static single assignment format *)
locale execution = elements where
   normalLabel = "normalLabel :: 'label"
    and brLabel = "brLabel :: 'label"
    and returnLabel = "returnLabel :: 'label"
    and readLabel = "readLabel :: 'label"
    and writeLabel = "writeLabel :: 'label"
    and callLabel = "callLabel :: 'label"
    and threadLabel = "threadLabel :: 'label"
    and theZero = "theZero :: 'int"
    and brLabelNames = "brLabelNames :: 'val set"
    and ByteOfVal = "ByteOfVal :: 'byte \<Rightarrow> 'val"
    and TidOfVal = "TidOfVal :: 'tid \<Rightarrow> 'val"
    and CallExp = "CallExp :: 'var \<Rightarrow> 'exp list \<Rightarrow> 'exp"
    and ThreadId = "ThreadId :: 'exp"
    and ThreadCreate = "ThreadCreate :: 'exp \<Rightarrow> 'var \<Rightarrow> 'exp list \<Rightarrow> 'exp"
    and ThreadJoin = "ThreadJoin :: 'exp \<Rightarrow> 'var \<Rightarrow> 'exp"
    and getValOfExp = "getValOfExp :: 'exp \<Rightarrow> 'val option"
    and ReadyIn = "ReadyIn :: 'commitCell \<Rightarrow> 'commitCellType"
    and ReadyOut = "ReadyOut :: 'commitCell \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'int \<Rightarrow> 'byte \<Rightarrow> 'commitCellType"
    and valsToBytes = "valsToBytes :: 'val list \<Rightarrow> 'byte list option"
    and countFrontPathAux = "countFrontPathAux :: ('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list"
    and countFrontPath = "countFrontPath :: ('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'int
                    \<Rightarrow> ('int * 'metaExp) list option"
    and countBackPathAux = "countBackPathAux :: ('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list"
    and countBackPath = "countBackPath :: ('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'int
                    \<Rightarrow> ('int * 'metaExp) list option"
    and countAllBlocks = "countAllBlocks :: ('val * ('int * 'metaExp) list) list \<Rightarrow> 'val list
                            \<Rightarrow> ('int * 'metaExp) list \<Rightarrow> ('int * 'metaExp) list"
    and countMidPathAux = "countMidPathAux :: ('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list"
    and countMidPath = "countMidPath :: ('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'int \<Rightarrow> 'int 
                             \<Rightarrow> ('int * 'metaExp) list option"
    and getSpecBlockPath = "getSpecBlockPath :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int list option"
    and getInstsFromPath = "getInstsFromPath :: ('val * ('int * 'metaExp) list) list \<Rightarrow> 'intMap \<Rightarrow> 'specTree
                             \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list option"
    and hasDefBetweenAux = "hasDefBetweenAux :: ('int * 'metaExp) list \<Rightarrow> 'var \<Rightarrow> bool"
    and hasDefBetween = "hasDefBetween :: ('int * 'metaExp) list \<Rightarrow> 'var \<Rightarrow> bool"
    and isPredecessorList = "isPredecessorList :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int list \<Rightarrow> bool"
    and isPredecessorAll = "isPredecessorAll :: 'specTree \<Rightarrow> 'int list \<Rightarrow> bool"
    and isChild = "isChild :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and getChildren = "getChildren :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int list"
    and getFatherLabel = "getFatherLabel :: ('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'val option"
    and isFather = "isFather :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and isSuccessor = "isSuccessor :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and isPredecessor = "isPredecessor :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool" 
    and updateSpecTree = "updateSpecTree :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'specTree"
    and emptyTree = "emptyTree :: 'specTree"
    and NoAssign = "NoAssign :: 'exp \<Rightarrow> 'metaExp"
    and Assign = "Assign :: 'var \<Rightarrow> 'exp \<Rightarrow> 'metaExp"
    and ValOfExp = "ValOfExp :: 'val \<Rightarrow> 'exp"
    and counter = "counter :: 'int list \<Rightarrow> 'int"
    and sortIntList = "sortIntList :: 'int list \<Rightarrow> 'int list"
    and maxSpecStep = "maxSpecStep :: 'int"
    and getFreeVars = "getFreeVars :: 'exp \<Rightarrow> 'var list"
    and isAvailable = "isAvailable :: 'exp \<Rightarrow> bool"
    and isAvailableMeta = "isAvailableMeta :: 'metaExp \<Rightarrow> bool"
    and updateIntMap = "updateIntMap :: 'intMap \<Rightarrow> 'int \<Rightarrow> 'val \<Rightarrow> 'intMap"
    and lookupIntMap = "lookupIntMap :: 'intMap \<Rightarrow> 'int \<Rightarrow> 'val option"
    and emptyIntMap = "emptyIntMap :: 'intMap"
    and Write = "Write :: 'exp \<Rightarrow> 'type \<Rightarrow> 'exp \<Rightarrow> 'flags \<Rightarrow> 'exp"
    and Read = "Read :: 'exp \<Rightarrow> 'type \<Rightarrow> 'flags \<Rightarrow> 'exp"
    and AWrite = "AWrite :: 'val \<Rightarrow> 'type \<Rightarrow> 'byte list \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and ARead = "ARead :: 'val \<Rightarrow> 'type \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and updateMap = "updateMap :: 'map \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> 'map"
    and lookupMap = "lookupMap :: 'map \<Rightarrow> 'var \<Rightarrow> 'val option"
    and singleMap = "singleMap :: 'var \<Rightarrow> 'val \<Rightarrow> 'map"
    and emptyMap = "emptyMap :: 'map"
  for normalLabel brLabel returnLabel readLabel writeLabel callLabel threadLabel theZero brLabelNames ByteOfVal TidOfVal
        CallExp ThreadId ThreadCreate ThreadJoin getValOfExp ReadyIn ReadyOut
     valsToBytes countFrontPathAux countFrontPath countBackPathAux countBackPath countAllBlocks
    countMidPathAux countMidPath getSpecBlockPath getInstsFromPath
    hasDefBetweenAux hasDefBetween isPredecessorList isPredecessorAll isChild getChildren
    getFatherLabel isFather isSuccessor isPredecessor updateSpecTree emptyTree NoAssign Assign
    ValOfExp counter sortIntList maxSpecStep getFreeVars isAvailable isAvailableMeta updateIntMap
    lookupIntMap emptyIntMap Write Read AWrite ARead updateMap lookupMap singleMap emptyMap +
  fixes getFunName :: "'exp \<Rightarrow> 'var option"
      and getFunArgs :: "'exp \<Rightarrow> 'val option"
    and guessNextBlock :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'int list
                \<Rightarrow> 'intMap \<Rightarrow> ('int * 'val * ('int * 'metaExp) list) option"
   and theModel :: "('var * ('var list * ('val * ('int * 'metaExp) list) list)) list \<Rightarrow>
                          'tid \<Rightarrow> 'tid set \<Rightarrow> ('val * ('int * 'metaExp) list) list \<Rightarrow> 'int list
                              \<Rightarrow> 'intMap \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'metaExp * 'label) set
                  \<Rightarrow> ('int * 'int * 'metaExp * 'label) option  \<Rightarrow> 'map \<Rightarrow> 'specTree
            \<Rightarrow> 'specMap \<Rightarrow> 'stack \<Rightarrow> (('int * 'int * 'var) * 'type * 'intMap) list \<Rightarrow> 'commitCellType \<Rightarrow> bool"
   and threadCount :: "'tid list \<Rightarrow> bool"
   and threadAbort :: "'tid \<Rightarrow> 'tid set \<Rightarrow> bool"
   and theResult :: "'tid \<Rightarrow> 'val \<Rightarrow> bool"
  assumes inputQueueAssumption : "\<forall> fd tid tids prog L cur S cpu reg a b c d x y u v specTree specReg labelMap stack loadSt cml . 
                   theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml
              \<and> (a,b,c,d) \<in> S \<and> (x,y,u,v) \<in> S \<and> a = x \<and> b = y \<longrightarrow> c = u \<and> d = v"
   and getFatherProperty : "\<forall> fd tid tids prog L cur S cpu reg labelMap specTree specReg a a' i i' stack loadSt cml . 
                  theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
                 isFather specTree i' i \<longrightarrow> getFatherLabel prog a = Some a' \<and>
                 lookupIntMap labelMap i' = Some a' \<and> lookupIntMap labelMap i = Some a
                    \<longrightarrow> getFatherLabel prog a = Some a'"
   and specSchemeBase : "\<forall> prog L labelMap a i a' l . guessNextBlock prog L labelMap = Some (i,a,l)
           \<and> lookupIntMap labelMap i = Some a' \<longrightarrow> (a,l) \<in> set prog \<and> getFatherLabel prog a = Some a'"
   and specSchemeRule : "\<forall> fd tid tids prog L labelMap a i l cur S cpu reg specTree specReg stack loadSt cml . 
              theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
             guessNextBlock prog L labelMap = Some (i,a,l) \<longrightarrow> 
             \<not> (\<exists> x . lookupIntMap labelMap x = Some a \<and> isFather specTree i x)"
   and updateSpecVarInTermProperty1 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 x e lab bn2 in2 y v insts .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,Assign x e, lab) \<in> S \<and> isPredecessor specTree bn2 bn1 \<and>
         lookupSpecMap specReg bn2 in2 y = Some v  \<and> y \<in> set (getFreeVars e)
            \<and> lessThanTuple (bn2,in2) (bn1,in1) \<and> \<not> hasDefBetween insts y
         \<and> getInstsFromPath prog labelMap specTree bn2 in2 bn1 in1 = Some insts
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,Assign x e, lab)
                         = (bn1, in1, Assign x (subst e y (ValOfExp v)), lab)"
  and updateSpecVarInTermProperty2 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 x e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,Assign x e, lab) \<in> S \<and> \<not> (\<exists> bn . isPredecessor specTree bn bn1)
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,Assign x e, lab)
                         = (bn1, in1, Assign x e, lab)"
   and updateSpecVarInTermProperty3 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 x e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,Assign x e, lab) \<in> S \<and> lookupSpecMap specReg bn2 in2 y = None 
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,Assign x e, lab)
                         = (bn1, in1, Assign x e, lab)"
   and updateSpecVarInTermProperty4 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 x e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,Assign x e, lab) \<in> S \<and> y \<notin> set (getFreeVars e)
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,Assign x e, lab)
                         = (bn1, in1, Assign x e, lab)"
   and updateSpecVarInTermProperty5 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 x e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,Assign x e, lab) \<in> S \<and> isPredecessor specTree bn2 bn1 \<and>
           y \<in> set (getFreeVars e) \<and> lessThanTuple (bn2,in2) (bn1,in1) \<and> hasDefBetween insts y
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,Assign x e, lab)
                         = (bn1, in1, Assign x e, lab)"
   and updateSpecVarInTermProperty6 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 e lab bn2 in2 y v insts .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,NoAssign e, lab) \<in> S \<and> isPredecessor specTree bn2 bn1 \<and>
         lookupSpecMap specReg bn2 in2 y = Some v  \<and> y \<in> set (getFreeVars e)
            \<and> lessThanTuple (bn2,in2) (bn1,in1) \<and> \<not> hasDefBetween insts y
         \<and> getInstsFromPath prog labelMap specTree bn2 in2 bn1 in1 = Some insts
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,NoAssign e, lab)
                         = (bn1, in1, NoAssign (subst e y (ValOfExp v)), lab)"
  and updateSpecVarInTermProperty7 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,NoAssign e, lab) \<in> S \<and> \<not> (\<exists> bn . isPredecessor specTree bn bn1)
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,NoAssign e, lab)
                         = (bn1, in1, NoAssign e, lab)"
   and updateSpecVarInTermProperty8 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,NoAssign e, lab) \<in> S \<and> lookupSpecMap specReg bn2 in2 y = None 
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,NoAssign e, lab)
                         = (bn1, in1, NoAssign e, lab)"
   and updateSpecVarInTermProperty9 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,NoAssign e, lab) \<in> S \<and> y \<notin> set (getFreeVars e)
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,NoAssign e, lab)
                         = (bn1, in1, NoAssign e, lab)"
   and updateSpecVarInTermProperty10 : "\<forall> fd tid tids prog L labelMap cur cpu S reg specTree specReg stack loadSt cml
                        bn1 in1 e lab bn2 in2 y .
               theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml \<and>
               (bn1,in1,NoAssign e, lab) \<in> S \<and> isPredecessor specTree bn2 bn1 \<and>
           y \<in> set (getFreeVars e) \<and> lessThanTuple (bn2,in2) (bn1,in1) \<and> hasDefBetween insts y
                 \<longrightarrow> updateSpecVarInTerm specReg bn2 in2 y (bn1,in1,NoAssign e, lab)
                         = (bn1, in1, NoAssign e, lab)"
   and updateVars : "\<forall> fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml .
                   theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml
             \<longrightarrow> theModel fd tid tids prog L labelMap cur  {t . \<exists> t' \<in> S .
                  t = updateAllVarsInMeta reg (updateSpecVarsInTerm specReg t') } cpu reg specTree specReg stack loadSt cml"
   and putInPoll1 : "\<forall> fd tid tids prog L labelMap cur S cpu reg specTree specReg a l n i stack loadSt cml .
                      guessNextBlock prog L labelMap = Some (i, a,l) \<and> counter L = n 
            \<and> getFatherLabel prog a = None
         \<longrightarrow> theModel fd tid tids prog (n#L) (updateIntMap labelMap n a) cur
                           (S \<union> set (turnInstList l n)) cpu reg specTree specReg stack loadSt cml"
   and putInPoll2 : "\<forall> fd tid tids prog L labelMap cur S cpu reg specTree specReg a l n a' i stack loadSt cml .
                      guessNextBlock prog L labelMap = Some (i, a,l) \<and> counter L = n 
            \<and> getFatherLabel prog a = Some a' \<and> lookupIntmap labelMap i = Some a'
         \<longrightarrow> theModel fd tid tids prog (n#L) (updateIntMap labelMap n a) cur (S \<union> set (turnInstList l n))
                    cpu reg (updateSpecTree specTree i n) specReg stack loadSt cml"
   and cpuInNormal : "\<forall> fd (a::'int) (b::'int) c d tid tids prog L labelMap cur S reg specTree specReg stack v loadSt cml .
              isAvailableMeta c \<and> (a,b,c,d) \<in> S \<and> (d = normalBLabel \<or> d = readLabel \<or>
                       d = writeLabel) \<and> theModel fd tid tids prog L labelMap cur S None reg specTree specReg stack loadSt cml \<and>
                       lessThan a (thePlus cur maxSpecStep) \<and> lookupIntMap labelMap a = Some v \<longrightarrow>
              theModel fd tid tids prog L labelMap cur (S - {(a,b,c,d)}) (Some (a,b,c,d)) reg specTree specReg stack loadSt cml"
   and cpuInReturn : "\<forall> fd (a::'int) (b::'int) c d tid tids prog L labelMap cur S reg specTree specReg stack loadSt cml .
         isAvailableMeta c \<and> (a,b,c,d) \<in> S \<and> (d = returnLabel \<or> d = callLabel \<or> d = threadLabel) \<and>
               theModel fd tid tids prog L labelMap cur S None reg specTree specReg stack loadSt cml \<and>
              (\<forall> x y u v . (x,y,u,v) \<in> S \<and> a \<noteq> x \<and> b \<noteq> y \<longrightarrow> lessThanTuple (a,b) (x,y))
          \<longrightarrow> theModel fd tid tids prog L labelMap cur (S - {(a,b,c,d)})
                                 (Some (a,b,c,d)) reg specTree specReg stack loadSt cml"
   and putInBr : "\<forall> fd (a::'int) (b::'int) c tid tids prog L labelMap cur S reg specTree specReg stack loadSt cml .
          isAvailableMeta c \<and> (a,b,c,brLabel) \<in> S \<and>
                 theModel fd tid tids prog L labelMap cur S None reg specTree specReg stack loadSt cml \<and>
               lessThan a (thePlus cur maxSpecStep) \<and> isChild specTree a cur \<and>
                           \<not> (\<exists> y u v. (a,y,u,v) \<in> S \<and> lessThan b y)
           \<longrightarrow> theModel fd tid tids prog L labelMap cur (S - {(a,b,c,brLabel)})
                                 (Some (a,b,c,brLabel)) reg specTree specReg stack loadSt cml"
   and normalEval : "\<forall> fd tid tids prog L labelMap cur S a b x e reg specTree specReg stack val loadSt cml .
                   theModel fd tid tids prog L labelMap cur S (Some (a,b,Assign x e,normalLabel)) reg specTree specReg stack loadSt cml
                   \<and> e \<noteq> ThreadId \<and> evalFun e = val \<longrightarrow>
             theModel fd tid tids prog L labelMap cur S None reg specTree (updateSpecMap specReg a b x val) stack loadSt cml"
   and threadIdEval : "\<forall> fd tid tid' tids tl prog L labelMap cur S a b x reg specTree specReg stack loadSt cml .
       theModel fd tid tids prog L labelMap cur S (Some (a,b,Assign x ThreadId,normalLabel)) reg specTree specReg stack loadSt cml
         \<and> threadCount tl \<and> tidCounter tl = tid'
          \<longrightarrow> threadCount (tid'#tl) \<and> 
                  theModel fd tid tids prog L labelMap cur S None reg specTree
                                 (updateSpecMap specReg a b x (TidOfVal tid')) stack loadSt cml"
   and threadCreateEval : "\<forall> fd tid tid' tids prog L labelMap cur S a b x e el
              reg specTree specReg stack loadSt cml vl args prog' m' .
       theModel fd tid tids prog L labelMap cur S (Some (a,b,NoAssign (ThreadCreate e x el),threadLabel))
         reg specTree specReg stack loadSt cml \<and> isAvailable (ThreadCreate e x el)
        \<and> getValOfExpList el = Some vl \<and> e = ValOfExp (TidOfVal tid')
              \<and> getValueInList fd x = Some (args, prog')  \<and> updateMapAll emptyMap args vl = Some m'
     \<longrightarrow> theModel fd tid (insert tid' tids) prog L labelMap cur S None reg specTree specReg stack loadSt cml
         \<and> theModel fd tid' {} prog' [theZero] emptyIntMap theZero
                     {} None m' emptyTree emptySpecMap emptyStack [] (ReadyIn emptyCommitCell)"
   and threadJoinEval : "\<forall> fd tid tid' tids prog L labelMap cur S a b x e reg specTree specReg stack loadSt cml val .
           theModel fd tid tids prog L labelMap cur S (Some (a,b,NoAssign (ThreadJoin e x),threadLabel))
                    reg specTree specReg stack loadSt cml \<and> isAvailable (ThreadJoin e x)
         \<and> theResult tid' val \<and> e = ValOfExp (TidOfVal tid')
       \<longrightarrow> theModel fd tid (tids-{tid'}) prog L labelMap cur S None (updateMap reg x val) specTree specReg stack loadSt cml"
   and brEval1 : "\<forall> fd tid tids prog L labelMap cur cur' S b e reg specTree specReg val nexts stack loadSt cml .
                 theModel fd tid tids prog L labelMap cur S (Some (cur,b,NoAssign e,brLabel)) reg specTree specReg stack loadSt cml
        \<and> evalFun e = val \<and> val \<in> set (getFirstInList prog) \<and> getChildren specTree cur = nexts
            \<and> lookupIntMapForOne nexts labelMap val = Some cur'  \<longrightarrow>
               theModel fd tid tids prog L labelMap cur' S None
               (addElementsToMap reg (selectNotesInSpecMap specReg [cur])) specTree 
                 (turnListToSpecMap (selectNotesInSpecMap specReg (cur#(getAllSubsExpectOneChild specTree cur cur')))) stack loadSt cml"
   and brEval2 : "\<forall> fd tid tids prog L labelMap cur S b e reg specTree specReg val nexts l n stack loadSt cml.
                 theModel fd tid tids prog L labelMap cur S (Some (cur,b,NoAssign e,brLabel)) reg specTree specReg stack loadSt cml
        \<and> evalFun e = val \<and> val \<in> set (getFirstInList prog) \<and> getChildren specTree cur = nexts
            \<and> lookupIntMapForOne nexts labelMap val = None \<and> getValueInList prog val = Some l
           \<and> counter L = n \<longrightarrow>
               theModel fd tid tids prog (n#L) (updateIntMap labelMap n val) n (S \<union> set (turnInstList l n))
                    None (addElementsToMap reg (selectNotesInSpecMap specReg [cur]))
              (updateSpecTree specTree cur n)
               (turnListToSpecMap (selectNotesInSpecMap specReg (cur#(getAllSubsExpectOneChild specTree cur cur')))) stack loadSt cml"
   and writeEval : "\<forall> fd tid tids prog L labelMap cur S a b e1 ty e2 reg specTree specReg val1 val2 cml bytes fs stack loadSt .
                 theModel fd tid tids prog L labelMap cur S (Some (a,b,NoAssign (Write e1 ty e2 fs), writeLabel))
                        reg specTree specReg stack loadSt (ReadyIn cml)
        \<and> evalFun e1 = val1 \<and> evalFun e2 = val2 \<and> splitBytes ty val2 = Some bytes \<longrightarrow>
               theModel fd tid tids prog L labelMap cur S None reg specTree specReg stack loadSt
                            (ReadyIn (insertToMemCell cml specTree tid a b (AWrite val1 ty bytes fs)))"
   and readEval : "\<forall> fd tid tids prog L labelMap cur S a b x e1 ty reg specTree specReg val1 cml fs stack loadSt .
                 theModel fd tid tids prog L labelMap cur S (Some (a,b,Assign x (Read e1 ty fs), readLabel))
                    reg specTree specReg stack loadSt (ReadyIn cml)
        \<and> evalFun e1 = val1 \<longrightarrow>
               theModel fd tid tids prog L labelMap cur S None reg specTree specReg stack (createLoadEntry loadSt a b x ty)
                    (ReadyIn (insertToMemCell cml specTree tid a b (ARead val1 ty fs)))"
   and loadOneByte : "\<forall> fd tid tids prog L labelMap cur S reg specTree specReg cml stack loadSt loadSt' cpu x y z i v .
                     theModel fd tid tids prog L labelMap cur S cpu reg specTree
                       specReg stack loadSt (ReadyOut cml x y z i v) \<and> \<not> isLoadFull loadSt' x y z
                   \<and> updateLoadMap loadSt x y z i v = Some loadSt'
                   \<longrightarrow> theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt' (ReadyIn cml)"
   and loadOneFull1 : "\<forall> fd tid tids prog L labelMap cur S reg specTree specReg cml stack loadSt loadSt' cpu x y z i v fv .
                     theModel fd tid tids prog L labelMap cur S cpu reg specTree
                       specReg stack loadSt (ReadyOut cml x y z i v) \<and> isLoadFull loadSt' x y z
                   \<and> updateLoadMap loadSt x y z i v = Some loadSt' \<and> isPredecessor specTree x cur
                  \<and> getValueFromLoadMap loadSt' x y z = Some fv
                   \<longrightarrow> theModel fd tid tids prog L labelMap cur S cpu (updateMap reg z fv)
                            specTree specReg stack (removeEntry loadSt' x y z) (ReadyIn cml)"
   and loadOneFull2 : "\<forall> fd tid tids prog L labelMap cur S reg specTree specReg cml stack loadSt loadSt' cpu x y z i v fv .
                     theModel fd tid tids prog L labelMap cur S cpu reg specTree
                       specReg stack loadSt (ReadyOut cml x y z i v) \<and> isLoadFull loadSt' x y z
                   \<and> updateLoadMap loadSt x y z i v = Some loadSt' \<and> (x = cur \<or> isSuccessor specTree x cur)
                  \<and> getValueFromLoadMap loadSt' x y z = Some fv
                   \<longrightarrow> theModel fd tid tids prog L labelMap cur S cpu reg specTree
                            (updateSpecMap specReg x y z fv) stack (removeEntry loadSt' x y z) (ReadyIn cml)"
   and callEval1 : "\<forall> fd tid tids prog prog' L labelMap cur S reg specTree specReg stack loadSt cml b x fn e vl args m' .
                      theModel fd tid tids prog L labelMap cur S (Some (cur,b,Assign x (CallExp fn e),callLabel))
                             reg specTree specReg stack loadSt cml \<and> isAvailable (CallExp fn e)
                     \<and> getValOfExpList e = Some vl \<and> getValueInList fd fn = Some (args, prog')
                      \<and> updateMapAll emptyMap args vl = Some m'
                    \<longrightarrow> theModel fd tid tids prog' [theZero] emptyIntMap theZero
                                 {} None m' emptyTree emptySpecMap
             (popIn stack (prog,L,labelMap,cur,S,Some x,reg,specTree,specReg,loadSt,cml)) [] (ReadyIn emptyCommitCell)"
   and callEval2 : "\<forall> fd tid tids prog prog' L labelMap cur S reg specTree specReg stack loadSt cml b fn e vl args m' .
                      theModel fd tid tids prog L labelMap cur S (Some (cur,b,NoAssign (CallExp fn e),callLabel))
                             reg specTree specReg stack loadSt cml \<and> isAvailable (CallExp fn e)
                     \<and> getValOfExpList e = Some vl \<and> getValueInList fd fn = Some (args, prog')
                      \<and> updateMapAll emptyMap args vl = Some m'
                    \<longrightarrow> theModel fd tid tids prog' [theZero] emptyIntMap theZero
                                 {} None m' emptyTree emptySpecMap
             (popIn stack (prog,L,labelMap,cur,S,None,reg,specTree,specReg,loadSt,cml)) [] (ReadyIn emptyCommitCell)"
   and returnEval1 : "\<forall> fd tid prog L labelMap cur S reg specTree specReg stack cml a b e val .
                      theModel fd tid {} prog L labelMap cur S (Some (a,b,NoAssign e,returnLabel))
          reg specTree specReg stack [] cml \<and> evalFun e = val \<and> popOut stack = (None, emptyStack)
                    \<longrightarrow> theResult tid val"
   and returnEval2 : "\<forall> fd tid tid' tids prog L labelMap cur S reg specTree specReg stack cml a b e
             tids' prog' L' labelMap' cur' S' cpu' reg' specTree' specReg' stack' loadSt' cml'.
                      theModel fd tid tids prog L labelMap cur S (Some (a,b,NoAssign e,returnLabel))
          reg specTree specReg stack [] cml \<and> popOut stack = (None, emptyStack) \<and> tid' \<in> tids
      \<and> theModel fd tid' tids' prog' L' labelMap' cur' S' cpu' reg' specTree' specReg' stack' loadSt' cml'
           \<longrightarrow> theModel fd tid (tids - {tid'}) prog L labelMap cur S (Some (a,b,NoAssign e,returnLabel))
                             reg specTree specReg stack [] cml \<and> threadAbort tid' tids'"
   and abortEval : "\<forall> tid tids fd tid' tids' prog L labelMap cur S cpu reg specTree specReg stack loadSt cml .
             threadAbort tid' tids' \<and> tid \<in> tids'
            \<and> theModel fd tid tids prog L labelMap cur S cpu reg specTree specReg stack loadSt cml
                    \<longrightarrow> threadAbort tid' (tids' - {tid}) \<and> threadAbort tid tids"
   and returnEval3 : "\<forall> fd tid tids prog L labelMap cur S reg specTree specReg stack stack' cml a b e val
                         prog' L' labelMap' cur' S' x reg' specTree' specReg' loadSt' cml' .
                      theModel fd tid tids prog L labelMap cur S (Some (a,b,NoAssign e,returnLabel))
          reg specTree specReg stack [] cml \<and> evalFun e = val
             \<and> popOut stack = (Some (prog',L',labelMap',cur',S',Some x,reg',specTree',specReg',loadSt',cml'), stack')
           \<longrightarrow> theModel fd tid tids prog' L' labelMap' cur' S' None (updateMap reg' x val) specTree' specReg' stack' loadSt' cml'"
   and returnEval4 : "\<forall> fd tid tids prog L labelMap cur S reg specTree specReg stack stack' cml a b e val
                         prog' L' labelMap' cur' S' reg' specTree' specReg' loadSt' cml' .
                      theModel fd tid tids prog L labelMap cur S (Some (a,b,NoAssign e,returnLabel))
          reg specTree specReg stack [] cml \<and> evalFun e = val
             \<and> popOut stack = (Some (prog',L',labelMap',cur',S',None,reg',specTree',specReg',loadSt',cml'), stack')
           \<longrightarrow> theModel fd tid tids prog' L' labelMap' cur' S' None reg' specTree' specReg' stack' loadSt' cml'"

end
