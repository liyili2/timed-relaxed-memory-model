theory elements
imports Main
begin

fun getFirstInList where
"getFirstInList [] = []"
| "getFirstInList ((a,b)#l) = a#(getFirstInList l)"

fun getValueInList where
"getValueInList [] a = None"
| "getValueInList ((a,b)#l) a' = (if a = a' then Some b else getValueInList l a')"

fun getFirstValueInList where
"getFirstValueInList [] al = []"
| "getFirstValueInList ((a,[])#l) al =  getFirstValueInList l al"
| "getFirstValueInList ((a,b#bl)#l) al = (if a \<in> set al then (b#getFirstValueInList l al)
          else getFirstValueInList l al)"

fun getInstInList where
"getInstInList [] a = None"
| "getInstInList ((a,b)#l) a' = (case getValueInList b a' of None \<Rightarrow> getInstInList l a' | Some x \<Rightarrow> Some x)"

fun selectEntries where
"selectEntries [] al = []"
| "selectEntries (((x,y,z),b)#l) al = (if x \<in> set al
                      then ((x,y,z),b)#(selectEntries l al) else selectEntries l al)"

fun adjTwo where
"adjTwo n [] = None"
| "adjTwo n [x] = None"
| "adjTwo n (x#(y#l)) = (if n = 0 then Some (x,y) else adjTwo n (y#l))"

fun removeEntry where
"removeEntry [] x y z = []"
| "removeEntry (((x,y,z),t,m)#l) a b c =
                  (if a = x \<and> b = y \<and> c = z then l else ((x,y,z),t,m)#(removeEntry l a b c))"

(*
    and restrictMap :: "'map \<Rightarrow> 'var list \<Rightarrow> 'map"

  and specMapProperty1 : "\<forall> v e m bn bn' . getCurSpecVarBlock m v = Some bn' \<and> (bn = bn' \<or> lessThan bn' bn)
                    \<longrightarrow> lookupSpecMap (updateSpecMap m bn v e) bn v = Some e"
  and specMapProperty2 : "\<forall> v e m bn . getCurSpecVarBlock m v = None
                    \<longrightarrow> lookupSpecMap (updateSpecMap m bn v e) bn v = Some e"
  and specMapProperty3 : "\<forall> v e m bn bn' . getCurSpecVarBlock m v = Some bn' \<and> lessThan bn bn'
                    \<longrightarrow> (updateSpecMap m bn v e) = m"
   and transformMapRule : "\<forall> m m' a v i . transformMap m = m' \<and> lookup m' a = Some v
                    \<and> lookupSpecMap m i a = Some v
                  \<longrightarrow> (\<forall> i' v' . lookupSpec m i' a = Some v'
                         \<longrightarrow> (i = i' \<and> v = v') \<or> (lessThan i' i))"
   and restrictMapRule : "\<forall> m m' l . restrictMap m l = m' \<longrightarrow>
                           (\<forall> x . x \<in> set l \<and> x \<in> set (keys m) \<longleftrightarrow> (\<exists> v . lookupMap m x = Some v))"
*)

locale elements =
   fixes normalLabel :: "'label"
    and brLabel :: "'label"
    and returnLabel :: "'label"
    and readLabel :: "'label"
    and writeLabel :: "'label"
    and callLabel :: "'label"
    and threadLabel :: "'label"
    and theZero :: "'int"
    and brLabelNames :: "'val set"
    and ByteOfVal :: "'byte \<Rightarrow> 'val"
    and TidOfVal :: "'tid \<Rightarrow> 'val"
    and CallExp :: "'var \<Rightarrow> 'exp list \<Rightarrow> 'exp"
    and ThreadId :: "'exp"
    and ThreadCreate :: "'exp \<Rightarrow> 'var \<Rightarrow> 'exp list \<Rightarrow> 'exp"
    and ThreadJoin :: "'exp \<Rightarrow> 'var \<Rightarrow> 'exp"
    and getValOfExp :: "'exp \<Rightarrow> 'val option"
    and ReadyIn :: "'commitCell \<Rightarrow> 'commitCellType"
    and ReadyOut :: "'commitCell \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'int \<Rightarrow> 'byte \<Rightarrow> 'commitCellType"
    and valsToBytes :: "'val list \<Rightarrow> 'byte list option"
    and countFrontPathAux :: "('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list"
    and countFrontPath :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'int
                    \<Rightarrow> ('int * 'metaExp) list option"
    and countBackPathAux :: "('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list"
    and countBackPath :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'int
                    \<Rightarrow> ('int * 'metaExp) list option"
    and countAllBlocks :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'val list
                            \<Rightarrow> ('int * 'metaExp) list \<Rightarrow> ('int * 'metaExp) list"
    and countMidPathAux :: "('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list"
    and countMidPath :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'int \<Rightarrow> 'int 
                             \<Rightarrow> ('int * 'metaExp) list option"
    and getSpecBlockPath :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int list option"
    and getInstsFromPath :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'intMap \<Rightarrow> 'specTree
                             \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> ('int * 'metaExp) list option"
    and hasDefBetweenAux :: "('int * 'metaExp) list \<Rightarrow> 'var \<Rightarrow> bool"
    and hasDefBetween :: "('int * 'metaExp) list \<Rightarrow> 'var \<Rightarrow> bool"
    and isPredecessorList :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int list \<Rightarrow> bool"
    and isPredecessorAll :: "'specTree \<Rightarrow> 'int list \<Rightarrow> bool"
    and isChild :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and getChildren :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int list"
    and getFatherLabel :: "('val * ('int * 'metaExp) list) list \<Rightarrow> 'val \<Rightarrow> 'val option"
    and isFather :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and isSuccessor :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and isPredecessor :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool" 
    and updateSpecTree :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'specTree"
    and emptyTree :: "'specTree"
    and NoAssign :: "'exp \<Rightarrow> 'metaExp"
    and Assign :: "'var \<Rightarrow> 'exp \<Rightarrow> 'metaExp"
    and ValOfExp :: "'val \<Rightarrow> 'exp"
    and counter :: "'int list \<Rightarrow> 'int"
    and tidCounter :: "'tid list \<Rightarrow> 'tid"
    and sortIntList :: "'int list \<Rightarrow> 'int list"
    and maxSpecStep :: "'int"
    and getFreeVars :: "'exp \<Rightarrow> 'var list"
    and isAvailable :: "'exp \<Rightarrow> bool"
    and isAvailableMeta :: "'metaExp \<Rightarrow> bool"
    and updateIntMap :: "'intMap \<Rightarrow> 'int \<Rightarrow> 'val \<Rightarrow> 'intMap"
    and lookupIntMap :: "'intMap \<Rightarrow> 'int \<Rightarrow> 'val option"
    and emptyIntMap :: "'intMap"
    and Write :: "'exp \<Rightarrow> 'type \<Rightarrow> 'exp \<Rightarrow> 'flags \<Rightarrow> 'exp"
    and Read :: "'exp \<Rightarrow> 'type \<Rightarrow> 'flags \<Rightarrow> 'exp"
    and AWrite :: "'val \<Rightarrow> 'type \<Rightarrow> 'byte list \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and ARead :: "'val \<Rightarrow> 'type \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and updateMap :: "'map \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> 'map"
    and lookupMap :: "'map \<Rightarrow> 'var \<Rightarrow> 'val option"
    and singleMap :: "'var \<Rightarrow> 'val \<Rightarrow> 'map"
    and emptyMap :: "'map"
    and popIn :: "'stack \<Rightarrow> 'a \<Rightarrow> 'stack"
    and popOut :: "'stack \<Rightarrow> ('a option * 'stack)"
    and emptyStack :: "'stack"
    and intListSize :: "'int list \<Rightarrow> 'int"
    and lookupIntMapAll :: "'intMap \<Rightarrow> 'int list \<Rightarrow> 'val list option"
    and lookupIntMapForOne :: "'int list \<Rightarrow> 'intMap \<Rightarrow> 'val \<Rightarrow> 'int option"
    and updateVarListInTerm :: "'map \<Rightarrow> 'var list \<Rightarrow> 'exp \<Rightarrow> 'exp"
    and updateAllVarsInTerm :: "'map \<Rightarrow> 'exp \<Rightarrow> 'exp"
    and updateAllVarsInMeta :: "'map \<Rightarrow> ('int * 'int * 'metaExp * 'label) \<Rightarrow> ('int * 'int * 'metaExp * 'label)"
    and updateSpecVarInTerm :: "'specMap \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var
                 \<Rightarrow> ('int * 'int * 'metaExp * 'label) \<Rightarrow> ('int * 'int * 'metaExp * 'label)"
    and updateSpecVarsInTermAux :: "'specMap \<Rightarrow> ('int * 'int * 'var) list \<Rightarrow> ('int * 'int * 'metaExp * 'label)
                                   \<Rightarrow> ('int * 'int * 'metaExp * 'label)"
    and updateSpecVarsInTerm :: "'specMap \<Rightarrow> ('int * 'int * 'metaExp * 'label)
                         \<Rightarrow> ('int * 'int * 'metaExp * 'label)"
    and subst :: "'exp \<Rightarrow> 'var \<Rightarrow> 'exp \<Rightarrow> 'exp"
    and substMetaExp :: "'metaExp \<Rightarrow> 'var \<Rightarrow> 'exp \<Rightarrow> 'metaExp"
    and keys :: "'map \<Rightarrow> 'var list"
    and theValues :: "'map \<Rightarrow> 'val list"
    and intKeys :: "'intMap \<Rightarrow> 'int list"
    and intValues :: "'intMap \<Rightarrow> 'val list"
    and specKeys :: "'specMap \<Rightarrow> ('int * 'int * 'var) list"
    and updateSpecMap :: "'specMap \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> 'specMap"
    and lookupSpecMap :: "'specMap \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'val option"
    and emptySpecMap :: "'specMap"
    and getCurSpecVarBlock :: "'specMap \<Rightarrow> 'var \<Rightarrow> 'int option"
    and evalFun :: "'exp \<Rightarrow> 'val"
    and thePlus :: "'int \<Rightarrow> 'int \<Rightarrow> 'int" 
    and lessThan :: "'int \<Rightarrow> 'int \<Rightarrow> bool"
    and lessThanTuple :: "('int * 'int) \<Rightarrow> ('int * 'int) \<Rightarrow> bool"
    and turnInst :: "('int * 'metaExp) \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'metaExp * 'label)"
    and turnInstList :: "('int * 'metaExp) list \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'metaExp * 'label) list"
    and turnSpecMapToList :: "'specMap \<Rightarrow> (('int * 'int * 'var) * 'val) list"
    and turnListToSpecMap :: "(('int * 'int * 'var) * 'val) list \<Rightarrow> 'specMap"
    and getSubNotes :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int list"
    and getAllSubNotes :: "'specTree \<Rightarrow> 'int list \<Rightarrow> 'int list"
    and subList :: "'int list \<Rightarrow> 'int list \<Rightarrow> 'int list"
    and getAllSubsExpectOneChild :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int list"
    and selectNotesInSpecMap :: "'specMap \<Rightarrow> 'int list \<Rightarrow> (('int * 'int * 'var) * 'val) list"
    and addElementsToMap :: "'map \<Rightarrow> (('int * 'int * 'var) * 'val) list \<Rightarrow> 'map"
    and splitBytes :: "'type \<Rightarrow> 'val \<Rightarrow> 'byte list option"
    and joinBytes :: "'type \<Rightarrow> 'byte list \<Rightarrow> 'val option"
    and sizeof :: "'type \<Rightarrow> nat"
    and emptyCommitCell :: "'commitCell"
    and insertToMemCell :: "'commitCell \<Rightarrow> 'specTree \<Rightarrow> 'tid \<Rightarrow> 'int \<Rightarrow> 'int
                                     \<Rightarrow> 'memExp \<Rightarrow> 'commitCell"
    and createLoadEntry :: "(('int * 'int * 'var) * 'type * 'intMap) list
                      \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'type \<Rightarrow> (('int * 'int * 'var) * 'type * 'intMap) list"
    and updateLoadMap :: "(('int * 'int * 'var) * 'type * 'intMap) list
                   \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'int \<Rightarrow> 'byte
                            \<Rightarrow> (('int * 'int * 'var) * 'type * 'intMap) list option"
    and isLoadFull :: "(('int * 'int * 'var) * 'type * 'intMap) list \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> bool"
    and getValueFromLoadMap :: "(('int * 'int * 'var) * 'type * 'intMap) list
                         \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'var \<Rightarrow> 'val option"
assumes counterProperty : "\<forall> a S x . x = counter S \<and> a \<in> set S \<longrightarrow> lessThan a x"
  and isAvailableProperty : "\<forall> e . isAvailable e = (getFreeVars e = [])"
  and mapProperty1 : "\<forall> v e m . lookupMap (updateMap m v e) v = Some e"
  and mapProperty2 : "\<forall> v m . \<not> (\<exists> e' e . lookupMap m v = Some e
                                                 \<and> lookupMap m v = Some e' \<and> e \<noteq> e')"
  and intMapProperty1 : "\<forall> v e m . lookupIntMap (updateIntMap m v e) v = Some e"
  and intMapProperty2 : "\<forall> v m . \<not> (\<exists> e' e . lookupIntMap m v = Some e
                                                 \<and> lookupIntMap m v = Some e' \<and> e \<noteq> e')"
  and specKeysRule : "\<forall> x map v bn1 in1 . lookupSpecMap map bn1 in1 x = Some v
                                                  \<longleftrightarrow> (bn1,in1,x) \<in> set (specKeys map)"
  and specMapProperty1 : "\<forall> v e m bn1 in1 .
                                 lookupSpecMap (updateSpecMap m bn1 in1 v e) bn1 in1 v = Some e"
  and specMapProperty2 : "\<forall> v m bn1 in1 . \<not> (\<exists> e' e . lookupSpecMap m bn1 in1 v = Some e
                              \<and> lookupSpecMap m bn1 in1 v = Some e' \<and> e \<noteq> e')"
  and specTreeProperty1 : "\<forall> ST x y . isChild ST x y \<longrightarrow> isSuccessor ST x y \<and> \<not> isPredecessor ST x y"
  and specTreeProperty2 : "\<forall> ST x y . isChild ST x y \<longrightarrow> isFather ST y x \<and> \<not> isChild ST y x"
and specTreeProperty3 : "\<forall> ST x y . isFather ST x y \<longrightarrow> isChild ST y x \<and> \<not> isFather ST y x"
and specTreeProperty4 : "\<forall> ST x y . isFather ST x y \<longrightarrow> isPredecessor ST y x \<and> \<not> isSuccessor ST y x"
  and specTreeProperty5 : "\<forall> ST x y . isSuccessor ST x y \<longrightarrow> isPredecessor ST y x \<and> \<not> isSuccessor ST y x"
  and specTreeProperty6 : "\<forall> ST x y . isPredecessor ST x y \<longrightarrow> isSuccessor ST y x \<and> \<not> isPredecessor ST y x"
  and specTreeUniqueFather1 : "\<forall> ST x y y' . isChild ST x y \<and> isChild ST x y' \<longrightarrow> y = y'"
  and specTreeUniqueFather2 : "\<forall> ST x y x' . isFather ST x y \<and> isFather ST x' y \<longrightarrow> x = x'"
  and specTreeOlderBigger1 : "\<forall> ST x y . isFather ST x y \<longrightarrow>  lessThan x y"
  and specTreeOlderBigger2 : "\<forall> ST x y . isChild ST x y \<longrightarrow>  lessThan y x"
  and isPredecessorListRule : "\<forall> ST x yl . isPredecessorList ST x yl =
                                                   (\<forall> y . y \<in> set yl \<longrightarrow> isPredecessor ST x y)"
  and isPredecenssorAllRule1 : "\<forall> G . isPredecessorAll G []"
  and isPredecenssorAllRule2 : "\<forall> G x l . isPredecenssorAll G (x#l)
                      = (isPredecessorList G x l \<and> isPredecenssorAll G l)"
  and lessThanTupleProperty : "\<forall> a b c d . lessThanTuple (a,b) (c,d)
                                        = (lessThan a c \<or> (a = c \<and> lessThan b d))"
   and isAvailableInCall : "\<forall> x el . isAvailable (CallExp x el) \<longleftrightarrow> (\<forall> e \<in> set el . (\<exists> v. e = ValOfExp v))"
   and isAvailableMetaRule1 : "\<forall> x e . isAvailableMeta (Assign x e) = isAvailable e"
   and isAvailableMetaRule2 : "\<forall> e . isAvailableMeta (NoAssign e) = isAvailable e"
   and turnInstRule : "\<forall> x e a . turnInst (x,e) a = (a,x,e,normalLabel)
                  \<or> turnInst (x,e) a = (a,x,e,readLabel) \<or> turnInst (x,e) a = (a,x,e,writeLabel)
                 \<or> turnInst (x,e) a = (a,x,e,returnLabel) \<or> turnInst (x,e) a = (a,x,e,brLabel)"
   and turnInstListRule1 : "\<forall> a . turnInstList [] a = []"
   and turnInstListRule2 : "\<forall> a x l . turnInstList (x#l) a = (turnInst x a)#(turnInstList l a)"
   and updateSpecTreeRule : "\<forall> specTree a b . isFather (updateSpecTree specTree b a) b a"
   and keysRule : "\<forall> x map v . lookupMap map x = Some v \<longleftrightarrow> x \<in> set (keys map)"
   and valuesRule : "\<forall> x map v . lookupMap map x = Some v \<longleftrightarrow> v \<in> set (theValues map)"
   and intKeysRule : "\<forall> x map v . lookupIntMap map x = Some v \<longleftrightarrow> x \<in> set (intKeys map)"
   and intValuesRule : "\<forall> x map v . lookupIntMap map x = Some v \<longleftrightarrow> v \<in> set (intValues map)"
  and singleMapProperty : "\<forall> x y . keys (singleMap x y) = [x] \<and> theValues (singleMap x y) = [y] 
                                  \<and> lookupMap (singleMap x y) x = Some y
                                   \<and> (\<forall> x' . x \<noteq> x' \<longrightarrow> lookupMap (singleMap x y) x' = None)"
  and emptyIntMapProperty : "\<forall> x . intKeys emptyIntMap = [] \<and> intValues emptyIntMap = [] 
                                  \<and> lookupIntMap emptyIntMap x = None"
  and emptyMapProperty : "\<forall> x . keys emptyMap = [] \<and> theValues emptyMap = [] 
                                  \<and> lookupMap emptyMap x = None"
  and emptySpecMapProperty : "\<forall> x y z . specKeys emptySpecMap = []  \<and> lookupSpecMap emptySpecMap x y z = None"
   and getChildrenRule : "\<forall> m i l . getChildren m i = l \<longrightarrow> (\<forall> x \<in> set l . isChild m x i)"
   and lookupIntMapAllRule1 : "\<forall> m . lookupIntMapAll m [] = Some []"
   and lookupIntMapAllRule2 : "\<forall> m a l x xl . (lookupIntMap m a  = None \<longrightarrow> lookupIntMapAll m (a#l) = None)
                     \<and> (lookupIntMapAll m l = None \<longrightarrow> lookupIntMapAll m (a#l) = None)
            \<and> (lookupIntMapAll m l = Some xl \<and> lookupIntMap m a = Some x
                                  \<longrightarrow> lookupIntMapAll m (a#l) = Some (x#xl))"
  and lookupIntMapForOneRule1 : "\<forall> m x . lookupIntMapForOne [] m x = None"
  and lookupIntMapForOneRule2 : "\<forall> m x i l . lookupIntMap m i = Some x \<longrightarrow>
                                                 lookupIntMapForOne (i#l) m x = Some i"
  and lookupIntMapForOneRule3 : "\<forall> m x i l . lookupIntMap m i = None
                                     \<longrightarrow> lookupIntMapForOne (i#l) m x = lookupIntMapForOne l m x"
  and lookupIntMapForOneRule4 : "\<forall> m x x' i l . lookupIntMap m i = Some x' \<and>  x \<noteq> x'
                                     \<longrightarrow> lookupIntMapForOne (i#l) m x = lookupIntMapForOne l m x"
  and getSpecBlockPathRule1 : "\<forall> G x y . \<not> isPredecessor G x y \<and> x \<noteq> y \<longleftrightarrow> getSpecBlockPath G x y = None"
  and getSpecBlockPathRule2 : "\<forall> G x . getSpecBlockPath G x x = Some [x]"
  and getSpecBlockPathRule3 : "\<forall> G x y yl . isPredecessor G x y
                 \<longleftrightarrow> (getSpecBlockPath G x y = Some (x#yl@[y]) \<and>  isPredecessorAll G (x#yl@[y]))"
  and countFrontPathAuxRule1 : "\<forall> t . countFrontPathAux [] t = []"
  and countFrontPathAuxRule2 : "\<forall> x y l t . countFrontPathAux ((x,y)#l) t =
                (if x \<noteq> t then (x,y)#(countFrontPathAux l t) else [(x,y)])"
  and countFrontPathRule1 : "\<forall> a t . countFrontPath [] a t = None"
  and countFrontPathRule2 : "\<forall> x y l a t . countFrontPath ((x,y)#l) a t
                      = (if x = a then Some (countFrontPathAux y t) else countFrontPath l a t)"
  and countBackPathAuxRule1 : "\<forall> t . countBackPathAux [] t = []"
  and countBackPathAuxRule2 : "\<forall> x y l t . countBackPathAux (l@[(x,y)]) t =
                (if x \<noteq> t then (countBackPathAux l t)@[(x,y)] else [(x,y)])"
  and countBackPathRule1 : "\<forall> a t . countBackPath [] a t = None"
  and countBackPathRule2 : "\<forall> x y l a t . countBackPath ((x,y)#l) a t
                      = (if x = a then Some (countFrontPathAux y t) else countBackPath l a t)"
  and countAllBlocksRule1 : "\<forall> G acc . countAllBlocks G [] acc = acc"
  and countAllBlocksRule2 : "\<forall> G x l acc . countAllBlocks G (x#l) acc
                                      = (case getValueInList G x of None \<Rightarrow> countAllBlocks G l acc
                                          | Some acc' \<Rightarrow> countAllBlocks G l (acc@acc'))"
  and countMidPathAuxRule1 : "\<forall> t . countMidPathAux [] t = []"
  and countMidPathAuxRule2 : "\<forall> x y l t . countMidPathAux ((x,y)#l) t =
                (if x \<noteq> t then (countMidPathAux l t) else (x,y)#l)"
  and countMidPathRule1 : "\<forall> a t1 t2 . countMidPath [] a t1 t2 = None"
  and countMidPathRule2 : "\<forall> a x y l t1 t2 . lessThan t1 t2 \<longrightarrow> countMidPath ((x,y)#l) a t1 t2
                       = (if x = a then Some (countFrontPathAux (countMidPathAux y t1) t2)
                           else countMidPath l a t1 t2)"
  and countMidPathRule3 : "\<forall> a x y l t1 t2 . \<not> lessThan t1 t2 \<longrightarrow>
                                 countMidPath ((x,y)#l) a t1 t2  = None"
  and getInstsFromPathRule1 : "\<forall> prog labelMap G bn1 in1 bn2 in2 . 
                              getSpecBlockPath G bn1 bn2 = None
                               \<longrightarrow> getInstsFromPath prog labelMap G bn1 in1 bn2 in2 = None"
  and getInstsFromPathRule2 : "\<forall> prog labelMap G bn1 in1 bn2 in2 l . 
                              getSpecBlockPath G bn1 bn2 = Some l \<and> lookupIntMapAll labelMap l = None
                               \<longrightarrow> getInstsFromPath prog labelMap G bn1 in1 bn2 in2 = None"
  and getInstsFromPathRule3 : "\<forall> prog labelMap G bn1 in1 bn2 in2 l x . 
                     getSpecBlockPath G bn1 bn2 = Some l \<and> lookupIntMapAll labelMap l = Some [x]
                    \<longrightarrow> getInstsFromPath prog labelMap G bn1 in1 bn2 in2 =  countMidPath prog x in1 in2"
  and getInstsFromPathRule4 : "\<forall> prog labelMap G bn1 in1 bn2 in2 l x xl y . 
                getSpecBlockPath G bn1 bn2 = Some l \<and> lookupIntMapAll labelMap l = Some (x#xl@[y])
                 \<longrightarrow> getInstsFromPath prog labelMap G bn1 in1 bn2 in2
                              =  (case countFrontPath prog x in1 of None \<Rightarrow> None
                                   | Some xrl \<Rightarrow> 
                                  (case countBackPath prog y in2 of None \<Rightarrow> None
                                    | Some yrl \<Rightarrow> Some (xrl@(countAllBlocks prog xl [])@yrl)))"
  and hasDefBetweenAuxrule1 :"\<forall> x . \<not> hasDefBetweenAux [] x"
  and hasDefBetweenAuxrule2 :"\<forall> x u v l . hasDefBetweenAux ((u,NoAssign v)#l) x = hasDefBetweenAux l x"
  and hasDefBetweenAuxrule3 :"\<forall> x u v l . hasDefBetweenAux ((u,Assign x v)#l) x"
  and hasDefBetweenAuxrule4 :"\<forall> x x' u v l . x \<noteq> x' \<longrightarrow>
                               hasDefBetweenAux ((u,Assign x' v)#l) x = hasDefBetweenAux l x"
  and hasDefBetweenRule1 : "\<forall> x . \<not> hasDefBetween [] x"
  and hasDefBetweenRule2 : "\<forall> x a l . hasDefBetween (a#l) x = hasDefBetweenAux l x"
   and updateVarListInTermRule1 : "\<forall> m e . updateVarListInTerm m [] e = e"
   and updateVarListInTermRule2 : "\<forall> m e x l v . lookupMap m x = Some v \<longrightarrow> 
                   updateVarListInTerm m (x#l) e = updateVarListInTerm m l (subst e x (ValOfExp v))"
   and updateVarListInTermRule3 : "\<forall> m e x l . lookupMap m x = None \<longrightarrow> 
                           updateVarListInTerm m (x#l) e = updateVarListInTerm m l e"
   and updateAllVarsInTermProperty:
                       "\<forall> m e .  updateAllVarsInTerm m e = updateVarListInTerm m (getFreeVars e) e"
   and updateAllVarsInMetaRule : "\<forall> x e m bn1 in1 lab . 
                 updateAllVarsInMeta m (bn1,in1,(Assign x e),lab) 
                                         = (bn1, in1, Assign x (updateAllVarsInTerm m e), lab)
      \<and> updateAllVarsInMeta m (bn1,in1,(NoAssign e),lab)
                                     = (bn1,in1,NoAssign (updateAllVarsInTerm m e),lab)"
   and updateSpecVarsInTermAuxRule1 : "\<forall> m t . updateSpecVarsInTermAux m [] t = t"
   and updateSpecVarsInTermAuxRule2 : "\<forall> m x y z l t . updateSpecVarsInTermAux m ((x,y,z)#l) t
                                     = updateSpecVarsInTermAux m l (updateSpecVarInTerm m x y z t)"
   and updateSpecVarsInTermRule : "\<forall> m l t . specKeys m = l
                               \<longrightarrow> updateSpecVarsInTerm m t = updateSpecVarsInTermAux m l t"
   and turnSpecMapToListRule : "\<forall> a . turnSpecMapToList (turnListToSpecMap a) = a"
   and turnSpecMapToListProperty : "\<forall> m l . turnSpecMapToList m = l \<and>
                                          (\<forall> ((x,y,u),b) \<in> set l . lookupSpecMap m x y u = Some b)"
   and turnListToSpecMapRule : "\<forall> a . turnListToSpecMap (turnSpecMapToList a) = a"
   and turnListToSpecMapProperty : "\<forall> l m . turnListToSpecMap l = m \<and>
                                      (\<forall> ((x,y,u),b) \<in> set l . lookupSpecMap m x y u = Some b)"
   and getSubNotesProperty : "\<forall> a tr  .  (\<forall> b . isSuccessor tr b a \<longrightarrow> b \<in> set (getSubNotes tr a))
                                      \<and> (\<forall> b . \<not> isSuccessor tr b a \<longrightarrow> b \<notin> set (getSubNotes tr a))"
   and getAllSubNotesRule1 : "\<forall> tr . getAllSubNotes tr [] = []"
   and getAllSubNotesRule2 : "\<forall> tr x l . getAllSubNotes tr (x#l) = (getSubNotes tr x)@(getAllSubNotes tr l)"
   and subListProperty : "\<forall> a b . set (subList a b) = (set a) - (set b)"
   and getAllSubsExpectOneChildProperty : "\<forall> tr me child . getAllSubsExpectOneChild tr me child
                                  = getAllSubNotes tr (subList (getChildren tr me) [child])"
   and selectNotesInSpecMapRule : "\<forall> tr x . selectNotesInSpecMap tr x = selectEntries (turnSpecMapToList tr) x"
   and addElementsToMapRule1 : "\<forall> m . addElementsToMap m [] = m"
   and addElementsToMapRule2 : "\<forall> m x y z b l . addElementsToMap m (((x,y,z),b)#l)
                                      = addElementsToMap (updateMap m z b) l"
   and splitBytesProperty : "\<forall> t e v . splitBytes t e = Some v \<longleftrightarrow> joinBytes t v = Some e"
   and valsToBytesRule1 : "valsToBytes [] = Some []"
   and valsToBytesRule2 : "\<forall> x l . valsToBytes ((ByteOfVal x)#l) = (case valsToBytes l of None \<Rightarrow> None
                                       | Some l' \<Rightarrow> Some (x#l'))"
   and valsToBytesRule3 : "\<forall> x l . \<not> (\<exists> v . x = ByteOfVal v) \<longrightarrow> valsToBytes (x#l) = None"
   and updateLoadMapRule1 : "\<forall> x y z i v . updateLoadMap [] x y z i v = None"
   and updateLoadMapRule2 : "\<forall> x y z t i v x' y' z' m l .
                    x' \<noteq> x \<or> y' \<noteq> y \<or> z' \<noteq> z \<longrightarrow> updateLoadMap (((x',y',z'),t,m)#l) x y z i v
                      = (case updateLoadMap l x y z i v of None \<Rightarrow> None
                           | Some newl \<Rightarrow> Some (((x',y',z'),t,m)#l))"
   and updateLoadMapRule3 : "\<forall> x y z t i v m l . i \<in> set (intKeys m) \<longrightarrow>
            updateLoadMap (((x,y,z),t,m)#l) x y z i v = None"
   and updateLoadMapRule4 : "\<forall> x y z t i v m l . i \<notin> set (intKeys m) \<longrightarrow>
            updateLoadMap (((x,y,z),t,m)#l) x y z i v = Some (((x,y,z),t,updateIntMap m i (ValOfByte v))#l)"
   and createLoadEntryRule : "\<forall> x y z t l . createLoadEntry l x y z t = ((x,y,z),t,emptyIntMap)#l"
   and isLoadFullProperty : "\<forall> l x y z . (\<exists> t im . ((x,y,z),t,im) \<in> set l \<and> sizeof t = length (intKeys im)
                                                    \<longrightarrow> isLoadFull l x y z)"
   and getValueFromLoadMapProperty : "\<forall> l x y z . (\<exists> t im vl vl' . ((x,y,z),t,im) \<in> set l
               \<and> lookupIntMapAll im (sortIntList (intKeys im)) = some vl \<and> valsToBytes vl = Some vl'
                \<longrightarrow> getValueFromLoadMap l x y z = joinBytes t vl')"
  and sortIntListProperty : "\<forall> l l' . sortIntList l = l' \<longrightarrow>
              (\<forall> i . i \<le> (length l' - 1) \<and> i \<ge> 0 \<and> (\<exists> x y . adjTwo i l' = Some (x,y) \<longrightarrow> lessThan x y))"
  and substMetaExpProperty : "\<forall> e x y .  (substMetaExp (NoAssign e) x y = NoAssign (subst e x y))
                                   \<and> (substMetaExp (Assign a e) x y = Assign a (subst e x y))"
  and getValOfExpProperty1 : "\<forall> v . getValOfExp (ValOfExp v) = Some v"
  and getValOfExpProperty2 : "\<forall> e . \<not> (\<exists> v . e = (ValOfExp v)) \<longrightarrow> getValOfExp e = None"
  and zeroProperty : "\<forall> i . theZero = i \<or> lessThan theZero i"
  and zeroAddRule : "thePlus theZero theZero = theZero \<and> (\<forall> i . thePlus theZero i = i)
                       \<and> (\<forall> i . thePlus i theZero = i)"
  and emptyTreeProperty : "(\<forall> a b . \<not> isPredecessorList emptyTree a b) 
      \<and> (\<forall> a . \<not> isPredecessorAll emptyTree a) \<and> (\<forall> a b . \<not> isChild emptyTree a b) 
      \<and>  (\<forall> a . getChildren emptyTree a = []) \<and> (\<forall> a b . \<not> isFather emptyTree a b)
        \<and>  (\<forall> a b . \<not> isSuccessor emptyTree a b)  \<and>  (\<forall> a b . \<not> isPredecessor emptyTree a b)"
  and stackProperty : "\<forall> s a . popOut (popIn s a) = (Some a, s)"
  and emptyStackProperty : "popOut emptyStack = (None, emptyStack)"
  and tidCounterProperty : "\<forall> a l . tidCounter l = a \<longrightarrow> a \<notin> set l"

context elements begin

fun substAllAux :: "('int * 'metaExp) list \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('int * 'metaExp) list" where
"substAllAux [] x y = []"
| "substAllAux ((a,b)#l) x y = (a,substMetaExp b x (ValOfExp y))#(substAllAux l x y)"

fun substAll :: "('val * ('int * 'metaExp) list) list
     \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('val * ('int * 'metaExp) list) list" where
"substAll [] x y = []"
| "substAll ((a,b)#l) x y = (a, substAllAux b x y)#(substAll l x y)"

fun getValOfExpList :: "'exp list \<Rightarrow> 'val list option" where
"getValOfExpList [] = Some []"
| "getValOfExpList (x#l) = (case getValOfExp x of None \<Rightarrow> None
                   | Some x' \<Rightarrow> (case getValOfExpList l of None \<Rightarrow> None
                      | Some l' \<Rightarrow> Some (x'#l')))"


fun updateMapAll :: "'map \<Rightarrow> 'var list \<Rightarrow> 'val list \<Rightarrow> 'map option" where
"updateMapAll m [] [] = Some m"
| "updateMapAll m (x#l) (y#yl) = updateMapAll (updateMap m x y) l yl"
| "updateMapAll m A B = None"

end

end
