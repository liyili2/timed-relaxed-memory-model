theory memorymodel
imports Main elements
begin

datatype ordering = Unordered | Relex | Acquire | Release | AcqRel | Seq

locale specTreeFuns =
  fixes lessThan :: "'int \<Rightarrow> 'int \<Rightarrow> bool"
    and isFather :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and getFather :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int option"
    and getChildren :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int list"
    and isPredecessor :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool" 
    and updateSpecTree :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'specTree"
    and emptyTree :: "'specTree"
 assumes updateSpecTreeRule : "\<forall> specTree a b . isFather (updateSpecTree specTree b a) b a"
     and specTreeProperty1 : "\<forall> ST x y . isFather ST x y \<longrightarrow> isPredecessor ST x y \<and> \<not> isPredecessor ST y x"
  and specTreeProperty2 : "\<forall> ST x y . isFather ST x y \<longrightarrow> \<not> isFather ST y x"
  and specTreeUniqueFather1 : "\<forall> ST x y x' . isFather ST x y \<and> isFather ST x' y \<longrightarrow> x = x'"
  and specTreeProperty3 : "\<forall> ST x y . isPredecessor ST x y \<longrightarrow>  \<not> isPredecessor ST y x"
  and specTreeProperty4 : "\<forall> ST x y z . isPredecessor ST x y \<and> isPredecessor ST y z \<longrightarrow> isPredecessor ST x z"
  and specTreeProperty5 : "\<forall> ST x y . isFather ST x y \<longrightarrow> isPredecessor ST x y"
  and getChildrenRule : "\<forall> m i l . getChildren m i = l \<longrightarrow> (\<forall> x \<in> set l . isChild m x i)"
  and getFatherProperty : "\<forall> T a b . getFather T a = Some b \<longleftrightarrow> isFather T b a"
  and lessThanPro1 : "\<forall> a b . lessThan a b \<longrightarrow> \<not> lessThan b a \<and> a \<noteq> b"
  and lessThanPro2 : "\<forall> a b c . lessThan a b \<and> lessThan b c \<longrightarrow> lessThan a c"
context specTreeFuns begin

fun isChild where
"isChild G s t = isFather G t s"

fun isSuccessor where
"isSuccessor G s t = isPredecessor G t s"

fun isPredecessorList :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int list \<Rightarrow> bool" where
"isPredecessorList st i [] = True"
| "isPredecessorList st i (x#l) = (isPredecessor st i x \<and> isPredecessorList st i l)"

fun isPredecessorAll :: "'specTree \<Rightarrow> 'int list \<Rightarrow> bool" where
"isPredecessorAll G [] = True"
| "isPredecessorAll G (x#l) = (isPredecessorList G x l \<and> isPredecessorAll G l)"

fun isFatherChain :: "'specTree \<Rightarrow> 'int list \<Rightarrow> bool" where
"isFatherChain G [] = True"
| "isFatherChain G [x] = True"
| "isFatherChain G (x#(y#l)) = (isFather G x y \<and> isFatherChain G (y#l))"

end

locale memElements = specTreeFuns where
       lessThan = "lessThan :: 'int \<Rightarrow> 'int \<Rightarrow> bool"
       and isFather = "isFather :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
     and getFather = "getFather :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int option"
    and getChildren = "getChildren :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int list"
    and isPredecessor = "isPredecessor :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool" 
    and updateSpecTree = "updateSpecTree :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'specTree"
    and emptyTree = "emptyTree :: 'specTree"
   for lessThan isFather getFather getChildren isPredecessor updateSpecTree emptyTree +
   fixes getPath :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'int list option" 
    and AWrite :: "'val \<Rightarrow> 'type \<Rightarrow> 'byte list \<Rightarrow> ordering \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and ARead :: "'val \<Rightarrow> 'type \<Rightarrow> ordering \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and Malloc :: "'type \<Rightarrow> int \<Rightarrow> 'int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> 'memExp"
                (* type, size of the type, addrspace, align, constant?*)
    and splitBytes :: "'type \<Rightarrow> 'val \<Rightarrow> 'byte list option"
    and joinBytes :: "'type \<Rightarrow> 'byte list \<Rightarrow> 'val option"
    and sizeof :: "'type \<Rightarrow> int"
    and updateIntMap :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'val \<Rightarrow> 'specTree"
    and lookupIntMap :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'val option"
    and intValues :: "'specTree \<Rightarrow> 'val list"
    and updateSpecMemOps :: "'specTree \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'memExp * bool) list \<Rightarrow> 'specTree"
    and lookupSpecMemOps :: "'specTree \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'memExp * bool) list"
    and markMemOpDone :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'specTree"
    and getAllMemOpsInList :: "('int * 'int * 'memExp * bool) list \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'memExp * bool) list"
    and getAllMemOpsAux :: "'specTree \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'memExp * bool) list"
    and getAllMemOps :: "'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> ('int * 'int * 'memExp * bool) list"
    and getOrdering :: "'memExp \<Rightarrow> ordering"
  assumes intKeysRule : "\<forall> x map v . lookupIntMap map x = Some v \<longleftrightarrow> x \<in> set (intKeys map)"
   and intValuesRule : "\<forall> x map v . lookupIntMap map x = Some v \<longleftrightarrow> v \<in> set (intValues map)"
  and intMapProperty1 : "\<forall> v e m . lookupIntMap (updateIntMap m v e) v = Some e"
  and intMapProperty2 : "\<forall> v m . \<not> (\<exists> e' e . lookupIntMap m v = Some e
                                                 \<and> lookupIntMap m v = Some e' \<and> e \<noteq> e')"
  and getPathProperty : "\<forall> G x y l . (getPath G x y = Some l \<longleftrightarrow> isFatherChain G (x#l@[y])
                 \<and> getPath G x y = None \<longleftrightarrow> (\<not> isPredecessor G x y \<and> \<not> isPredecessor G y x))"
   and getAllMemOpsInListProperty : "\<forall> l i l' . getAllMemOpsInList l i = l' \<longleftrightarrow> 
                               (\<forall> i' x y. lessThan i' i \<and> (x,i',y) \<in> set l
                                    \<longrightarrow> (x,i',y) \<in> set l')
                               \<and> (\<forall> i' x y. (\<not> lessThan i' i) \<and> (x,i',y) \<in> set l
                                    \<longrightarrow> (x,i',y) \<notin> set l')"
   and getAllMemOpsAuxProperty : "\<forall> T a b . 
                         ((getFather T a = None \<longrightarrow> getAllMemOpsAux T a = lookupSpecMemOps T a)
                        \<and> (getFather T a = Some b \<longrightarrow>
                               getAllMemOpsAux T a = lookupSpecMemOps T a @(getAllMemOpsAux T b)))"
   and getAllMemOpsProperty : "\<forall> T a b c . 
     ((getFather T a = None \<longrightarrow> getAllMemOps T a b = getAllMemOpsInList (lookupSpecMemOps T a) b)
      \<and> (getFather T a = Some c \<longrightarrow>
              getAllMemOps T a b = getAllMemOpsAux T a @(getAllMemOpsInList (lookupSpecMemOps T a) b)))"
   and getOrderingProperty : "\<forall> a b c d e . getOrdering (AWrite a b c d e) = d 
                                  \<and> getOrdering (ARead a b d e) = d"
   and markMemOpDoneProperty : "\<forall> T a b l . lookupSpecMemOps T a = l \<longrightarrow>
        markMemOpDone T a b = updateSpecMemOps T a
                           (List.map (\<lambda> (x,y,u,v) . if y = b then (x,y,u,True) else (x,y,u,v)) l)"

context memElements begin

fun getBlockBodyByInstNum where
"getBlockBodyByInstNum prog labelMap x = (case lookupIntMap labelMap x of None \<Rightarrow> None
                 | Some a \<Rightarrow> (case getValueInList prog a of None \<Rightarrow> None
                  | Some b \<Rightarrow> Some b))"

fun getAllBlocksByNums where
"getAllBlocksByNums prog labelMap [] = Some []"
| "getAllBlocksByNums prog labelMap (x#l) = (case getBlockBodyByInstNum prog labelMap x of None \<Rightarrow> None
              | Some bl \<Rightarrow> (case getAllBlocksByNums prog labelMap l of None \<Rightarrow> None
                  | Some ll \<Rightarrow> Some (bl@ll)))"

fun countFrontInsts where
"countFrontInsts [] a = None"
| "countFrontInsts ((x,y)#l) a = (if x = a then Some [(x,y)] else (case countFrontInsts l a of None \<Rightarrow> None
                                    | Some l' \<Rightarrow> Some ((x,y)#l')))"

fun countBackInsts where
"countBackInsts l a = (case countFrontInsts (rev l) a of None \<Rightarrow> None | Some l' \<Rightarrow> Some (rev l'))"

fun getAllBlocksByInts where
"getAllBlocksByInts prog labelMap specTree xb xl yb yl = (case getPath specTree xb yb of None \<Rightarrow> None
          | Some l \<Rightarrow> (case getAllBlocksByNums prog labelMap l of None \<Rightarrow> None
          | Some l' \<Rightarrow> (case lookupIntMap labelMap xb of None \<Rightarrow> None
           | Some xb' \<Rightarrow> (case getValueInList prog xb' of None \<Rightarrow> None
             | Some xll \<Rightarrow> (case countBackInsts xll xl of None \<Rightarrow> None
               | Some rxl \<Rightarrow> (case lookupIntMap labelMap yb of None \<Rightarrow> None
          | Some yb' \<Rightarrow> (case getValueInList prog yb' of None \<Rightarrow> None
         | Some yll \<Rightarrow> (case countFrontInsts yll yl of None \<Rightarrow> None
             | Some ryl \<Rightarrow> Some (rxl@l'@ryl)))))))))"

end
fun getAlignValue :: "int \<Rightarrow> int \<Rightarrow> int" where
"getAlignValue base al = (if base mod al = 0 then 0 else al - (base mod al))"

(* assuming variables are in static single assignment format *)
locale threadMemory = memElements where
        isFather = "isFather :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool"
    and getChildren = "getChildren :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int list"
    and isPredecessor = "isPredecessor :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> bool" 
    and updateSpecTree = "updateSpecTree :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'int \<Rightarrow> 'specTree"
    and emptyTree = "emptyTree :: 'specTree"
    and AWrite = "AWrite :: 'val \<Rightarrow> 'type \<Rightarrow> 'byte list \<Rightarrow> ordering \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and ARead = "ARead :: 'val \<Rightarrow> 'type \<Rightarrow> ordering \<Rightarrow> 'flags \<Rightarrow> 'memExp"
    and Malloc = "Malloc :: 'type \<Rightarrow> int \<Rightarrow> 'int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> 'memExp"
    and splitBytes = "splitBytes :: 'type \<Rightarrow> 'val \<Rightarrow> 'byte list option"
    and joinBytes = "joinBytes :: 'type \<Rightarrow> 'byte list \<Rightarrow> 'val option"
    and sizeof = "sizeof :: 'type \<Rightarrow> int"
    and updateIntMap = "updateIntMap :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'val \<Rightarrow> 'specTree"
    and lookupIntMap = "lookupIntMap :: 'specTree \<Rightarrow> 'int \<Rightarrow> 'val option"
    and intValues = "intValues :: 'specTree \<Rightarrow> 'val list"
  for isFather getChildren  isPredecessor updateSpecTree emptyTree AWrite ARead Malloc splitBytes joinBytes
    sizeof updateIntMap lookupIntMap intValues +
  fixes convertExpToMemExp :: "'metaExp \<Rightarrow> 'memExp option"
   and insertToMemCell :: "(('int * 'int * 'memExp * bool) set
          * ('int * 'int * 'memExp * bool) set * ('int * 'int * 'memExp * bool) set)
                  \<Rightarrow>  'int \<Rightarrow> 'int \<Rightarrow> 'memExp
                  \<Rightarrow> (( 'int * 'int * 'memExp * bool) set
          * ('int * 'int * 'memExp * bool) set * ('int * 'int * 'memExp * bool) set)"
   and createObj :: "int \<Rightarrow> 'type \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> 'int \<Rightarrow> 'object"
                   (* base, type, size, align-val, constant?, addrspace *)
   and createChunck :: "int \<Rightarrow> int \<Rightarrow> 'type \<Rightarrow> 'memChunck"
                  (* base, size, type *)
   and createChuncks :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'type \<Rightarrow> 'memChunck list"
   and MemChunck :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'type \<Rightarrow> bool \<Rightarrow> int set \<Rightarrow> (int, 'memChunck) map \<Rightarrow> 'memChunck"
        (* base, size, align, type of the chunck, initial?, set of child chunck bases, child chunck map*)
   and MemObject :: "(int * int) \<Rightarrow> 'memChunck list \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> 'int
        \<Rightarrow> (('tid * 'int * 'int), int) map \<Rightarrow> ('tid * 'int * 'int * (int * int)) set \<Rightarrow> 'object"
         (* chunckrange, mem chunck list, algin, isConst?, addrspace, complete, stay in race *)
   and threadMemOpCell :: "'tid \<Rightarrow> 'int \<Rightarrow> 'specTree \<Rightarrow> (('int * 'int * 'memExp * bool) set
          * ('int * 'int * 'memExp * bool) set * ('int * 'int * 'memExp * bool) set) \<Rightarrow> bool"
   and MemCell :: "('tid * 'int * 'int * 'memExp) list
                \<Rightarrow> (int * int) \<Rightarrow> (int * int) list
          \<Rightarrow> 'object set \<Rightarrow> (int,'byte) map \<Rightarrow> bool"
               (* mem op list \<Rightarrow> mem range \<Rightarrow> mem chunck ranges \<Rightarrow> object set *)
   and isAvaliable :: "('int * 'int * 'memExp * bool) list \<Rightarrow> 'memExp \<Rightarrow> bool"
 assumes insertToMemCellProperty : "\<forall> a b c x y z . insertToMemCell (a,b,c) x y z = (a,b,insert (x,y,z,False) c)"
   and createObjDef : "\<forall> base type s alv b ad . createObj base type s alv b ad
            = (MemObject (base, base + alv + (sizeof type) * s) (createChuncks s (base + alv) (sizeof type) type)
                    alv b ad empty {})"
   and createChuncksDef : "\<forall> n base s t . createChuncks 0 base s t = []
                        \<and> (n > 0 \<longrightarrow> createChuncks n base s t = (createChunck base s t)#(createChuncks (n - 1) (base + s) s t))"
   and threadMove1 : "\<forall> t cur specTree S . threadMemOpCell t cur specTree S \<longrightarrow>
                              (\<exists> a b c . threadMemOpCell t cur specTree (insertToMemCell S a b c))"
   and threadRemove : "\<forall> t cur specTree good partial not . threadMemOpCell t cur specTree (good, partial, not)
          \<longrightarrow> threadMemOpCell t cur specTree (good, partial
              - {(a,b,c,d) \<in> partial . \<not> isFather specTree cur a \<and> \<not> isFather specTree a cur},
            not - {(a,b,c,d) \<in> not . \<not> isFather specTree cur a \<and> \<not> isFather specTree a cur})"
   and threadMoveToAva : "\<forall> t cur specTree good partial not a b c d l. threadMemOpCell t cur specTree (good, partial, not)
   \<and> (a,b,c,d) \<in> not \<and> (a = cur \<or> isFather specTree a cur) \<and> getAllMemOps specTree a b = l 
   \<and> isAvaliable l c \<longrightarrow> threadMemOpCell t cur specTree (insert (a,b,c,d) good, partial, Set.remove (a,b,c,d) not)"
   and threadMoveToPar : "\<forall> t cur specTree good partial not a b c d l. threadMemOpCell t cur specTree (good, partial, not)
   \<and> (a,b,c,d) \<in> not \<and> isFather specTree cur a \<and> getAllMemOps specTree a b = l 
   \<and> isAvaliable l c \<longrightarrow> threadMemOpCell t cur specTree (good, insert (a,b,c,d) partial, Set.remove (a,b,c,d) not)"
   and threadMoveToAvaFromPar : "\<forall> t cur specTree good partial not a b c d . threadMemOpCell t cur specTree (good, partial, not)
   \<and> (a,b,c,d) \<in> partial \<and> isFather specTree cur a 
          \<longrightarrow> threadMemOpCell t cur specTree (insert (a,b,c,d) good, Set.remove (a,b,c,d) partial, not)"
  and threadMoveToMem : "\<forall> t cur specTree good partial not a b c d S memRange chunckRanges objs bytemap .
              threadMemOpCell t cur specTree (good, partial, not)
          \<and> MemCell S memRange chunckRanges objs bytemap \<and> (a,b,c,d) \<in> good
                \<longrightarrow> MemCell (S@[(t, a,b,c)]) memRange chunckRanges objs bytemap
                      \<and> threadMemOpCell t cur (markMemOpDone specTree a b) (remove (a,b,c,d) good, partial, not)"
  and memMalloc : "\<forall> tid bn inst t s ad al b S down up ranges objs bytem .
     MemCell ((tid, bn, inst, Malloc t s ad al b)#S) (down, up) ranges objs bytem
     \<longrightarrow> MemCell S (down, up + ((sizeof t) * s) + getAlignValue up al) ranges
           (insert (createObj up t s (getAlignValue up al) b ad) objs) bytem"


end
