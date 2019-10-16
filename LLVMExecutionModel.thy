theory LLVMExecutionModel
imports Main
begin

datatype memId = MemId int int int

datatype bit = One | Zero | Undef

datatype atype = IntType nat | PointerType atype | ArrayType nat atype

(* global setting section *)
definition pointerSize :: "nat" where
"pointerSize = 64"

definition tidSize :: "nat" where
"tidSize = 64"

definition maxSpec :: "nat" where
"maxSpec = 4"

definition maxInstQueue :: "nat" where
"maxInstQueue = 20"

definition byteSize :: "nat" where
"byteSize = 8"

fun bitsof where
"bitsof (IntType a) = a"
| "bitsof (PointerType a) = pointerSize"
| "bitsof (ArrayType n x) = (n * (bitsof x))"

fun sizeof where
"sizeof (IntType a) = (if a mod byteSize = 0 then a div byteSize else a div byteSize + 1)"
| "sizeof (PointerType a) = pointerSize div byteSize"
| "sizeof (ArrayType n x) = (n * (sizeof x))"

datatype 'id element = IntVal "bit list" "atype" "(nat \<times> nat) option" "(nat \<times> nat) option"
  | Local "'id" | Pointer "bit list" "atype" "(nat \<times> nat) option" "(nat \<times> nat) option"
  | GlobalUndef | Poison | ArrayVal "'id element list"

datatype order = Unordered | Monotonic | Acquire | Release | AcqRel | Seq 

datatype icmpFactor = Eq | Ne | Lt | Leq | Gt | Geq

datatype ('id, 'a) stmt =
    Add "'id" "'id element" "'id element"
  | Sub "'id" "'id element" "'id element"
  | GEP "'id" bool "atype" "'id element" "(bool \<times> 'id element) list"
  (* return-value, inboud-flag, type, poniter-to-cal, indexes with inrange *)
  | ExtractValue "'id" "'id element" "int list"
  | InsertValue "'id" "'id element" "'id element" "int list" 
  | Phi "'id" "('id element \<times> 'id) list"
  | Malloc "'id" "nat"
  | Bitcast "'id" "'id element" "atype"
  | Inttoptr "'id" "'id element" "atype"
  | Ptrtoint "'id" "'id element" "atype"
  | Fence "order"
  | Store "atype" "'id element" "'id element" bool  (* indicating volitile or not *)
  | AtomicStore "atype" "'id element" "'id element" "order" bool (* indicating volitile or not *)
  | Load "'id" "atype" "'id element" bool (* loading a value type from a pointer / indicating volitile or not *)
  | AtomicLoad "'id" "atype" "'id element" "order" bool  (* indicating volitile or not *)
  | CreateThread "'id" "'id" "('id element) list"
  | ThreadJoin 'id "'id element"
  | Call "'id" "'id" "('id element) list"
               (* return value, call function id, if return void, then undef *)
  | Icmp "'id" icmpFactor "'id element" "'id element"
  | Br "'id element" "'id" "'id"
  | UnBr "'id"
  | Return "'id element"
  | Other "'a"

(* define error state *)
datatype error = MemOutOfRange | NotValidPointer | UndefinedBehavior | StoreRace | LoadRace

datatype ('a,'b) state = State "'a" | Error "'b"

(* memory opeartions in memory model
  byte can have a bit list or a None indicating a poison value *)
datatype byte = Byte "bit list option" "(nat \<times> nat) option" "(nat \<times> nat) option"

datatype memOp = Write nat nat "byte list" order
               (* base, number of writes from the store, list of byte, order*)
  | Read nat nat nat nat order (* base, read-position in the load op,
                       number of reads from the load, number of bytes to read, order*)
  | MemFence order
  | Create nat
  | WaitMsg nat
  | WaitToRead nat nat nat (* message number, base, byte number *)

(* each basic block is a combination of block id, (inst-id x inst) list and a terminator inst *)
datatype ('id, 'a) block = BasicBlock "'id" "(nat \<times> ('id, 'a) stmt) list" "(nat \<times> ('id, 'a) stmt)"

(* require the first block in the list is the entry block *)
datatype ('id,'a) program = Prog "'id" "'id list" "('id,'a) block list"

(* fathers used in the specDDG *)
datatype 'id memFactor = ToRead "'id element" "order option" bool (* value/variable, order, volitile or not *)
  | ToWrite "'id element" "order option" bool (* vale/var, order, volitile or not *)
  | AFence order | CallFence | ControlFence

datatype 'id memProto = MemProto nat "'id memFactor" nat nat
          (* instruction-ID, memFactor,  number of op commiting, a nat flag for number of store needing to commit *)

fun getUseVarInElem where
"getUseVarInElem (Local x) = {x}"
| "getUseVarInElem (ArrayVal xl) = (List.foldl (\<lambda> S x . S \<union> (getUseVarInElem x)) {} xl)"
| "getUseVarInElem x = {}"

fun getUseVars where
"getUseVars (Add x y z) = (getUseVarInElem y \<union> getUseVarInElem z)"
| "getUseVars (Sub x y z) = (getUseVarInElem y \<union> getUseVarInElem z)"
| "getUseVars (GEP x y z u v) = (getUseVarInElem u \<union> List.foldl (\<lambda> S (a,b) . S \<union> getUseVarInElem b) {} v)"
| "getUseVars (ExtractValue x y z) = getUseVarInElem y"
| "getUseVars (InsertValue x y z u) = getUseVarInElem y \<union> getUseVarInElem z"
| "getUseVars (Phi x y) = List.foldl (\<lambda> S (a,b) . S \<union> getUseVarInElem a) {} y"
| "getUseVars (Malloc x y) = {x}"
| "getUseVars (Bitcast x y z) = getUseVarInElem y"
| "getUseVars (Inttoptr x y z) = getUseVarInElem y"
| "getUseVars (Ptrtoint x y z) = getUseVarInElem y"
| "getUseVars (Fence x) = {}"
| "getUseVars (Store x y z u) = getUseVarInElem y \<union> getUseVarInElem z"
| "getUseVars (AtomicStore x y z u v) = getUseVarInElem y \<union> getUseVarInElem z"
| "getUseVars (Load x y z u) = getUseVarInElem z"
| "getUseVars (AtomicLoad x y z u v) = getUseVarInElem z"
| "getUseVars (CreateThread x y z) = List.foldl (\<lambda> S a . S \<union> getUseVarInElem a) {} z"
| "getUseVars (ThreadJoin x y) = getUseVarInElem y"
| "getUseVars (Call x y z) = List.foldl (\<lambda> S a . S \<union> getUseVarInElem a) {} z"
| "getUseVars (Icmp x y z u) = getUseVarInElem z \<union> getUseVarInElem u"
| "getUseVars (Br x y z) = getUseVarInElem x"
| "getUseVars (UnBr x) = {}"
| "getUseVars (Return x) = getUseVarInElem x"
| "getUseVars (Other x) = {}"

fun getAllUsesInBlocks where
"getAllUsesInBlocks [] = {}"
| "getAllUsesInBlocks ((BasicBlock x y z)#xs)
      = (List.foldl (\<lambda> S (a,b) . getUseVars b \<union> S) {} (z#y)) \<union> (getAllUsesInBlocks xs)"

fun getAllUsesInProg where
"getAllUsesInProg (Prog x y z) = getAllUsesInBlocks z"

fun getAllUsesInInsts where
"getAllUsesInInsts [] = {}"
| "getAllUsesInInsts ((a,b)#xs) = getUseVars b \<union> getAllUsesInInsts xs"

fun getDefVar where
"getDefVar (Add x y z) = {x}"
| "getDefVar (Sub x y z) = {x}"
| "getDefVar (GEP x y z u v) = {x}"
| "getDefVar (ExtractValue x y z) = {x}"
| "getDefVar (InsertValue x y z u) = {x}"
| "getDefVar (Phi x y) = {x}"
| "getDefVar (Malloc x y) = {x}"
| "getDefVar (Bitcast x y z) = {x}"
| "getDefVar (Inttoptr x y z) = {x}"
| "getDefVar (Ptrtoint x y z) = {x}"
| "getDefVar (Fence x) = {}"
| "getDefVar (Store x y z u) = {}"
| "getDefVar (AtomicStore x y z u v) = {}"
| "getDefVar (Load x y z u) = {x}"
| "getDefVar (AtomicLoad x y z u v) = {x}"
| "getDefVar (CreateThread x y z) = {x}"
| "getDefVar (ThreadJoin x y) = {x}"
| "getDefVar (Call x y z) = {x}"
| "getDefVar (Icmp x y z u) = {x}"
| "getDefVar (Br x y z) = {}"
| "getDefVar (UnBr x) = {}"
| "getDefVar (Return x) = {}"
| "getDefVar (Other x) = {}"

fun getAllDefsInBlocks where
"getAllDefsInBlocks [] = {}"
| "getAllDefsInBlocks ((BasicBlock x y z)#xs)
      = (List.foldl (\<lambda> S (a,b) . getDefVar b \<union> S) {} (z#y)) \<union> (getAllDefsInBlocks xs)"

fun getAllDefsInProg where
"getAllDefsInProg (Prog x y z) = getAllDefsInBlocks z"

fun getAllDefsInInsts where
"getAllDefsInInsts [] = {}"
| "getAllDefsInInsts ((a,b)#xs) = getDefVar b \<union> getAllDefsInInsts xs"

fun getAllPreDefsInBlocks where
"getAllPreDefsInBlocks [] = {}"
| "getAllPreDefsInBlocks ((BasicBlock x y z)#xs) = insert x (getAllPreDefsInBlocks xs)"

fun getAllPreDefsInProg where
"getAllPreDefsInProg (Prog x y z) = (set y) \<union> (getAllPreDefsInBlocks z)"

fun ssaCheck and ssaCheckAux where
"ssaCheck [] S2 = True"
| "ssaCheck ((BasicBlock bn al fi)#l) S2 = ssaCheckAux (al@[fi]) l (insert bn S2)"
| "ssaCheckAux [] l S2 = ssaCheck l S2"
| "ssaCheckAux ((a,b)#xl) l S2 = ((\<not> (getDefVar b \<subseteq> S2)) \<and> ssaCheckAux xl l (getDefVar b \<union> S2))"

fun wellFormTwo and wellFormTwoAux where
"wellFormTwo [] S2 = True"
| "wellFormTwo ((BasicBlock bn al fi)#l) S2 = wellFormTwoAux (al@[fi]) l S2"
| "wellFormTwoAux [] l S2 = wellFormTwo l S2"
| "wellFormTwoAux ((a,b)#xl) l S2 = ((\<not> (a \<in> S2)) \<and> (wellFormTwoAux xl l (insert a S2)))"

fun wellFormOne where
"wellFormOne [] = True"
| "wellFormOne (x#xs) = ((\<not> x \<in> set xs) \<and> (wellFormOne xs))"

fun orderCorrect where
"orderCorrect z =
      (\<forall> x . x \<in> (List.foldl (\<lambda> r b . (case b of (BasicBlock bn al fi) \<Rightarrow> set (al@[fi]) \<union> r)) {} z)
             \<longrightarrow> (case x of (n,Fence ord) \<Rightarrow> ord \<noteq> Unordered \<and> ord \<noteq> Monotonic
                         | (n,AtomicStore x y u ord v) \<Rightarrow> ord \<noteq> Release \<and> ord \<noteq> AcqRel
                         |  (n,AtomicLoad x y u ord v) \<Rightarrow> ord \<noteq> Acquire \<and> ord \<noteq> AcqRel
                         | _ \<Rightarrow> True))"

fun terminatorOnly where
"terminatorOnly [] = True"
| "terminatorOnly ((BasicBlock bn al fi)#xs) = 
     (case fi of (n,Br x y z) \<Rightarrow> terminatorOnly xs
              | (n,UnBr x) \<Rightarrow> terminatorOnly xs
              | (n, Return x) \<Rightarrow> terminatorOnly xs
              | _ \<Rightarrow> False)"

definition wellform :: " ('id,'a) program \<Rightarrow> bool" where
"wellform a = (case a of Prog x y z \<Rightarrow>
                      (wellFormOne (x#y)) \<and> wellFormTwo z {} \<and> ssaCheck z (insert x (set y))
                       \<and> orderCorrect z \<and> terminatorOnly z)"

(* dominance check helper functions *)
fun isPhi where
"isPhi (Phi a b) = True"
| "isPhi x = False"

fun findInstsByBlockName where
"findInstsByBlockName [] a = None"
| "findInstsByBlockName ((BasicBlock x y z)#xs) a =
     (if a = x then Some (y@[z]) else findInstsByBlockName xs a)"

fun findInstsByBlockNameProg where
"findInstsByBlockNameProg (Prog x y z) u = findInstsByBlockName z u"

fun allInstsInProgAux where
"allInstsInProgAux [] = {}"
| "allInstsInProgAux ((BasicBlock x y z)#xs)
          = insert z (set y) \<union> (allInstsInProgAux xs)"

fun allInstsInProg where
"allInstsInProg (Prog x y z) = allInstsInProgAux z"

fun findBlockNameByInst where
"findBlockNameByInst [] x = None"
| "findBlockNameByInst ((BasicBlock x y z)#xs) u =
      (if List.foldl (\<lambda> B (a,b) . if a = u then True else B) False (z#y)
           then Some x else findBlockNameByInst xs u)"

fun findBlockNameByInstProg where
"findBlockNameByInstProg (Prog x y z) u = findBlockNameByInst z u"

fun findAllInEdges where
"findAllInEdges [] x = []"
| "findAllInEdges ((BasicBlock x y (n,Br u v w))#xs) h = 
     (if v = h \<or> w = h then x#(findAllInEdges xs h) else findAllInEdges xs h)"
| "findAllInEdges ((BasicBlock x y (n,UnBr u))#xs) h = 
     (if u = h then x#(findAllInEdges xs h) else findAllInEdges xs h)"
| "findAllInEdges ((BasicBlock x y z)#xs) h = findAllInEdges xs h"

fun findAllInEdgesProg where
"findAllInEdgesProg (Prog x y z) u = findAllInEdges z u"

fun formInEdgesMapAux where
"formInEdgesMapAux [] S = Map.empty"
| "formInEdgesMapAux ((BasicBlock x y z)#xs) S
           = (formInEdgesMapAux xs S)(x \<mapsto> (findAllInEdges S x))"

definition formInEdgesMap where
"formInEdgesMap p = (case p of (Prog x y S) \<Rightarrow> formInEdgesMapAux S S)"

fun allFunVarsInInst where
"allFunVarsInInst (CreateThread x y l) = {y}"
| "allFunVarsInInst (Call x y l) = {y}"
| "allFunVarsInInst x = {}"

fun allFunVarsInBlocks where
"allFunVarsInBlocks [] = {}"
| "allFunVarsInBlocks ((BasicBlock x l z)#xs) =
    (List.foldl (\<lambda> S (a,b) . allFunVarsInInst b \<union> S) {} (l@[z])) \<union> (allFunVarsInBlocks xs)"

fun allFunVarsInProg where
"allFunVarsInProg (Prog x y z) = allFunVarsInBlocks z"

type_synonym ('id, 'a) blockHolder = "(int \<times> ('id, 'a) block)"
type_synonym 'id currBlock = "(int \<times> 'id)"

fun getBlock where
"getBlock [] a = None"
| "getBlock ((BasicBlock x y z)#xl) a = (if a = x then Some (y@[z]) else getBlock xl a)"

fun getInstsBeforeInstAux where
"getInstsBeforeInstAux [] ins A = None"
| "getInstsBeforeInstAux ((a,b)#xs) ins A =
    (if a = ins then Some A else getInstsBeforeInstAux xs ins (A@[(a,b)]))"

(* for dominance *)
fun getInstsBeforeInst where
"getInstsBeforeInst S ins = (case findBlockNameByInst S ins of None \<Rightarrow> None
      | Some name \<Rightarrow> (case getBlock S name of None \<Rightarrow> None
                   | Some l \<Rightarrow> getInstsBeforeInstAux l ins []))"

fun getInstsBeforeInstProg where
"getInstsBeforeInstProg (Prog x y z) ins = getInstsBeforeInst z ins"

fun phiEliminateAux where
"phiEliminateAux [] x = []"
| "phiEliminateAux ((a,b)#xs) x= (if b = x then [(a,b)] else phiEliminateAux xs x)"

fun phiEliminate where
"phiEliminate [] label = []"
| "phiEliminate ((x,Phi a bl)#xs) label = (x, Phi a (phiEliminateAux bl label))#(phiEliminate xs label)"
| "phiEliminate (x#xs) label = phiEliminate xs label"

fun updateReg where
"updateReg (reg,specReg) currNum n x y =
      (if n \<le> currNum then (reg(x \<mapsto> y), specReg)
           else (reg, specReg((n,x) \<mapsto> y)))"

(* listdifference *)
fun listMinus where
"listMinus [] a = []"
| "listMinus (x#xs) a = (if x = a then listMinus xs a else x#(listMinus xs a))"

(* check if a instruction is available *)
fun isAvailElem where
"isAvailElem (Local x) = False"
| "isAvailElem (ArrayVal xl) = (List.foldl (\<lambda> v x . v \<and> (isAvailElem x)) True xl)"
| "isAvailElem x = True"

fun isAvailInst where
"isAvailInst (Add x y z) = (isAvailElem y \<and> isAvailElem z)"
| "isAvailInst (Sub x y z) = (isAvailElem y \<and> isAvailElem z)"
| "isAvailInst (GEP x y z u v) = (isAvailElem u \<and> (List.foldl (\<lambda> b (s,t) . b \<and> isAvailElem t) True v))"
| "isAvailInst (ExtractValue x y z) = isAvailElem y"
| "isAvailInst (InsertValue x y z u) = (isAvailElem y \<and> isAvailElem z)"
| "isAvailInst (Phi x y) = (List.foldl (\<lambda> t (a,b) . t \<and> isAvailElem a) True y)"
| "isAvailInst (Malloc x y) = True"
| "isAvailInst (Bitcast x y z) = isAvailElem y"
| "isAvailInst (Inttoptr x y z) = isAvailElem y"
| "isAvailInst (Ptrtoint x y z) = isAvailElem y"
| "isAvailInst (Fence x) = True"
| "isAvailInst (Store x y z u) = (isAvailElem y \<and> isAvailElem z)"
| "isAvailInst (AtomicStore x y z u v) = (isAvailElem y \<and> isAvailElem z)"
| "isAvailInst (Load x y z u) = isAvailElem z"
| "isAvailInst (AtomicLoad x y z u v) = isAvailElem z"
| "isAvailInst (CreateThread x y z) = (List.foldl (\<lambda> t a . t \<and> isAvailElem a) True z)"
| "isAvailInst (ThreadJoin x y) = isAvailElem y"
| "isAvailInst (Call x y z) = (List.foldl (\<lambda> t a . t \<and> isAvailElem a) True z)"
| "isAvailInst (Icmp x y z u) = (isAvailElem z \<and> isAvailElem u)"
| "isAvailInst (Br x y z) = isAvailElem x"
| "isAvailInst (UnBr x) = True"
| "isAvailInst (Return x) = isAvailElem x"
| "isAvailInst (Other x) = True"

(* a fixed operation must be sent to the CPU only if it is in the least opstion (start) *)
fun isFixedOp where
"isFixedOp (Malloc x y) = True"
| "isFixedOp (Fence x) = True"
| "isFixedOp (CreateThread x y z) = True"
| "isFixedOp (ThreadJoin x y) = True"
| "isFixedOp (Call x y z) = True"
| "isFixedOp (Br x y z) = True"
| "isFixedOp (UnBr x) = True"
| "isFixedOp (Return x) = True"
| "isFixedOp x = False"

fun isMemoryOp where
"isMemoryOp (Fence x) = True"
| "isMemoryOp (Store x y z u) = True"
| "isMemoryOp (AtomicStore x y z u v) = True"
| "isMemoryOp (Load x y z u) = True"
| "isMemoryOp (AtomicLoad x y z u v) = True"
| "isMemoryOp x = False"

(* helpers and function to define single cpu instruction semantics *)
fun bitsToInt :: "bit list \<Rightarrow> nat \<Rightarrow> int option"  where
"bitsToInt [] n = Some 0"
| "bitsToInt (x#xs) n = (if x = One then
           ( case bitsToInt xs (n - 1) of None \<Rightarrow> None | Some x \<Rightarrow> Some ((2 ^ (n -1)) + x))
                              else if x = Zero then bitsToInt xs (n - 1)
                              else None)"

fun bitsToIntSign :: "bit list \<Rightarrow> int option"  where
"bitsToIntSign [] = None"
| "bitsToIntSign (x#xs) = (case x of One \<Rightarrow> (case bitsToInt xs (length xs) of None \<Rightarrow> None
                         | Some v \<Rightarrow> Some (0 - v))
                                | Zero \<Rightarrow> bitsToInt xs (length xs)
                                | Undef \<Rightarrow> None)"

fun intToBits where
"intToBits x 0 = []"
| "intToBits x (Suc n) = (if x \<le> 0 then ((intToBits x n)@[Zero])
         else (intToBits (x div 2) n)@[if x mod 2 = 0 then Zero else One])"

fun intToIntElem where
"intToIntElem x n = IntVal (intToBits x n) (IntType n) None None"

fun compareMemRange where
"compareMemRange (Some (a,b)) (Some (a',b')) = (if a = a' \<and> b = b' then Some (a,b) else None)"
| "compareMemRange (Some (a,b)) None = (Some (a,b))"
| "compareMemRange None (Some (a,b)) = (Some (a,b))"
| "compareMemRange None None = None"

fun dealWithIcmp where
"dealWithIcmp Eq a b = (if a = b then One else Zero)"
| "dealWithIcmp Ne a b = (if a \<noteq> b then One else Zero)"
| "dealWithIcmp Lt a b = (if a < b then One else Zero)"
| "dealWithIcmp Leq a b = (if a \<le> b then One else Zero)"
| "dealWithIcmp Gt a b = (if a > b then One else Zero)"
| "dealWithIcmp Geq a b = (if a \<ge> b then One else Zero)"

(* computing GEP *)
fun dealWithInRange where
"dealWithInRange None u newleft newright = (if u then Some (newleft,newright) else None)"
| "dealWithInRange (Some (left,right)) u newleft newright
            = (if u then (if newleft \<ge> right then Some (0,0) else if newright \<le> left then Some (0,0)
                else if newleft < right \<and> newleft \<ge> left \<and> newright > left \<and> newright \<le> right
                       then Some (newleft,newright)
                else if newleft < left \<and>  newright > left \<and> newright \<le> right then Some (left, newright)
                else if newleft < right \<and> newleft \<ge> left \<and> newright > right then Some (newleft, right)
                else Some (left,right)) else Some (left,right))"

fun computeGEPAux :: "atype \<Rightarrow> int \<Rightarrow> (bool \<times> 'b element) list
                     \<Rightarrow> (nat \<times> nat) option
             \<Rightarrow> (nat \<times> atype \<times> 'b element option \<times> (nat \<times> nat) option) option" where
  "computeGEPAux a x [] rans = (if x < 0 then None else Some (nat x, a, None, rans))"
| "computeGEPAux (PointerType a) x ((u,v)#l) rans = None"
| "computeGEPAux (IntType a) x ((u,v)#l) rans = None"
| "computeGEPAux (ArrayType n a) x ((u,v)#l) rans =
      (case v of GlobalUndef \<Rightarrow> Some (0, (ArrayType n a), Some GlobalUndef, None)
        |  Poison \<Rightarrow> Some (0,(ArrayType n a), Some Poison,None)
        | IntVal bits at rans1 inrange \<Rightarrow> (case bitsToIntSign bits of None \<Rightarrow> None
                 | Some val \<Rightarrow> (computeGEPAux a (x + (val * (int (sizeof a)))) l
           (dealWithInRange rans u (nat (x + (val * (int (sizeof a)))))
                         (nat (x + ((val + 1) * (int (sizeof a)))))))))"

fun computeGEP :: "atype \<Rightarrow> int \<Rightarrow> (bool \<times> 'a element) list \<Rightarrow> (nat \<times> nat) option
             \<Rightarrow> (nat \<times> atype \<times> 'a element option \<times> (nat \<times> nat) option) option" where
"computeGEP a x [] rans = (if x < 0 then None else Some (nat x, a, None, rans))"
| "computeGEP (PointerType a) x ((u,v)#l) rans =
      (case v of GlobalUndef \<Rightarrow> Some (0, (PointerType a), Some GlobalUndef, None)
        |  Poison \<Rightarrow> Some (0,(PointerType a),Some Poison,None)
        | IntVal bits at rans1 inrange \<Rightarrow> (case bitsToIntSign bits of None \<Rightarrow> None
                 | Some val \<Rightarrow> (computeGEPAux a (x + (val * (int (sizeof a)))) l
            (dealWithInRange rans u (nat (x + (val * (int (sizeof a))))) (nat (x + ((val + 1) * (int (sizeof a)))))))))"
| "computeGEP (IntType a) x ((u,v)#l) rans = None"
| "computeGEP (ArrayType n a) x ((u,v)#l) rans = None"

fun computeGEPInBoundAux :: "atype \<Rightarrow> int \<Rightarrow> nat \<times> nat
                     \<Rightarrow> (bool \<times> 'b element) list
                        \<Rightarrow> (nat \<times> nat) option \<Rightarrow> (nat \<times> atype \<times> 'b element option \<times> (nat \<times> nat) option) option" where
  "computeGEPInBoundAux a x (left,right) [] rans = 
        (if x < 0 then None else if nat x \<ge> left \<and> nat x \<le> right then Some (nat x, a, None, rans)
                   else Some (0, a, Some Poison, None))"
| "computeGEPInBoundAux (PointerType a) x rag ((u,v)#l) rans = None"
| "computeGEPInBoundAux (IntType a) x rag ((u,v)#l) rans = None"
| "computeGEPInBoundAux (ArrayType n a) x (left,right) ((u,v)#l) rans =
    (if nat x \<ge> left \<and> nat x \<le> right then
      (case v of GlobalUndef \<Rightarrow> Some (0, (ArrayType n a), Some GlobalUndef, None)
        |  Poison \<Rightarrow> Some (0,(ArrayType n a), Some Poison,None)
        | IntVal bits at rans1 inrange \<Rightarrow> (case bitsToIntSign bits of None \<Rightarrow> None
                 | Some val \<Rightarrow> (computeGEPInBoundAux a (x + (val * (int (sizeof a)))) (left,right) l
           (dealWithInRange rans u (nat (x + (val * (int (sizeof a)))))
                      (nat (x + ((val + 1) * (int (sizeof a)))))))))
        else Some (0, (ArrayType n a), Some Poison, None))"

fun computeGEPInBound :: "atype \<Rightarrow> int \<Rightarrow> nat \<times> nat
                     \<Rightarrow> (bool \<times> 'b element) list
                        \<Rightarrow> (nat \<times> nat) option \<Rightarrow> (nat \<times> atype \<times> 'b element option \<times> (nat \<times> nat) option) option" where
"computeGEPInBound a x (left,right) [] rans =
    (if nat x \<ge> left \<and> nat x \<le> right then (if x < 0 then None else Some (nat x, a, None, rans))
                else Some (0, a, Some Poison, None))"
| "computeGEPInBound (PointerType a) x (left,right) ((u,v)#l) rans =
    (if nat x \<ge> left \<and> nat x \<le> right then
      (case v of GlobalUndef \<Rightarrow> Some (0, (PointerType a), Some GlobalUndef, None)
        |  Poison \<Rightarrow> Some (0,(PointerType a),Some Poison,None)
        | IntVal bits at rans1 inrange \<Rightarrow> (case bitsToIntSign bits of None \<Rightarrow> None
                 | Some val \<Rightarrow> (computeGEPInBound a (x + (val * (int (sizeof a)))) (left,right) l
             (dealWithInRange rans u (nat (x + (val * (int (sizeof a)))))
                   (nat (x + ((val + 1) * (int (sizeof a)))))))))
         else Some (0, (PointerType a), Some Poison, None))"
| "computeGEPInBound (IntType a) x rag ((u,v)#l) rans = None"
| "computeGEPInBound (ArrayType n a) x rag ((u,v)#l) rans = None"

(* semantics meaning for cpu only instructions *)
fun singleInstSolve :: "('id, 'a) stmt \<Rightarrow> ('id \<times> 'id element) option"  where
"singleInstSolve (Add x (IntVal a (IntType b) c d) (IntVal a' (IntType b') c' d'))
        = (if b = b' then (case (bitsToInt a b) of None \<Rightarrow> Some (x,GlobalUndef)
              | Some ax \<Rightarrow> (case  (bitsToInt a' b) of None \<Rightarrow> Some (x,GlobalUndef)
               | Some ay \<Rightarrow> Some (x,
            (IntVal (intToBits (ax + ay) b) (IntType b)
                      (compareMemRange c c') (compareMemRange d d'))))) else None)"
| "singleInstSolve (Sub x (IntVal a (IntType b) c d) (IntVal a' (IntType b') c' d'))
        = (if b = b' then (case (bitsToInt a b) of None \<Rightarrow> Some (x,GlobalUndef)
              | Some ax \<Rightarrow> (case  (bitsToInt a' b) of None \<Rightarrow> Some (x,GlobalUndef)
               | Some ay \<Rightarrow> if ax < ay then Some (x,
            (IntVal (intToBits (ax - ay + (2 ^ b)) b) (IntType b)
                      (compareMemRange c c') (compareMemRange d d')))
           else Some (x,
            (IntVal (intToBits (ax - ay) b) (IntType b)
                      (compareMemRange c c') (compareMemRange d d'))))) else None)"
| "singleInstSolve (Phi x ((a,b)#xs)) = Some (x,a)"
| "singleInstSolve (GEP x True t (Pointer bits at None inrange) l) = Some (x,Poison)"
| "singleInstSolve (GEP x True t (Pointer bits at (Some rag) inrange) l)
        = (case bitsToInt bits pointerSize of None \<Rightarrow> None
             | Some v \<Rightarrow> (case computeGEPInBound t v rag l inrange of None \<Rightarrow> None
                             | Some (val, newt,Some Poison, reran) \<Rightarrow> Some (x, Poison)
                             | Some (val, newt, Some GlobalUndef, reran) \<Rightarrow> Some (x, GlobalUndef)
                             | Some (val, newt, None, None)
                                  \<Rightarrow> Some (x, Pointer (intToBits val pointerSize) (PointerType newt) (Some rag) None)
                             | Some (val, newt, None, inran) \<Rightarrow>
                                 Some (x, Pointer (intToBits val pointerSize) (PointerType newt)
                                      (Some rag) inran)
                             | _ \<Rightarrow> None))"
| "singleInstSolve (GEP x False t (Pointer bits at rag inrange) l)
        = (case bitsToInt bits pointerSize of None \<Rightarrow> None
             | Some v \<Rightarrow> (case computeGEP t v l inrange of None \<Rightarrow> None
                             | Some (val, newt,Some Poison, reran) \<Rightarrow> Some (x, Poison)
                             | Some (val, newt, Some GlobalUndef, reran) \<Rightarrow> Some (x, GlobalUndef)
                             | Some (val, newt, None, None)
                                  \<Rightarrow> Some (x, Pointer (intToBits val pointerSize) (PointerType newt) rag None)
                             | Some (val, newt, None, inran) \<Rightarrow>
                                 Some (x, Pointer (intToBits val pointerSize) (PointerType newt)
                                      rag inran)
                             | _ \<Rightarrow> None))"
| "singleInstSolve (Icmp a x (IntVal bl at rans inran) (IntVal bl' at' rans' inran')) =
    (if at = at' then (case bitsToInt bl (bitsof at) of None \<Rightarrow> Some (a,GlobalUndef)
                           | Some v1 \<Rightarrow> (case bitsToInt bl' (bitsof at) of None \<Rightarrow> Some (a,GlobalUndef)
                            | Some v2 \<Rightarrow> Some (a,IntVal [(dealWithIcmp x v1 v2)] (IntType 1) None None)))
     else None)"
| "singleInstSolve (Icmp a x (Pointer bl at rans inran) (Pointer bl' at' rans' inran')) =
    (if at = at' then (case bitsToInt bl (bitsof at) of None \<Rightarrow> Some (a,GlobalUndef)
                           | Some v1 \<Rightarrow> (case bitsToInt bl' (sizeof at) of None \<Rightarrow> Some (a,GlobalUndef)
                            | Some v2 \<Rightarrow> Some (a,IntVal [(dealWithIcmp x v1 v2)] (IntType 1) None None)))
     else None)"
| "singleInstSolve x = None"

fun hasDependMem where
"hasDependMem env a = True"

(* tid,count,bNum,bName,prog: control unit and define max spec count*)
fun getTid where
"getTid (tid, count,bNum,bName,prog, toExecutes) = tid"

fun getCount where
"getCount (tid, count,bNum,bName,prog,toExecutes) = count"

fun setCount where
"setCount (tid, count,bNum,bName,prog,toExecutes) count' = (tid, count',bNum,bName,prog,toExecutes)"

fun getBlockNum where
"getBlockNum (tid, count,bNum,bName,prog,toExecutes) = bNum"

fun getBlockName where
"getBlockName (tid, count,bNum,bName,prog,toExecutes) = bName"

fun setBlockPair where
"setBlockPair (tid, count,bNum,bName,prog,toExecutes) a b = (tid, count,a,b,prog,toExecutes)"

fun getProg where
"getProg (tid,count,bNum,bName,prog,toExecutes) = prog"

fun getExecutes where
"getExecutes (tid,count,bNum,bName,prog,toExecutes) = toExecutes"

fun insertExecutes where
"insertExecutes a (tid,count,bNum,bName,prog,toExecutes) = (tid,count,bNum,bName,prog,insert a toExecutes)"

(* spec control cell *)
fun getDDG where
"getDDG (firstDDGBlock, DDG, choice, anti, nameMap) = DDG"

fun genDDGAux where
"genDDGAux [] = []"
| "genDDGAux ((a, Fence s)#xs) = (MemProto a (AFence s) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, Store t x y u)#xs) = (MemProto a (ToWrite y None u) 0 (sizeof t))#(genDDGAux xs)"
| "genDDGAux ((a, AtomicStore t x y z u)#xs) = (MemProto a (ToWrite y (Some z) u) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, Load x t y u)#xs) = (MemProto a (ToRead y None u) 0 (sizeof t))#(genDDGAux xs)"
| "genDDGAux ((a, AtomicLoad x t y z u)#xs) = (MemProto a (ToRead y (Some z) u) 0 (sizeof t))#(genDDGAux xs)"
| "genDDGAux ((a, CreateThread x y z)#xs) = (MemProto a (CallFence) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, Call x y z)#xs) = (MemProto a (CallFence) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, ThreadJoin x y)#xs) = (MemProto a (CallFence) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, Malloc x y)#xs) = (MemProto a (CallFence) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, Br x y z)#xs) = (MemProto a (ControlFence) 0 1)#(genDDGAux xs)"
| "genDDGAux ((a, x)#xs) = (genDDGAux xs)"

fun genDDG where
"genDDG DDG bn l = DDG(bn \<mapsto> genDDGAux l)"

fun setDDGAux where
"setDDGAux [] a = []"
| "setDDGAux ((MemProto x y u v)#xs) a =
      (if a = x then (MemProto x y (u + 1) v)#xs else (MemProto x y u v)#(setDDGAux xs a))"

fun setDDG where
"setDDG (firstDDGBlock, DDG, choice, anti, nameMap) bn a
      = (case DDG bn of None \<Rightarrow> (firstDDGBlock, DDG, choice, anti, nameMap)
             | Some l \<Rightarrow> (firstDDGBlock, DDG(bn \<mapsto> setDDGAux l a), choice, anti, nameMap))"

fun turnTrueAux where
"turnTrueAux [] a = []"
| "turnTrueAux ((MemProto x y u v)#l) a =
     (if a = x then ((MemProto x y v v)#l) else (MemProto x y u v)#(turnTrueAux l a))"

fun turnTrue where
"turnTrue (firstDDGBlock, DDG, choice, anti, nameMap) bn a =
       (case DDG bn of None \<Rightarrow> (firstDDGBlock, DDG, choice, anti, nameMap)
             | Some l \<Rightarrow> (firstDDGBlock, DDG(bn \<mapsto> turnTrueAux l a), choice, anti, nameMap))"



fun isAllFinished where
"isAllFinished [] = True"
| "isAllFinished ((MemProto a b c d)#xs) = (if c = d then isAllFinished xs else False)"

fun getChoice where
"getChoice (firstDDGBlock, DDG, choice, anti, nameMap) = choice"

fun updateSpecNoChoice where
"updateSpecNoChoice (firstDDGBlock, DDG, choice, anti, nameMap) bn x bl =
      (firstDDGBlock, genDDG DDG bn bl, choice, anti, nameMap(bn \<mapsto> x))"

fun updateSpecChoice where
"updateSpecChoice (firstDDGBlock, DDG, choice, anti, nameMap) bn n x bl =
    (case choice bn of None \<Rightarrow> (firstDDGBlock, genDDG DDG n bl, choice(bn \<mapsto> {n}), anti(n \<mapsto> bn), nameMap(n \<mapsto> x))
             | Some S \<Rightarrow> (firstDDGBlock, genDDG DDG n bl, choice(bn \<mapsto> (insert n S)), anti(n \<mapsto> bn), nameMap(n \<mapsto> x)))"

fun getAnti where
"getAnti (firstDDGBlock, DDG, choice, anti, nameMap) = anti"

fun getNameMap where
"getNameMap (firstDDGBlock, DDG, choice, anti, nameMap) = nameMap"

fun delEntryNameMap where
"delEntryNameMap (firstDDGBlock, DDG, choice, anti, nameMap) a
    = (firstDDGBlock, DDG, choice, anti, restrict_map nameMap (dom nameMap - {a}))"

(* merge range or inrange flags *)
fun mergeRange where
"mergeRange None None = None"
| "mergeRange (Some (a,b)) None = Some (a,b)"
| "mergeRange None (Some (a,b)) = Some (a,b)"
| "mergeRange (Some (a,b)) (Some (c,d)) = (if a = c \<and> b = d then Some (a,b) else None)"

(* partition value into a list of bytes *)
fun countBits where
"countBits 0 l r = (l, r)"
| "countBits (Suc n) [] r = countBits n [] (Undef#r)"
| "countBits (Suc n) (x#xs) r = (countBits n xs (x#r))"

definition countEight where
"countEight l = (case countBits byteSize (rev l) [] of (x,y) \<Rightarrow> (rev x,y))"

primrec toBytesAux where
"toBytesAux 0 l rans inrans = []"
| "toBytesAux (Suc n) l rans inrans =
      (case countEight l of (x,y) \<Rightarrow> (toBytesAux n x rans inrans)@[(Byte (Some y) rans inrans)])"

primrec copiesof where
"copiesof 0 a = []"
| "copiesof (Suc n) a = a#(copiesof n a)"

fun collectArrayBits where
"collectArrayBits at (IntVal l pt rans inrans) accl accran accinran
       = Some (accl@l,compareMemRange rans accran, compareMemRange inrans accinran)"
| "collectArrayBits at (Pointer l pt rans inrans) accl accran accinran
       = Some (accl@l,compareMemRange rans accran, compareMemRange inrans accinran)"
| "collectArrayBits at (GlobalUndef) accl accran accinran
       = Some (accl@(copiesof (bitsof at) Undef),accran, accinran)"
| "collectArrayBits at Poison accl accran accinran = None"
| "collectArrayBits at (Local x) accl accran accinran = None"
| "collectArrayBits at (ArrayVal []) accl accran accinran = Some (accl,accran,accinran)"
| "collectArrayBits (ArrayType n at) (ArrayVal (x#xs)) accl accran accinran =
        (case collectArrayBits at x accl accran accinran of None \<Rightarrow> None
            | Some (newl,newran,newinran) \<Rightarrow>
                 collectArrayBits (ArrayType n at) (ArrayVal xs) newl newran newinran)"
| "collectArrayBits x y accl accran accinran = None"

primrec toBytes where
"toBytes at (IntVal l pt rans inrans) = Some (toBytesAux (sizeof at) l rans inrans)"
| "toBytes at (Pointer l pt rans inrans) = Some (toBytesAux (sizeof at) l rans inrans)"
| "toBytes at GlobalUndef = Some (toBytesAux (sizeof at) (copiesof (bitsof at) Undef) None None)"
| "toBytes at Poison = Some (copiesof (sizeof at) (Byte None None None))"
| "toBytes at (Local x) = None"
| "toBytes at (ArrayVal xl) = (case collectArrayBits at (ArrayVal xl) [] None None
         of None \<Rightarrow> Some (copiesof (sizeof at) (Byte None None None))
           | Some (newl,newran,newinran) \<Rightarrow> Some (toBytesAux (sizeof at) newl newran newinran))"

(* functions for turning a list of bytes to a typed value *)
fun mergeAllRanges where
"mergeAllRanges [] = (None,None)"
| "mergeAllRanges ((Byte x y z)#xs) =
  (case mergeAllRanges xs of (a,b) \<Rightarrow> (mergeRange y a, mergeRange z b))"

fun toBits where
"toBits [] = Some []"
| "toBits ((Byte None y z)#xs) = None"
| "toBits ((Byte (Some l) y z)#xs) = (case toBits xs of None \<Rightarrow> None | Some l1 \<Rightarrow> Some (l@l1))"

definition toInt where
"toInt at bs ran1 ran2 = (case countBits (bitsof at) (rev bs) [] of (l,r)
        \<Rightarrow> if Undef \<in> set r then (rev l, GlobalUndef) else (rev l, IntVal r at ran1 ran2))"

definition toPointer where
"toPointer at bs ran1 ran2 = (case countBits (bitsof at) (rev bs) [] of (l,r)
        \<Rightarrow> if Undef \<in> set r then (rev l, GlobalUndef) else (rev l, Pointer r at ran1 ran2))"

fun toTypes and toArray where
"toTypes 0 at bs ran1 ran2 result = Some (bs,result)"
| "toTypes (Suc n) (IntType x) bs ran1 ran2 result =
           (case toInt (IntType x) bs ran1 ran2 of (r, v)
                \<Rightarrow> toTypes n (IntType x) r ran1 ran2 (result@[v]))"
| "toTypes (Suc n) (PointerType x) bs ran1 ran2 result =
           (case toPointer (PointerType x) bs ran1 ran2 of (r,v)
                \<Rightarrow> toTypes n (PointerType x) r ran1 ran2 (result@[v]))"
| "toTypes (Suc n) (ArrayType m x) bs ran1 ran2 result =
           (case toArray (ArrayType m x) bs ran1 ran2 of Some (r,v)
                \<Rightarrow> toTypes n (ArrayType m x) r ran1 ran2 (result@[v]))"
| "toArray (ArrayType n at) bs ran1 ran2 = 
      (case toTypes n at bs ran1 ran2 [] of None \<Rightarrow> None
                   | Some (r,result) \<Rightarrow> Some (r,ArrayVal result))"
| "toArray a bs ran1 ran2 = None"

fun toValue where
"toValue (asize,IntType n,bytes) = (case toBits bytes of None \<Rightarrow> Poison
             | Some l \<Rightarrow>
           (case mergeAllRanges bytes of (ran1,ran2) \<Rightarrow> 
                 (case toInt (IntType n) l ran1 ran2 of (r,v) \<Rightarrow> if r = [] then v else Poison)))"
| "toValue (asize,PointerType n,bytes) = (case toBits bytes of None \<Rightarrow> Poison
             | Some l \<Rightarrow>
           (case mergeAllRanges bytes of (ran1,ran2) \<Rightarrow> 
                 (case toPointer (PointerType n) l ran1 ran2 of (r,v) \<Rightarrow> if r = [] then v else Poison)))"
| "toValue (asize,ArrayType n at,bytes) = (case toBits bytes of None \<Rightarrow> Poison
             | Some l \<Rightarrow>
           (case mergeAllRanges bytes of (ran1,ran2) \<Rightarrow> 
                 (case toArray (ArrayType n at) l ran1 ran2 of None \<Rightarrow> Poison
                         | Some (r,v) \<Rightarrow> if r = [] then v else Poison)))"

fun removeIndices where
"removeIndices [] = []"
| "removeIndices ((a,b)#xs) = b#(removeIndices xs)"


(* generate a list of writes/reads for non-atomic store/load *)
primrec genWrites where
"genWrites bn inum n base [] = []"
| "genWrites bn inum n base (x#xs) = (bn,inum,Write n base [x] Monotonic)
                                               #(genWrites bn inum n (base + 1) xs)"

primrec genReads where
"genReads bn inum n base pos 0 = []"
| "genReads bn inum n base pos (Suc x) = (bn,inum,Read base pos n 1 Monotonic)
                                                  #(genReads bn inum n (base+1) (pos + 1) x)"

(* a function to compare a pair of blocknum,inst-num *)
fun lessInstPair where
"lessInstPair (a,b) (c,d) = (a < c \<or> (a = c \<and>  b < d))"

(* assuming ssa and dominance, so every block has only one instance of a variable, and 
  if in the same block, a use of the variable happens, it must have been assigned in this block or previous, 
   it is impossible to have a name used and then assigned in a block. 
  updateVar find the x in specReg with the largest block num < n but if the block number is less than the curr-block
  the function returns None, because it means that the value of the variable is in the register. *)
(* fun findInSpecReg where
"findInSpecReg specReg antiMap currs n x = (if n > currs then
    (case specReg (n,x) of None
          \<Rightarrow> (case antiMap n of None \<Rightarrow> None | Some n' \<Rightarrow> findInSpecReg specReg antiMap currs n' x)
          | Some v \<Rightarrow> Some v) else None)"

TODO: input the typed program property.
*)
locale executionModel =
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
                  "\<forall> specReg antiMap currNum n x . n \<le> currNum
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
                                                findPathToFather antiMap a b l = Some (a#l)"
         and findPathToFatherRule2 :
                     "\<forall> antiMap a b c l . a \<noteq> b \<and> (antiMap a = Some c) \<longrightarrow>
                              findPathToFather antiMap a b l = (findPathToFather antiMap c b (a#l))"
         and findPathToFatherRule3 :
                     "\<forall> antiMap a b l . a \<noteq> b \<and> (antiMap a = None) \<longrightarrow> findPathToFather antiMap a b l = None"
begin

fun removeEntryByBlockNum where
"removeEntryByBlockNum specReg bn
       = restrict_map specReg (dom specReg - {x . \<exists> a . (bn, a) \<in> dom specReg \<and> x = (bn,a)})"

fun removeEntryBySetNums where
"removeEntryBySetNums specReg [] = specReg"
| "removeEntryBySetNums specReg (x#xs) = removeEntryBySetNums (removeEntryByBlockNum specReg x) xs"

fun moveSpecRegToReg where
"moveSpecRegToReg (reg, specReg) bn =
        (map_add reg (rewriteMap (restrict_map specReg {x . \<exists> a . (bn, a) \<in> dom specReg \<and> x = (bn,a)})),
          removeEntryByBlockNum specReg bn)"

(* remove all root and children entries in specreg based on a root blockNum *)
fun removeEntriesInSpecReg where
"removeEntriesInSpecReg (reg,specReg) choice bn =
        (case getChildren choice bn of S \<Rightarrow> (reg, removeEntryBySetNums specReg (sorted_list_of_set S)))"

fun removeAllEntriesInSpecReg where
"removeAllEntriesInSpecReg (reg,specReg) choice [] = (reg,specReg)"
| "removeAllEntriesInSpecReg (reg,specReg) choice (x#xs)
         = removeAllEntriesInSpecReg (removeEntriesInSpecReg (reg,specReg) choice x) choice xs"

definition removeAllEntriesForAllOtherBranches where
"removeAllEntriesForAllOtherBranches a choice S = removeAllEntriesInSpecReg a choice (sorted_list_of_set S)"


(* remove all root and children entries in memCell based on a root blockNum *)
fun removeEntriesInMemCell where
"removeEntriesInMemCell (cacheN,toCommit, readBack) choice bn =
        (case getChildren choice bn of S \<Rightarrow> (cacheN, toCommit, removeEntryBySetNums readBack (sorted_list_of_set S)))"

fun removeAllEntriesInMemCell where
"removeAllEntriesInMemCell (cacheN,toCommit, readBack) choice [] = (cacheN, toCommit, readBack)"
| "removeAllEntriesInMemCell (cacheN,toCommit, readBack) choice (x#xs)
         = removeAllEntriesInMemCell (removeEntriesInMemCell (cacheN,toCommit, readBack) choice x) choice xs"

definition removeAllEntriesForAllOtherMemcell where
"removeAllEntriesForAllOtherMemcell a choice S = removeAllEntriesInMemCell a choice (sorted_list_of_set S)"

(* remove all toExecute blocks that guesses wrong in a branch. *)
fun getChildrenFromAllRoots where
"getChildrenFromAllRoots choice [] = {}"
| "getChildrenFromAllRoots choice (x#xs) = (getChildren choice x) \<union> (getChildrenFromAllRoots choice xs)"

fun removeAllExecutesFun where
"removeAllExecutesFun [] S = []"
| "removeAllExecutesFun ((a,b)#xs) S =
        (if a \<in> S then removeAllExecutesFun xs S else (a,b)#(removeAllExecutesFun xs S))"

definition removeAllExecutes where
"removeAllExecutes toExecutes choice rest =
                    removeAllExecutesFun toExecutes
                          (getChildrenFromAllRoots choice (sorted_list_of_set rest))"

fun removeAllExecutesPair where
"removeAllExecutesPair (cacheN,toCommit,readBack) choice rest =
                 (cacheN,removeAllExecutes toCommit choice rest, readBack)"

(* control includes thread-ID, blockCount, counter for variables, current block num, current block name, program
   specControl includes firstDDGBlock, spec choice map (father to children), spec anti-map (child to father)
                 spec block-name-map (block num to block name)

   firstDDGBlock is a block number that must be equal or older to the currblock number.
   It represents the oldest block number that contains the oldest memory op that has not yet been committed.
 *)

fun updateElem where
"updateElem (reg,specReg) antiMap currNum n (Local x) = 
   (case findInSpecReg specReg antiMap currNum n x of None
        \<Rightarrow> (case reg x of None \<Rightarrow> Local x | Some y \<Rightarrow> y) | Some y \<Rightarrow> y)"
| "updateElem (reg,specReg) antiMap currNum n x = x"

fun updateInst where
"updateInst env antiMap currNum n (Add x y z)
         = Add x (updateElem env antiMap currNum n y) (updateElem env antiMap currNum n z)"
| "updateInst env antiMap currNum n (Sub x y z)
         = Sub x (updateElem env antiMap currNum n y) (updateElem env antiMap currNum n z)"
| "updateInst env antiMap currNum n (GEP x y z u v)
          = GEP x y z (updateElem env antiMap currNum n u)
                (List.map (\<lambda> (a,b) . (a, (updateElem env antiMap currNum n b))) v)"
| "updateInst env antiMap currNum n (ExtractValue x y z)
          = ExtractValue x (updateElem env antiMap currNum n y) z"
| "updateInst env antiMap currNum n (InsertValue x y z u)
           = InsertValue x (updateElem env antiMap currNum n y) (updateElem env antiMap currNum n z) u"
| "updateInst env antiMap currNum n (Phi x y)
            = Phi x (List.map (\<lambda> (a,b) . ((updateElem env antiMap currNum n a), b)) y)"
| "updateInst env antiMap currNum n (Malloc x y) = Malloc x y"
| "updateInst env antiMap currNum n (Bitcast x y z)
             = Bitcast x (updateElem env antiMap currNum n y) z"
| "updateInst env antiMap currNum n (Inttoptr x y z)
            = Inttoptr x (updateElem env antiMap currNum n y) z"
| "updateInst env antiMap currNum n (Ptrtoint x y z)
                   = Ptrtoint x (updateElem env antiMap currNum n y) z"
| "updateInst env antiMap currNum n (Fence x) = Fence x"
| "updateInst env antiMap currNum n (Store x y z u)
               = Store x (updateElem env antiMap currNum n y) (updateElem env antiMap currNum n z) u"
| "updateInst env antiMap currNum n (AtomicStore x y z u v)
            = AtomicStore x (updateElem env antiMap currNum n y) (updateElem env antiMap currNum n z) u v"
| "updateInst env antiMap currNum n (Load x y z u)
                = Load x y (updateElem env antiMap currNum n z) u"
| "updateInst env antiMap currNum n (AtomicLoad x y z u v)
                    = AtomicLoad x y (updateElem env antiMap currNum n z) u v"
| "updateInst env antiMap currNum n (CreateThread x y z)
              = CreateThread x y (List.map (\<lambda> a . (updateElem env antiMap currNum n a)) z)"
| "updateInst env antiMap currNum n (ThreadJoin x y)
              = ThreadJoin x (updateElem env antiMap currNum n y)"
| "updateInst env antiMap currNum n (Call x y z)
              = Call x y (List.map (\<lambda> a . (updateElem env antiMap currNum n a)) z)"
| "updateInst env antiMap currNum n (Icmp x y z u)
                  = Icmp x y (updateElem env antiMap currNum n z) (updateElem env antiMap currNum n u)"
| "updateInst env antiMap currNum n (Br x y z)
                 = Br (updateElem env antiMap currNum n x) y z"
| "updateInst env antiMap currNum n (UnBr x) = UnBr x"
| "updateInst env antiMap currNum n (Return x) = Return (updateElem env antiMap currNum n x)"
| "updateInst env antiMap currNum n (Other x) = Other x"

fun updateAllInsts where
"updateAllInsts env antiMap currNum [] = []"
| "updateAllInsts env antiMap currNum ((x,y,z)#xs) = 
        (x,y, updateInst env antiMap currNum x z)#(updateAllInsts env antiMap currNum xs)"

(* a function to update variable in MemProtos to actual pointer *)
fun updateDDGElem where
"updateDDGElem env antiMap currNum bn [] = []"
| "updateDDGElem env antiMap currNum bn ((MemProto x (ToRead p ord vol) u v)#xs) = 
       ((MemProto x (ToRead (updateElem env antiMap currNum bn p) ord vol) u v)
                      #(updateDDGElem env antiMap currNum bn xs))"
| "updateDDGElem env antiMap currNum bn ((MemProto x (ToWrite p ord vol) u v)#xs) = 
       ((MemProto x (ToWrite (updateElem env antiMap currNum bn p) ord vol) u v)
                      #(updateDDGElem env antiMap currNum bn xs))"
| "updateDDGElem env antiMap currNum bn ((MemProto x a u v)#xs) = 
       ((MemProto x a u v) #(updateDDGElem env antiMap currNum bn xs))"

fun updateDDGAux where
"updateDDGAux env antiMap currNum DDG [] = DDG"
| "updateDDGAux env antiMap currNum DDG (bn#bns) =
    updateDDGAux env antiMap currNum (DDG(bn \<mapsto> updateDDGElem env antiMap currNum bn (the (DDG bn)))) bns"

fun updateDDG where
"updateDDG env currNum (firstDDGBlock, DDG, choice, anti, nameMap) =
       (firstDDGBlock, updateDDGAux env anti currNum DDG (sorted_list_of_set (dom DDG)), choice, anti, nameMap)"

(* a function to output a mem execution history from DDG *)
fun getHistoryAux where
"getHistoryAux DDG [] = []"
| "getHistoryAux DDG (x#xs) = (List.map (\<lambda> y . (x,y)) (the (DDG x)))@(getHistoryAux DDG xs)"

fun removeFinishes where
"removeFinishes [] = []"
| "removeFinishes ((bn,MemProto x y u v)#xs) =
         (if u = v then removeFinishes xs else ((bn,MemProto x y u v)#xs))"

fun mergeSingleFence where
"mergeSingleFence  (ToRead x ords y) (AFence Acquire) =
  (if ords = Some Unordered \<or> ords = Some Monotonic
           then Some (ToRead x (Some Acquire) y)
           else None)"
| "mergeSingleFence  (ToRead x ords y) (AFence AcqRel) =
  (if ords = Some Unordered \<or> ords = Some Monotonic
           then Some (ToRead x (Some Acquire) y)
           else None)"
| "mergeSingleFence  (ToRead x ords y) (AFence Seq) =
  (if ords = Some Unordered \<or> ords = Some Monotonic
           then Some (ToRead x (Some Acquire) y)
           else None)"
| "mergeSingleFence (AFence Release) (ToWrite x ords y)  =
  (if ords = Some Unordered \<or> ords = Some Monotonic
           then Some (ToWrite x (Some Release) y)
           else None)"
| "mergeSingleFence (AFence AcqRel) (ToWrite x ords y)  =
  (if ords = Some Unordered \<or> ords = Some Monotonic
           then Some (ToWrite x (Some Release) y)
           else None)"
| "mergeSingleFence (AFence Seq) (ToWrite x ords y)  =
  (if ords = Some Unordered \<or> ords = Some Monotonic
           then Some (ToWrite x (Some Release) y)
           else None)"
| "mergeSingleFence x y = None"

fun findReadInList where
"findReadInList [] = None"
| "findReadInList ((n,MemProto x (ToRead a b c) u v)#xs) =
           Some ((n,MemProto x (ToRead a b c) u v))"
| "findReadInList (x#xs) = findReadInList xs"

fun findReadFromBottom where
"findReadFromBottom x = findReadInList (rev x)"

fun findWriteFromBegin where
"findWriteFromBegin [] = None"
| "findWriteFromBegin ((n,MemProto x (ToWrite a b c) u v)#xs) =
           Some ((n,MemProto x (ToWrite a b c) u v))"
| "findWriteFromBegin (x#xs) = findWriteFromBegin xs"

fun replaceReadWithNew where
"replaceReadWithNew [] (bn,inum) a = []"
| "replaceReadWithNew ((bn,MemProto x y u v)#xs) (bn',inum) a =
          (if bn = bn' \<and> x = inum then (a#xs) else (bn,MemProto x y u v)#(replaceReadWithNew xs (bn',inum) a))"

(* the basic idea of the function is to join a acquire fence with a sequence-before load,
       and change the load's order to at least acquire.
   Then, join a release fence with a sequence-after write, and change the write's order to at least release
    acq_rel and seq_cst fences will do the both.
 *)
fun joinFence where
"joinFence l [] S = l"
| "joinFence l ((n,MemProto x (AFence ord) u v)#xs) S =
       (case findReadFromBottom l of None \<Rightarrow> 
            (case findWriteFromBegin xs of None \<Rightarrow> joinFence (l@[(n,MemProto x (AFence ord) u v)]) xs S
               | Some (bn,MemProto inum (ToWrite a b c) num1 num2) \<Rightarrow> 
                     (case mergeSingleFence (AFence ord) (ToWrite a b c) of None
                                 \<Rightarrow> joinFence (l@[(n,MemProto x (AFence ord) u v)]) xs S
                        | Some inst \<Rightarrow> joinFence (l@[(n,MemProto x (AFence ord) u v)])
                                          xs (S((bn,inum) \<mapsto> (bn,MemProto inum inst num1 num2)))))
          | Some (bn,MemProto inum (ToRead a b c) num1 num2)
                  \<Rightarrow> (case findWriteFromBegin xs of None \<Rightarrow> 
                         (case mergeSingleFence (ToRead a b c) (AFence ord) of None
                                \<Rightarrow> joinFence (l@[(n,MemProto x (AFence ord) u v)]) xs S
                           | Some inst \<Rightarrow> joinFence ((replaceReadWithNew l
                               (bn,inum) (bn,MemProto inum inst num1 num2))
                                      @[(n,MemProto x (AFence ord) u v)]) xs S)
                      | Some (bn',MemProto inum' (ToWrite a' b' c') num1' num2')
                            \<Rightarrow> (case mergeSingleFence (ToRead a b c) (AFence ord) of None
                                \<Rightarrow> (case mergeSingleFence (AFence ord) (ToWrite a' b' c') of None
                                        \<Rightarrow> joinFence (l@[(n,MemProto x (AFence ord) u v)]) xs S
                           | Some inst \<Rightarrow> joinFence (l@[(n,MemProto x (AFence ord) u v)])
                                          xs (S((bn',inum') \<mapsto> (bn',MemProto inum' inst num1' num2'))))
                        | Some inst \<Rightarrow> (case mergeSingleFence (AFence ord) (ToWrite a' b' c') of None
                               \<Rightarrow> joinFence ((replaceReadWithNew l
                                     (bn,inum) (bn,MemProto inum inst num1 num2))
                                      @[(n,MemProto x (AFence ord) u v)]) xs S
                             | Some inst' \<Rightarrow> joinFence ((replaceReadWithNew l
                                     (bn,inum) (bn,MemProto inum inst num1 num2))
                                      @[(n,MemProto x (AFence ord) u v)]) xs
                                 (S((bn',inum') \<mapsto> (bn',MemProto inum' inst' num1' num2')))))))"
| "joinFence l ((bn,MemProto x (ToWrite a b c) u v)#xs) S =
          (case S (bn,x) of None \<Rightarrow> (joinFence (l@[(bn,MemProto x (ToWrite a b c) u v)]) xs S)
              | Some new \<Rightarrow> joinFence (l@[new]) xs S)"                              
| "joinFence l (x#xs) S = joinFence (l@[x]) xs S"

(* after finishing join fence above, we can just remove all fences *)
fun removeFences where
"removeFences [] = []"
| "removeFences ((n, MemProto x (AFence a) u v)#xs) = removeFences xs"
| "removeFences (x#xs) = x#(removeFences xs)"

(* remove last few instructions *)
fun removeFirst where
"removeFirst [] bn inst = []"
| "removeFirst ((n,MemProto x y u v)#xs) bn inst =
          (if \<not> lessInstPair (n,x) (bn,inst) then removeFirst xs bn inst else ((n,MemProto x y u v)#xs))"

(* TODO: add merging for acquire/release fence with previous/later read/write *)

definition getHistory where
"getHistory DDG antiMap child inst root =
    rev (removeFirst (rev (removeFences (joinFence [] (removeFinishes
                            (getHistoryAux DDG (the (findPathToFather antiMap child root [])))) Map.empty))) child inst)"


inductive execute :: "((('b \<times> (nat \<times> nat \<times> memOp) list \<times> (nat \<times> nat \<Rightarrow> ('id \<times> nat \<times> atype \<times> ('c \<times> byte) list) option)) \<times>
        (nat \<times> nat \<times> nat \<times> 'id \<times> ('id, 'a) block list \<times> nat set) \<times>
        (nat \<times> (nat \<Rightarrow> 'id memProto list option) \<times> (nat \<Rightarrow> nat set option) \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> 'id option)) \<times>
        (nat \<times> (nat \<times> ('id, 'a) stmt) list) list \<times>
        (nat \<times> nat \<times> ('id, 'a) stmt) list \<times>
        (('id \<Rightarrow> 'id element option) \<times> (nat \<times> 'id \<Rightarrow> 'id element option)) \<times>
        (nat \<times> nat \<times> ('id, 'a) stmt) option \<times>
        (('b \<times> (nat \<times> nat \<times> memOp) list \<times> (nat \<times> nat \<Rightarrow> ('id \<times> nat \<times> atype \<times> ('c \<times> byte) list) option)) \<times>
         (nat \<times> nat \<times> nat \<times> 'id \<times> ('id, 'a) block list \<times> nat set) \<times>
         (nat \<times> (nat \<Rightarrow> 'id memProto list option) \<times> (nat \<Rightarrow> nat set option) \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> 'id option)) \<times>
         (nat \<times> (nat \<times> ('id, 'a) stmt) list) list \<times>
         (nat \<times> nat \<times> ('id, 'a) stmt) list \<times>
         (('id \<Rightarrow> 'id element option) \<times> (nat \<times> 'id \<Rightarrow> 'id element option)) \<times> nat \<times> nat \<times> 'id) list) set \<times>
       nat \<times> nat set \<times> (nat \<Rightarrow> 'id element option),
       error) state
      \<Rightarrow> ((('b \<times> (nat \<times> nat \<times> memOp) list \<times> (nat \<times> nat \<Rightarrow> ('id \<times> nat \<times> atype \<times> ('c \<times> byte) list) option)) \<times>
           (nat \<times> nat \<times> nat \<times> 'id \<times> ('id, 'a) block list \<times> nat set) \<times>
           (nat \<times> (nat \<Rightarrow> 'id memProto list option) \<times> (nat \<Rightarrow> nat set option) \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> 'id option)) \<times>
           (nat \<times> (nat \<times> ('id, 'a) stmt) list) list \<times>
           (nat \<times> nat \<times> ('id, 'a) stmt) list \<times>
           (('id \<Rightarrow> 'id element option) \<times> (nat \<times> 'id \<Rightarrow> 'id element option)) \<times>
           (nat \<times> nat \<times> ('id, 'a) stmt) option \<times>
           (('b \<times> (nat \<times> nat \<times> memOp) list \<times> (nat \<times> nat \<Rightarrow> ('id \<times> nat \<times> atype \<times> ('c \<times> byte) list) option)) \<times>
            (nat \<times> nat \<times> nat \<times> 'id \<times> ('id, 'a) block list \<times> nat set) \<times>
            (nat \<times> (nat \<Rightarrow> 'id memProto list option) \<times> (nat \<Rightarrow> nat set option) \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> 'id option)) \<times>
            (nat \<times> (nat \<times> ('id, 'a) stmt) list) list \<times>
            (nat \<times> nat \<times> ('id, 'a) stmt) list \<times>
            (('id \<Rightarrow> 'id element option) \<times> (nat \<times> 'id \<Rightarrow> 'id element option)) \<times> nat \<times> nat \<times> 'id) list) set \<times>
          nat \<times> nat set \<times> (nat \<Rightarrow> 'id element option),
          error) state
         \<Rightarrow> bool" where
input : "\<lbrakk>(getBlockNum control) \<notin> getExecutes control;
               getBlock (getProg control) (getBlockName control) = Some l \<rbrakk> \<Longrightarrow>
         execute (State ({(memCell,control,specControl,toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
            (State ({(memCell,insertExecutes (getBlockNum control) control,
               updateSpecNoChoice specControl (getBlockNum control) (getBlockName control) l,
               toExecute@[((getBlockNum control),l)], instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| input1 : "\<lbrakk> (getBlockNum control) \<in> getExecutes control;
                   getBlock (getProg control) (getBlockName control) = Some (l@[(n, Br a x y)]);
             (getChoice specControl) (getBlockNum control) = Some children;
             (\<forall> u \<in>  children . the ((getNameMap specControl) u) \<noteq> x);
              getBlock (getProg control) x = Some A\<rbrakk> \<Longrightarrow> 
            execute (State ({(memCell,control,specControl,toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,setCount (insertExecutes (getCount control) control) (counter (getCount control)),
                     updateSpecChoice specControl (getBlockNum control) (getCount control) x A,
                    toExecute@[((getCount control), phiEliminate A (getBlockName control))],
                                 instQueue, registers, CPU, stack)} \<union> TS, GlobalControl))"
| input2 : "\<lbrakk> (getBlockNum control) \<in> getExecutes control;
                getBlock (getProg control) (getBlockName control) = Some (l@[(n, Br a x y)]);
             (getChoice specControl) (getBlockNum control) = Some children;
             (\<forall> u \<in>  children . the ((getNameMap specControl) u) \<noteq> y);
              getBlock (getProg control) y = Some A\<rbrakk> \<Longrightarrow> 
            execute (State ({(memCell,control,specControl,toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,setCount (insertExecutes (getCount control) control) (counter (getCount control)),
                     updateSpecChoice specControl (getBlockNum control) (getCount control) y A,
                    toExecute@[( (getCount control), phiEliminate A (getBlockName control))],
                                 instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| input3 : "\<lbrakk> (getBlockNum control) \<in> getExecutes control;
                getBlock (getProg control) (getBlockName control) = Some (l@[(n, UnBr x)]);
              (getChoice specControl) (getBlockNum control) = None;
              getBlock (getProg control) x = Some A\<rbrakk> \<Longrightarrow> 
            execute (State ({(memCell,control,specControl, toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                   (State ({(memCell,setCount (insertExecutes (getCount control) control) (counter (getCount control)),
                   updateSpecChoice specControl (getBlockNum control) (getCount control) x A,
                    toExecute@[( (getCount control), phiEliminate A (getBlockName control))],
                                instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| inputSpec1 : "\<lbrakk> (getBlockNum control) \<in> getExecutes control;
                      bn \<in> dom (getNameMap specControl); (getNameMap specControl) bn = Some bName;
            bn < (getBlockNum control) + maxSpec;   
          getBlock (getProg control) bName = Some (l@[(n, Br a x y)]);
             (getChoice specControl) bn = Some children;
             (\<forall> u \<in>  children . the ((getNameMap specControl) u) \<noteq> x);
              getBlock (getProg control) x = Some A\<rbrakk> \<Longrightarrow> 
            execute (State ({(memCell,control,specControl,toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,setCount (insertExecutes (getCount control) control) (counter (getCount control)),
                     updateSpecChoice specControl bn (getCount control) x A,
                    toExecute@[( (getCount control), phiEliminate A bName)],
                                 instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| inputSpec2 : "\<lbrakk> (getBlockNum control) \<in> getExecutes control;
                bn \<in> dom (getNameMap specControl); (getNameMap specControl) bn = Some bName;
            bn < (getBlockNum control) + maxSpec;   
          getBlock (getProg control) bName = Some (l@[(n, Br a x y)]);
             (getChoice specControl) bn = Some children;
             (\<forall> u \<in>  children . the ((getNameMap specControl) u) \<noteq> y);
              getBlock (getProg control) y = Some A\<rbrakk> \<Longrightarrow> 
            execute (State ({(memCell,control,specControl,toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,setCount (insertExecutes (getCount control) control) (counter (getCount control)),
                     updateSpecChoice specControl bn (getCount control) y A,
                    toExecute@[((getCount control), phiEliminate A bName)],
                                 instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| inputSpec3 : "\<lbrakk> (getBlockNum control) \<in> getExecutes control;
                   bn \<in> dom (getNameMap specControl); (getNameMap specControl) bn = Some bName;
               bn < (getBlockNum control) + maxSpec;
              getBlock (getProg control) bName = Some (l@[(n, UnBr x)]);
              (getChoice specControl) bn = None;
              getBlock (getProg control) x = Some A\<rbrakk> \<Longrightarrow> 
            execute (State ({(memCell,control,specControl, toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,setCount (insertExecutes (getCount control) control) (counter (getCount control)),
                   updateSpecChoice specControl bn (getCount control) x A,
                    toExecute@[((getCount control), phiEliminate A bName)],
                                instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| toExecuteEnd : "execute (State ({(memCell,control,specControl,((bn,[]))#toExecute,
                               instQueue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,control, specControl,
                         toExecute, instQueue, registers, CPU, stack)} \<union> TS, globalControl))"
| toQueue : "\<lbrakk> length queue < maxInstQueue \<rbrakk> \<Longrightarrow>
                 execute (State ({(memCell,control,specControl,
                      ((bn,(inum, inst)#insts))#toExecute, queue, registers, CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,control, specControl, (bn, insts)#toExecute,
                            queue@[(bn,(inum, updateInst registers (getAnti specControl)
                                (getBlockNum control) bn inst))], registers, CPU, stack)} \<union> TS, globalControl))"
| cpuLeast : "isAvailInst inst \<Longrightarrow>
           execute (State ({(memCell,control,specControl, toExecute,
                                  (bn, inum, inst)#queue, registers, None, stack)} \<union> TS, globalControl))
                   (State ({(memCell,control, specControl, toExecute,
                             queue, registers, Some (bn, inum, inst), stack)} \<union> TS, globalControl))"
| cpuNormal : "\<lbrakk>\<not> isFixedOp inst; isAvailInst inst ; (bn,inum,inst) \<in> set queue \<rbrakk> \<Longrightarrow>
              execute (State ({(memCell,control,specControl,toExecute, queue, registers, None, stack)} \<union> TS, globalControl))
                (State ({(memCell,control, specControl, toExecute, listMinus queue (bn,inum,inst),
                      registers, Some (bn, inum, inst), stack)} \<union> TS, globalControl))"
| singleRule : "\<lbrakk> \<not> isFixedOp inst; \<not> isMemoryOp inst; singleInstSolve inst = Some (x,val) \<rbrakk> \<Longrightarrow>
      execute (State ({(memCell,control,specControl,toExecute,
                        queue, registers, Some (bn,inum,inst), stack)} \<union> TS, globalControl))
              (State ({(memCell,control,
                   updateDDG (updateReg registers (getBlockNum control) bn x val)
                        (getBlockNum control) specControl, toExecute,
                     updateAllInsts (updateReg registers (getBlockNum control) bn x val)
                              (getAnti specControl) (getBlockNum control) queue,
                            updateReg registers (getBlockNum control) bn x val, None, stack)} \<union> TS, globalControl))"
| threadRule : "\<lbrakk> programs y = Some (Prog fname fargs ((BasicBlock fa fb fc)#rest));
                  length fargs = length l \<rbrakk> \<Longrightarrow>
     execute (State ({(memCell,control,specControl,toExecute,
                           queue, registers, Some (bn,inum,CreateThread x y l), stack)} \<union> TS,
                 (tidCount,tidSet,tidMap)))
               (State ({(memCell,control,setDDG specControl bn inum, toExecute,
                     updateAllInsts
                     (updateReg registers (getBlockNum control) bn x (intToIntElem tidCount tidSize))
                              (getAnti specControl) (getBlockNum control) queue,
                            updateReg registers (getBlockNum control)
                             bn x (intToIntElem tidCount tidSize), None, stack),
           ((fst memCell,[],Map.empty),(tidCount,1,0,fa,((BasicBlock fa fb fc)#rest),{}),(0, Map.empty,Map.empty,Map.empty,Map.empty),
                        [],[],(map_of (zip fargs l), Map.empty),None,[])} \<union> TS,
                    (counter tidCount,(insert tidCount tidSet),tidMap)))"
| callRule : "\<lbrakk> programs y = Some (Prog fname fargs ((BasicBlock fa fb fc)#rest));
                  length fargs = length l \<rbrakk> \<Longrightarrow>
     execute (State ({(memCell,control,specControl,toExecute,
                           queue, registers, Some (bn,inum,Call x y l), stack)} \<union> TS, globalControl))
             (State ({((fst memCell,[],Map.empty),(getTid control,1,0,fa,((BasicBlock fa fb fc)#rest),{}),
                    (0,Map.empty,Map.empty,Map.empty,Map.empty),[],[],(map_of (zip fargs l), Map.empty),None,
                    ((memCell,control,specControl,toExecute,queue,registers,(bn,inum,x))#stack))} \<union> TS, globalControl))"
| returnRule : " execute (State ({((cacheN,[],Map.empty),control,specControl,toExecute,
                           queue, registers, Some (bn,inum,Return v),
       (memCell',control',specControl',toExecute',queue',register',(bn',inum',x))#stack)} \<union> TS, globalControl))
         (State ({(memCell',control',
                         updateDDG (updateReg registers' (getBlockNum control') bn' x v)
                        (getBlockNum control') (setDDG specControl' bn' inum'),toExecute',
                     updateAllInsts (updateReg registers' (getBlockNum control') bn' x v)
                              (getAnti specControl') (getBlockNum control') queue',
                 updateReg registers' (getBlockNum control') bn' x v, None, stack)} \<union> TS, globalControl))"
| returnRuleThread : " execute (State ({((cacheN,[],Map.empty),control,specControl,toExecute,
                           queue, registers, Some (bn,inum,Return v), [])} \<union> TS, (tidCount, tidSet,tidMap)))
              (State (TS, (tidCount, tidSet - {getTid control}, tidMap(getTid control \<mapsto> v))))"
| threadJoinRule : "tidMap (nat (the (bitsToInt bl (bitsof at)))) = Some v
                       \<Longrightarrow> execute (State ({(memCell,control,specControl,toExecute,
                           queue, registers, Some (bn,inum,
                     ThreadJoin x (IntVal bl at rans inrange)), stack)} \<union> TS, (tidCount, tidSet, tidMap)))
              (State ({(memCell,control,
                  updateDDG (updateReg registers (getBlockNum control) bn x v)
                        (getBlockNum control) (setDDG specControl bn inum), toExecute,
                     updateAllInsts (updateReg registers (getBlockNum control) bn x v)
                              (getAnti specControl) (getBlockNum control) queue,
                            updateReg registers (getBlockNum control) bn x v, None, stack)}
                    \<union> TS, (tidCount, tidSet, restrict_map tidMap
                               ((dom tidMap) - {(nat (the (bitsToInt bl (bitsof at))))}))))"
| mallocRule : "execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute,
                           queue, registers, Some (bn,inum, Malloc x asize), stack)} \<union> TS, globalControl))
              (State ({((cacheN,toCommit@[(bn,inum, Create asize)],
                      readBack((bn,inum)
                             \<mapsto> (x,pointerSize,PointerType (IntType byteSize),[]))),control,specControl,
                                  toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| ddgRule : "\<lbrakk> DDG first = Some l; isAllFinished l; second \<in> the (choice first);
                   isFather anti second (getBlockNum control) \<rbrakk>
                \<Longrightarrow> execute (State ({(memCell,control,(first, DDG, choice, anti, nameMap),
                                toExecute,queue,registers,CPU, stack)} \<union> TS, globalControl))
                    (State ({(memCell,control,(second, DDG, choice, anti, nameMap),
                               toExecute,queue,registers,CPU,stack)} \<union> TS, globalControl))"
| unbrRule1 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = Some {bn'};
                (getNameMap specControl) bn' = Some x\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                                  Some (bn,inum,UnBr x),stack)} \<union> TS, globalControl))
                  (State ({(memCell,setBlockPair control bn' x,delEntryNameMap specControl bn,
                        toExecute,queue,moveSpecRegToReg registers bn',None,stack)} \<union> TS, globalControl))"
| unbrRule2 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = None;
                 getBlock (getProg control) x = Some A \<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                                  Some (bn,inum,UnBr x),stack)} \<union> TS, globalControl))
                  (State ({(memCell,setBlockPair (setCount (insertExecutes (getCount control) control)
                           (counter (getCount control))) (getCount control) x,
                       delEntryNameMap (updateSpecChoice
                               specControl bn (getCount control) x A) bn,
                        toExecute@[((getCount control), phiEliminate A x)],
                               queue,registers,None,stack)} \<union> TS, globalControl))"
| brRuleLeft1 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = Some ({bn'} \<union> rest);
                (getNameMap specControl) bn' = Some x\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum,Br (IntVal [One] (IntType 1) rans inran) x y),stack)} \<union> TS, globalControl))
                   (State ({(
                    removeAllExecutesPair
                     (removeAllEntriesForAllOtherMemcell memCell (getChoice specControl) rest)
                                   (getChoice specControl) rest,
                       setBlockPair control bn' x,delEntryNameMap (setDDG specControl bn inum) bn,
                        removeAllExecutes toExecute (getChoice specControl) rest,
                        removeAllExecutes queue (getChoice specControl) rest,
                          removeAllEntriesForAllOtherBranches
                               registers (getChoice specControl) rest,None,stack)} \<union> TS, globalControl))"
| brRuleRight1 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = Some ({bn'} \<union> rest);
                (getNameMap specControl) bn' = Some y\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum,Br (IntVal [Zero] (IntType 1) rans inran) x y),stack)} \<union> TS, globalControl))
                  (State ({(removeAllExecutesPair
                     (removeAllEntriesForAllOtherMemcell memCell (getChoice specControl) rest)
                                   (getChoice specControl) rest,
                         setBlockPair control bn' y,delEntryNameMap (setDDG specControl bn inum) bn,
                        removeAllExecutes toExecute (getChoice specControl) rest,
                        removeAllExecutes queue (getChoice specControl) rest,
                          removeAllEntriesForAllOtherBranches
                               registers (getChoice specControl) rest,None,stack)} \<union> TS, globalControl))"
| brRuleLeft2 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = None;
                      getBlock (getProg control) x = Some A\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum,Br (IntVal [One] (IntType 1) rans inran) x y),stack)} \<union> TS, globalControl))
                  (State ({(memCell,setBlockPair (setCount (insertExecutes (getCount control) control)
                           (counter (getCount control))) (getCount control) x,
                     delEntryNameMap (updateSpecChoice
                             (setDDG specControl bn inum) bn (getCount control) x A) bn,
                             toExecute, queue,registers,None,stack)} \<union> TS, globalControl))"
| brRuleLeft3 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = Some {bn'};
                      (getNameMap specControl) bn' = Some y; getBlock (getProg control) x = Some A\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum,Br (IntVal [One] (IntType 1) rans inran) x y),stack)} \<union> TS, globalControl))
                  (State ({(removeAllExecutesPair
                     (removeAllEntriesForAllOtherMemcell memCell (getChoice specControl) {bn'})
                                   (getChoice specControl) {bn'},
                 setBlockPair (setCount (insertExecutes (getCount control) control)
                           (counter (getCount control))) (getCount control) x,
                     delEntryNameMap (updateSpecChoice
                             (setDDG specControl bn inum) bn (getCount control) x A) bn,
                        removeAllExecutes toExecute (getChoice specControl) {bn'},
                        removeAllExecutes queue (getChoice specControl) {bn'},
                          removeAllEntriesForAllOtherBranches
                               registers (getChoice specControl) {bn'},None,stack)} \<union> TS, globalControl))"
| brRuleRight2 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = None;
                      getBlock (getProg control) y = Some A\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum,Br (IntVal [Zero] (IntType 1) rans inran) x y),stack)} \<union> TS, globalControl))
                   (State ({(memCell,setBlockPair (setCount (insertExecutes (getCount control) control)
                           (counter (getCount control))) (getCount control) y,
                     delEntryNameMap (updateSpecChoice
                               (setDDG specControl bn inum) bn (getCount control) y A) bn,
                             toExecute, queue,registers,None,stack)} \<union> TS, globalControl))"
| brRuleRight3 : "\<lbrakk> bn = getBlockNum control; (getChoice specControl) bn = Some {bn'};
                      (getNameMap specControl) bn' = Some x; getBlock (getProg control) y = Some A\<rbrakk> \<Longrightarrow>
           execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum,Br (IntVal [Zero] (IntType 1) rans inran) x y),stack)} \<union> TS, globalControl))
                  (State ({(removeAllExecutesPair
                     (removeAllEntriesForAllOtherMemcell memCell (getChoice specControl) {bn'})
                                   (getChoice specControl) {bn'},
                 setBlockPair (setCount (insertExecutes (getCount control) control)
                           (counter (getCount control))) (getCount control) y,
                     delEntryNameMap (updateSpecChoice
                             (setDDG specControl bn inum) bn (getCount control) y A) bn,
                        removeAllExecutes toExecute (getChoice specControl) {bn'},
                        removeAllExecutes queue (getChoice specControl) {bn'},
                          removeAllEntriesForAllOtherBranches
                               registers (getChoice specControl) {bn'},None,stack)} \<union> TS, globalControl))"
| fenceRule1 : "ords \<noteq> Seq \<Longrightarrow> 
                     execute (State ({(memCell,control,specControl,toExecute,queue,registers,
                      Some (bn,inum, Fence ords),stack)} \<union> TS, globalControl))
                   (State ({(memCell,control, specControl, toExecute,
                              queue, registers, None, stack)} \<union> TS, globalControl))"
| fenceRule2 : "execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute,queue,registers,
                      Some (bn,inum, Fence Seq),stack)} \<union> TS, globalControl))
                   (State ({((cacheN,toCommit@[(bn,inum,MemFence Seq)],readBack),control, specControl, toExecute,
                              queue, registers, None, stack)} \<union> TS, globalControl))"
| fenceDDG : "\<lbrakk> (bn,l) \<in> set toExecute;
                  getHistory (getDDG specControl) (getAnti specControl) bn x (fst specControl)
                         = ((bn',MemProto x (AFence ord) u v)#hl) \<rbrakk>
                \<Longrightarrow> execute (State ({(memCell,control,specControl,toExecute,
                                    queue,registers,CPU,stack)} \<union> TS, globalControl))
                     (State ({(memCell,control,turnTrue specControl bn' x,toExecute,
                                    queue,registers,CPU,stack)} \<union> TS, globalControl))"
| storeError : "execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Store at val (Pointer bl at' None inran) voflag),stack)} \<union> TS, globalControl))
                     (Error NotValidPointer)"
| atomicStoreError : "execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicStore at val (Pointer bl at' None inran) ord voflag),stack)} \<union> TS, globalControl))
                     (Error NotValidPointer)"
| storeError1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; (nat v < l \<or> nat v > r) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Store at val (Pointer bl at' (Some (l,r)) inran) voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| storeError2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; (nat v < il \<or> nat v > ir) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Store at val (Pointer bl at' (Some (l,r)) (Some (il,ir))) voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| storeError3 : "\<lbrakk>bitsToInt bl pointerSize = None \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Store at val (Pointer bl at' rans inran) voflag),stack)}
                        \<union> TS, globalControl))
                  (Error UndefinedBehavior)"
| atomicStoreError1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; (nat v < l \<or> nat v > r) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicStore at val (Pointer bl at' (Some (l,r)) inran) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| atomicStoreError2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; (nat v < il \<or> nat v > ir) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicStore at val (Pointer bl at' (Some (l,r)) (Some (il,ir))) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| atomicStoreError3 : "\<lbrakk>bitsToInt bl pointerSize = None \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicStore at val (Pointer bl at' rans inran) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (Error UndefinedBehavior)"
| storeRule1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; nat v \<ge> il ; nat v \<le> ir\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Store at val (Pointer bl at' (Some (l,r)) (Some (il,ir))) voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@(genWrites bn inum (sizeof at) (nat v) (the (toBytes at val))),
                      readBack),control,specControl,toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| storeRule2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Store at val (Pointer bl at' (Some (l,r)) None) voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@(genWrites bn inum (sizeof at) (nat v) (the (toBytes at val))),
                      readBack),control,specControl,toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| atomicStoreRule1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; nat v \<ge> il ; nat v \<le> ir\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicStore at val (Pointer bl at' (Some (l,r)) (Some (il,ir))) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@[(bn,inum, Write (sizeof at) (nat v) (the (toBytes at val)) ord)],
                      readBack),control,specControl,toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| atomicStoreRule2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicStore at val (Pointer bl at' (Some (l,r)) None) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@[(bn,inum, Write (sizeof at) (nat v) (the (toBytes at val)) ord)],
                      readBack),control,specControl,toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| loadError : "execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Load x at (Pointer bl at' None inran) voflag),stack)} \<union> TS, globalControl))
                     (Error NotValidPointer)"
| atomicLoadError : "execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicLoad x at
                          (Pointer bl at' None inran) ord voflag),stack)} \<union> TS, globalControl))
                     (Error NotValidPointer)"
| loadError1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; (nat v < l \<or> nat v > r) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Load x at (Pointer bl at' (Some (l,r)) inran) voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| loadError2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; (nat v < il \<or> nat v > ir) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Load x at (Pointer bl at' (Some (l,r)) (Some (il,ir))) voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| loadError3 : "\<lbrakk>bitsToInt bl pointerSize = None \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Load x at (Pointer bl at' rans inran) voflag),stack)}
                        \<union> TS, globalControl))
                  (Error UndefinedBehavior)"
| atomicLoadError1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; (nat v < l \<or> nat v > r) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicLoad x at (Pointer bl at' (Some (l,r)) inran) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| atomicLoadError2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; (nat v < il \<or> nat v > ir) \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicLoad x at (Pointer bl at' (Some (l,r)) (Some (il,ir))) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (Error MemOutOfRange)"
| atomicLoadError3 : "\<lbrakk>bitsToInt bl pointerSize = None \<rbrakk> \<Longrightarrow>
                execute (State ({(memCell,control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicLoad x at (Pointer bl at' rans inran) ord voflag),stack)}
                        \<union> TS, globalControl)) (Error UndefinedBehavior)"
| loadRule1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; nat v \<ge> il ; nat v \<le> ir\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Load x at (Pointer bl at' (Some (l,r)) (Some (il,ir))) voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@(genReads bn inum (sizeof at) (nat v) 0 (sizeof at)),
                      readBack((bn,inum) \<mapsto> (x,(sizeof at),at,[]))),control,
                          specControl,toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| loadRule2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, Load x at (Pointer bl at' (Some (l,r)) None) voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@(genReads bn inum (sizeof at) (nat v) 0 (sizeof at)),
                      readBack((bn,inum) \<mapsto> (x,(sizeof at),at,[]))),control,
                          specControl,toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| atomicLoadRule1 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l; nat v \<ge> il ; nat v \<le> ir\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicLoad x at (Pointer bl at' (Some (l,r)) (Some (il,ir))) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@[(bn,inum, Read (nat v) 0 (sizeof at) 1 ord)],
                      readBack((bn,inum) \<mapsto> (x,(sizeof at),at,[]))),control,specControl,
                                  toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| atomicLoadRule2 : "\<lbrakk>bitsToInt bl pointerSize = Some v; nat v \<le> r;nat v \<ge> l\<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,specControl,toExecute, queue,registers,
                     Some (bn,inum, AtomicLoad x at (Pointer bl at' (Some (l,r)) None) ord voflag),stack)}
                        \<union> TS, globalControl))
                  (State ({((cacheN,toCommit@[(bn,inum, Read (nat v) 0 (sizeof at) 1 ord)],
                      readBack((bn,inum) \<mapsto> (x,(sizeof at),at,[]))),control,specControl,
                            toExecute, queue,registers,None,stack)}  \<union> TS, globalControl))"
| readBackUpdate : "\<lbrakk>readBack(bn,inum) = Some (x,asize, ty, bytes); asize = length bytes;
                        toValue (asize, ty, (removeIndices bytes)) = val \<rbrakk> \<Longrightarrow>
                execute (State ({((cacheN,toCommit,readBack),control,
                      specControl,
                               toExecute, queue,registers, CPU,stack)} \<union> TS, globalControl))
                  (State ({((cacheN,toCommit, restrict_map readBack (dom readBack - {(bn,inum)}))
                      ,control,updateDDG (updateReg registers (getBlockNum control) bn x val)
                            (getBlockNum control) specControl,toExecute,
                 updateAllInsts (updateReg registers (getBlockNum control) bn x val)
                              (getAnti specControl) (getBlockNum control) queue,
          updateReg registers (getBlockNum control) bn x val,None,stack)}  \<union> TS, globalControl))"

term execute

end

end