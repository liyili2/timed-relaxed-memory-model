theory LLVMConcurrencyModel
imports Main LLVMExecutionModel
begin

fun notInSameRange where
"notInSameRange (left, right) (left1, right1) =
     ((left < left1 \<and> right < left1) \<or> (right > right1 \<and> left > right1))"

(* a function to determine if a read op is avaiable to commit *)
fun isMemAvailRead where
"isMemAvailRead [] (bn,inum,x,y) = True"
| "isMemAvailRead ((bn1, MemProto inum1 CallFence u v)#xs) (bn,inum,loc,ord) = False"
| "isMemAvailRead ((bn1, MemProto inum1 ControlFence u v)#xs) (bn,inum,loc,ord) = False"
| "isMemAvailRead ((bn1, MemProto inum1 (ToRead (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 vol) u v)#as) (bn,inum,(Pointer bs at (Some (left,right)) inran),ord) =
           (if (ord1 = Some Acquire \<or> ord1 = Some Seq) then False
                  else isMemAvailRead as (bn,inum,(Pointer bs at (Some (left,right)) inran),ord))"
| "isMemAvailRead ((bn1, MemProto inum1 (ToWrite (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 vol) u v)#as) (bn,inum,(Pointer bs at (Some (left,right)) inran),ord) =
           (if (notInSameRange (left1,right1) (left,right))
               then isMemAvailRead as (bn,inum,(Pointer bs at (Some (left,right)) inran),ord)
               else False)"
| "isMemAvailRead l (bn,inum,x,y) = False"

(* a function to determine if a write op is avaiable to commit *)
fun isMemAvailWrite where
"isMemAvailWrite [] (bn,inum,x,y) = True"
| "isMemAvailWrite ((bn1, MemProto inum1 CallFence u v)#xs) (bn,inum,loc,ord) = False"
| "isMemAvailWrite ((bn1, MemProto inum1 ControlFence u v)#xs) (bn,inum,loc,ord) = False"
| "isMemAvailWrite ((bn1, a)#xs) (bn,inum,loc,(Some Release)) = False"
| "isMemAvailWrite ((bn1, a)#xs) (bn,inum,loc,(Some Seq)) = False"
| "isMemAvailWrite ((bn1, MemProto inum1 (ToRead (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 vol) u v)#as) (bn,inum,(Pointer bs at (Some (left,right)) inran),ord) =
           (if ((ord1 = Some Acquire \<or> ord1 = Some Seq) \<or>
                 \<not> notInSameRange (left1,right1) (left,right)) then False
                  else isMemAvailWrite as (bn,inum,(Pointer bs at (Some (left,right)) inran),ord))"
| "isMemAvailWrite ((bn1, MemProto inum1 (ToWrite (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 vol) u v)#as) (bn,inum,(Pointer bs at (Some (left,right)) inran),ord) =
           (if (notInSameRange (left1,right1) (left,right))
               then isMemAvailWrite as (bn,inum,(Pointer bs at (Some (left,right)) inran),ord)
               else False)"
| "isMemAvailWrite l (bn,inum,x,y) = False"

(* a function to determine if an mem-op has volatile conflict with others *)
fun isVolatileConflict where
"isVolatileConflict [] = False"
| "isVolatileConflict ((bn1, MemProto inum1 (ToRead (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 True) u v)#xs) = True"
| "isVolatileConflict ((bn1, MemProto inum1 (ToRead (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 False) u v)#xs) = isVolatileConflict xs"
| "isVolatileConflict ((bn1, MemProto inum1 (ToWrite (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 True) u v)#xs) = True"
| "isVolatileConflict ((bn1, MemProto inum1 (ToWrite (Pointer bs1 at1 (Some (left1,right1)) inran1)
                  ord1 False) u v)#xs) = isVolatileConflict xs"
| "isVolatileConflict ((bn1, a)#xs) = isVolatileConflict xs"

fun isMemAvailAux where
"isMemAvailAux [] (bn,inum,x) = True"
| "isMemAvailAux ((bn, h)#xs) (bn',inum',(ToRead x y False)) =
     isMemAvailRead ((bn, h)#xs) (bn',inum',x,y)"
| "isMemAvailAux ((bn, h)#xs) (bn',inum',(ToRead x y True)) =
     ((isMemAvailRead ((bn, h)#xs) (bn',inum',x,y)) \<and> \<not> isVolatileConflict ((bn, h)#xs))"
| "isMemAvailAux ((bn, h)#xs) (bn',inum',(ToWrite x y False)) =
     isMemAvailWrite ((bn, h)#xs) (bn',inum',x,y)"
| "isMemAvailAux ((bn, h)#xs) (bn',inum',(ToWrite x y True)) =
     ((isMemAvailWrite ((bn, h)#xs) (bn',inum',x,y)) \<and> \<not> isVolatileConflict ((bn, h)#xs))"
| "isMemAvailAux ((bn, h)#xs) (bn',inum',a) = False"

definition isMemAvailable where
"isMemAvailable l a = isMemAvailAux (rev l) a"

(* datatype defining the message between caches and leader cache *)
datatype message = MemCreating nat (* create a memory from cache id and size *)
  | ToSeqCaches 
  | WaitToSeq nat
  | ToSeqWrite nat nat "byte list" "(nat \<times> nat)" order
        (* time stamp, base, bytes range order *)

datatype ack = MemCreated nat nat nat nat (* msgNum, leader created the memory
                    and then send back with range of memory left edge, right edge and init-time stamps*)
  | AMemCreate nat nat nat nat (* seqnum, mem field created for tother caches *)
  | SeqTheCache nat (* with a sequence number sending back to leader *)
  | FinishSeq nat (* msgNum *)
  | WriteHappen nat nat "byte list" "(nat \<times> nat)" (* time stamp, base, byte list range order *)
  | SeqWriteHappen nat nat nat "byte list" "(nat \<times> nat)"
              (* seq-number, time stamp, base, byte list range order *)
  | MemOpFail "(nat \<times> nat)" nat (* range, time stamps *)

datatype ('a,'b) leaderMessage = SeqSend 'a | NormalSend 'b

datatype objType = Static | Heap

(* a function to generate a list of bytes of pointer for creating memory region *)
fun addIndexToBytes where
"addIndexToBytes n [] = []"
| "addIndexToBytes n (x#xs) = (n,x)#(addIndexToBytes (n + 1) xs)"

definition createPionterBytes where
"createPionterBytes left right =
     addIndexToBytes 0 (toBytesAux (pointerSize div byteSize) (intToBits left pointerSize) (Some (left,right)) None)"

(* functions to update or set readback cell from a successful read *)
fun setReadBack where
"setReadBack (var,asize,ty,bl) bl' = (var,asize,ty,bl')"

fun updateReadBackAux where
"updateReadBackAux [] a b = [(a,b)]"
| "updateReadBackAux ((x,y)#xs) a b =
       (if a > x then (x,y)#(updateReadBackAux xs a b) else (a,b)#(x,y)#xs)"

fun updateReadBack where
"updateReadBack (var,asize,ty,bl) a b = (var,asize,ty, updateReadBackAux bl a b)"

(* functions to update the seqNum map in the leader *)
fun updateSeqMap where
"updateSeqMap seqs a = seqs(a \<mapsto> (the (seqs a)) + 1)"

(* a function to write a list of bytes to locations in byteMap *)
fun writeToByteMap where
"writeToByteMap byteMap base [] = byteMap"
| "writeToByteMap byteMap base (x#xs) = writeToByteMap (byteMap(base \<mapsto> x)) (base + 1) xs"

(* a function to read a list of bytes from byteMap with indices *)
fun readFromByteMap where
"readFromByteMap byteMap base 0 count = []"
| "readFromByteMap byteMap base (Suc n) count
     = (count,the (byteMap base))#(readFromByteMap byteMap (base + 1) n (count + 1))"

fun existCallFence where
"existCallFence l = (\<exists> x u v . (MemProto x CallFence u v) \<in> set l)"

locale concurrentModel = executionModel where
           programs = "programs :: 'id \<Rightarrow> ('id,'a) program option"
        and counter = "counter :: nat \<Rightarrow> nat"
        and findInSpecReg = "findInSpecReg :: ((nat \<times> 'id) \<Rightarrow> 'id element option)
                           \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'id \<Rightarrow> 'id element option"
        and findPathToFather = "findPathToFather ::
                           (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list option"
        and isFather = "isFather :: (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
        and usesInAllDefs = "usesInAllDefs :: ('id,'a) program \<Rightarrow> 'id set \<Rightarrow> 'id set \<Rightarrow> bool"
        and rewriteMap = "rewriteMap :: ((nat \<times> 'id) \<Rightarrow> 'id element option) \<Rightarrow> ('id \<Rightarrow> 'id element option)"
        and getChildren = "getChildren :: (nat \<Rightarrow> nat set option) \<Rightarrow> nat \<Rightarrow> nat set"
      for programs counter findInSpecReg findPathToFather isFather usesInAllDefs rewriteMap getChildren +
      fixes rewriteGraph :: "(nat \<Rightarrow> 'id memProto list option)
                         \<Rightarrow> (nat \<Rightarrow> 'id option) \<Rightarrow> (nat \<Rightarrow> 'id memProto list option)"
      assumes rewriteGraphProperty : "\<forall> DDG DDG' nameMap . rewriteGraph DDG nameMap = DDG' \<longrightarrow>
          (\<exists> S . (\<forall> s n l x u v. s \<in> S \<and> nameMap n = Some s
              \<longrightarrow> (\<not> existCallFence l \<and> DDG n = Some l \<and> DDG' n = Some (l@[MemProto x ControlFence u v]))))"
begin

inductive concurrency where
  errorFromExecute : "execute (State (Ts, global)) (Error x)
                \<Longrightarrow> concurrency (State (global, Ts, Ms, memGlobal)) (Error x)"
| executeRule : "execute (State (Ts, global)) (State (Ts', global'))
                \<Longrightarrow> concurrency (State (global, Ts, Ms, memGlobal)) (State (global', Ts', Ms, memGlobal))"
| memMoveRule1 :  "\<lbrakk> getBlockNum control \<ge> bn \<rbrakk> \<Longrightarrow> 
        concurrency
           (State (global, {((cacheNum,(bn,inum, v)#toCommit, readBack),control,specControl, rest)} \<union> Ts,
                         {(cacheNum, memOpList, rest')} \<union> Ms, memGlobal))
                     (State (global, {((cacheNum,toCommit, readBack),
                                      control,setDDG specControl bn inum, rest)} \<union> Ts,
                            {(cacheNum, memOpList@[(getTid control, bn,inum,v)], rest')} \<union> Ms, memGlobal))"
| memMoveRule2 :  "\<lbrakk> (bn,inum,v) \<in> set toCommit; isMemAvailable hl (bn,inum,elem);
                getHistory (rewriteGraph (getDDG specControl) (getNameMap specControl))
                       (getAnti specControl) bn inum (fst specControl)
                         = hl@[(bn,MemProto inum elem num1 num2)] \<rbrakk> \<Longrightarrow>
          concurrency
           (State (global, {((cacheN, toCommit, readBack),control,specControl, rest)} \<union> Ts,
                         {(cacheNum, memOpList, rest')} \<union> Ms, memGlobal))
                     (State (global, {((cacheNum,listMinus toCommit (bn,inum,v), readBack),control,
                                  setDDG specControl bn inum, rest)} \<union> Ts,
                            {(cacheNum, memOpList@[(getTid control, bn,inum,v)], rest')} \<union> Ms, memGlobal))"
(* malloc function will be implemented by assuming that there is a seq_cst fence that requires
   a global equality on memory *)
| sendMsg : "concurrency
           (State (global, Ts, {(cacheNum, memOpList,msgNum,msg#messages,rest')} \<union> Ms, (receive,memGlobal)))
              (State (global, Ts, {(cacheNum, memOpList,msgNum,messages,rest')} \<union> Ms, (receive@[msg],memGlobal)))"
| dealCreate : "concurrency
           (State (global, Ts, Ms, ((cacheNum,msgNum,MemCreating n)#receive,cacheSet,
                   send,nextLoc, memFeilds, seqNum, seqWaitMap, memGlobal)))
              (State (global, Ts, Ms, ((cacheNum, msgNum, WaitToSeq seqNum)#receive,cacheSet,
                  send@[(SeqSend (seqNum, remove1 cacheNum cacheSet,
                      AMemCreate seqNum nextLoc (nextLoc + n) 0, MemCreated msgNum nextLoc (nextLoc + n) 0))],
                 nextLoc+ (n + 1), memFeilds((nextLoc,nextLoc+n) \<mapsto> 0),
                           seqNum + 1, seqWaitMap(seqNum \<mapsto> 0), memGlobal)))"
| dealSeqFence : "concurrency
           (State (global, Ts, Ms, ((cacheNum, msgNum, ToSeqCaches)#receive,cacheSet,
                   send,nextLoc, memFeilds, seqNum, seqWaitMap, memGlobal)))
              (State (global, Ts, Ms, ((cacheNum, msgNum,WaitToSeq seqNum)#receive,cacheSet,
                  send@[(SeqSend (seqNum, remove1 cacheNum cacheSet,
                          SeqTheCache seqNum, FinishSeq msgNum))], nextLoc, memFields,
                           seqNum + 1, seqWaitMap(seqNum \<mapsto> 0), memGlobal)))"
| dealWrite : "\<lbrakk> ord \<noteq> Seq; atime > the (memFields (left,right)) \<rbrakk> \<Longrightarrow>
         concurrency
           (State (global, Ts, Ms, ((cacheNum, msgNum,
                   ToSeqWrite atime base bs (left,right) ord)#receive,cacheSet,
                   send,nextLoc, memFeilds, seqNum, seqWaitMap, memGlobal)))
              (State (global, Ts, Ms, (receive,cacheSet,
                  send@[(NormalSend (remove1 cacheNum cacheSet,
                          WriteHappen (atime + 1) base bs (left,right)))], nextLoc, memFields,
                           seqNum, seqWaitMap, memGlobal)))"
| ignoreWrite : "\<lbrakk> atime \<le> the (memFields (left,right)) \<rbrakk> \<Longrightarrow>
         concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum, messages, acks, rest)} \<union> Ms,
                  ((cacheNum, msgNum,
                   ToSeqWrite atime base bs (left,right) ord)#receive,cacheSet,
                   send,nextLoc, memFeilds, seqNum, seqWaitMap, memGlobal)))
              (State (global, Ts, {(cacheNum, memOpList, msgNum, messages,
                 acks@[MemOpFail (left,right) (the (memFields (left,right)) + 1)], rest)} \<union> Ms,
                  (receive,cacheSet, send, nextLoc,
                       memFields((left,right) \<mapsto> the (memFields (left,right)) + 1),
                           seqNum, seqWaitMap, memGlobal)))"
| dealSeqWrite : "\<lbrakk>  atime > the (memFields (left,right)) \<rbrakk> \<Longrightarrow>
         concurrency
           (State (global, Ts, Ms, ((cacheNum, msgNum,
                   ToSeqWrite atime base bs (left,right) Seq)#receive,cacheSet,
                   send,nextLoc, memFeilds', seqNum, seqWaitMap, memGlobal)))
              (State (global, Ts, Ms, (receive,cacheSet,
                  send@[(SeqSend (seqNum,remove1 cacheNum cacheSet,
                          SeqWriteHappen seqNum (atime + 1) base bs (left,right), FinishSeq msgNum))],
                     nextLoc, memFields',
                           seqNum + 1, seqWaitMap(seqNum \<mapsto> 0), memGlobal)))"
| normalSend : "concurrency
           (State (global, Ts, 
                {(cache, memOpList, msgNum, messages, acks, rest)} \<union> Ms,
                      (receive, cacheSet, (NormalSend (cache#caches, ack))#send, memGlobal)))
              (State (global, Ts, {(cache, memOpList, msgNum, messages, acks@[ack], rest)} \<union> Ms,
                       (receive, cacheSet, (NormalSend (caches,ack))#send, memGlobal)))"
| normalSendEnd : "concurrency
           (State (global, Ts, Ms,
                      (receive, cacheSet, (NormalSend ([], ack))#send, memGlobal)))
              (State (global, Ts,  Ms, (receive, cacheSet, send, memGlobal)))"
| seqSend : "concurrency
           (State (global, Ts, 
                {(cache, memOpList, msgNum, messages, acks, rest)} \<union> Ms,
                      (receive, cacheSet, (SeqSend (flag,cache#caches, otherAck, ack))#send, memGlobal)))
              (State (global, Ts, {(cache, memOpList, msgNum, messages, acks@[otherAck], rest)} \<union> Ms,
                       (receive, cacheSet, (SeqSend (flag,caches,otherAck, ack))#send, memGlobal)))"
| seqSendEnd : "\<lbrakk> seqWaitMap flag = Some (length cacheSet - 1)\<rbrakk> \<Longrightarrow>
          concurrency
           (State (global, Ts, 
                {(cacheNum, memOpList, msgNum, messages, acks, rest)} \<union> Ms,
                      ((cacheNum, msgNum,WaitToSeq flag)#receive,
                           cacheSet, (SeqSend (flag,[], otherAck,ack))#send,
                              nextLoc, memFeilds', seqNum, seqWaitMap, memGlobal)))
            (State (global, Ts, {(cache, memOpList, msgNum, messages, acks@[ack], rest)} \<union> Ms,
               (receive, cacheSet, send, nextLoc, memFeilds', seqNum,
                      restrict_map seqWaitMap (dom seqWaitMap - {flag}), memGlobal)))"
| toCreateMemRule : " concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Create n)#memOpList,msgNum,messages,rest')} \<union> Ms, memGlobal))
                     (State (global, Ts, {(cacheNum, (tid,bn,inum,WaitMsg msgNum)#memOpList,
                                msgNum + 1,messages@[(cacheNum,msgNum,MemCreating n)], rest')} \<union> Ms, memGlobal))"
| CreatedMemRule : "\<lbrakk> getTid control = tid \<rbrakk> \<Longrightarrow>
         concurrency
           (State (global, {((cacheNum,toCommit, readBack),control,threadRest)} \<union> Ts,
                          {(cacheNum, (tid,bn,inum,WaitMsg msgNum)#memOpList,
                         msgNum,messages,(MemCreated msgNum left right time)#acks,
                          memfields,byteMap, objects, rest')} \<union> Ms, memGlobal))
            (State (global,{((cacheNum,toCommit,
                readback((bn,inum) \<mapsto> setReadBack (the (readBack (bn,inum))) (createPionterBytes left right))),
                  control,threadRest)} \<union> Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields((left,right) \<mapsto> time),
                        byteMap, objects \<union> {((left,right),Heap,Map.empty,{})}, rest')} \<union> Ms, memGlobal))"
| notifyMemCreate : "concurrency
           (State (global, Ts, {(cacheNum, memOpList,
                         msgNum,messages,(AMemCreate flag left right time)#acks,
                                 memfields,byteMap, objects, rest')} \<union> Ms,
                (receive, cacheSet, send, nextLoc, memFeilds', seqNum, seqWaitMap, memGlobal)))
            (State (global,Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields((left,right) \<mapsto> time),
                       byteMap, objects \<union> {((left,right), Heap, Map.empty, {})}, rest')} \<union> Ms,
              (receive, cacheSet, send, nextLoc, memFeilds', seqNum, updateSeqMap seqWaitMap flag, memGlobal)))"
| seqFenceRule : "concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,MemFence Seq)#memOpList,
                 msgNum,messages,rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, (tid,bn,inum,WaitMsg msgNum)#memOpList,
                                msgNum + 1,messages@[(cacheNum,msgNum,ToSeqCaches)], rest')} \<union> Ms, memGlobal))"
| finishSeqRule : "concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,WaitMsg msgNum)#memOpList,
                         msgNum',messages,(FinishSeq msgNum)#acks, rest')} \<union> Ms, memGlobal))
            (State (global, Ts, {(cacheNum, memOpList,
                          msgNum',messages, acks, rest')} \<union> Ms, memGlobal))"
| notifySeqRule : "concurrency
           (State (global, Ts, {(cacheNum, memOpList,
                         msgNum,messages,(SeqTheCache flag)#acks, memfields, rest')} \<union> Ms,
                (receive, cacheSet, send, nextLoc, memFeilds', seqNum, seqWaitMap, memGlobal)))
            (State (global,Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields, rest')} \<union> Ms,
              (receive, cacheSet, send, nextLoc, memFeilds', seqNum, updateSeqMap seqWaitMap flag, memGlobal)))"
| notifyWrite : "\<lbrakk> atime > the (memfields (left,right))\<rbrakk> \<Longrightarrow>
          concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,
              (WriteHappen atime base bs (left,right))#acks, memfields,byteMap,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms,memGlobal))
            (State (global,Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields((left,right) \<mapsto> atime),
                      writeToByteMap byteMap base bs,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| notifyWriteFail : "\<lbrakk> atime \<le> the (memfields (left,right))\<rbrakk> \<Longrightarrow>
          concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,
              (WriteHappen atime base bs (left,right))#acks, memfields,byteMap,
                       objects, rest')} \<union> Ms, memGlobal))
            (State (global,Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields,byteMap,
                       objects, rest')} \<union> Ms, memGlobal))"
| notifySeqWrite : "\<lbrakk> atime > the (memfields (left,right))\<rbrakk> \<Longrightarrow>
          concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,
              (SeqWriteHappen flag atime base bs (left,right))#acks, memfields,byteMap,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms,
                (receive, cacheSet, send, nextLoc, memFeilds', seqNum, seqWaitMap, memGlobal)))
            (State (global,Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields((left,right) \<mapsto> atime),
                      writeToByteMap byteMap base bs,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms,
              (receive, cacheSet, send, nextLoc', memFeilds', seqNum, updateSeqMap seqWaitMap flag, memGlobal)))"
| notifySeqWriteFail : "\<lbrakk> atime \<le> the (memfields (left,right))\<rbrakk> \<Longrightarrow>
          concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,
              (SeqWriteHappen flag atime base bs (left,right))#acks, memfields,byteMap,
                  objects, rest')} \<union> Ms,
                (receive, cacheSet, send, nextLoc, memFeilds', seqNum, seqWaitMap, memGlobal)))
            (State (global,Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields, byteMap, objects, rest')} \<union> Ms,
              (receive, cacheSet, send, nextLoc', memFeilds', seqNum, updateSeqMap seqWaitMap flag, memGlobal)))"
(* the difference of complete and race is that race only has writes but complete can contain non-atomic reads *)
| atomicWriteRule : "\<lbrakk> ord \<noteq> Seq ; (left,right) \<in> dom memfields;  base \<ge> left ; base \<le> right \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base 1 bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, memOpList,
                     msgNum + 1,messages@[(cacheNum,msgNum,
                     ToSeqWrite (the (memfields (left,right)) + 1) base bs (left,right) ord)], acks,
                  memfields((left,right) \<mapsto> (the (memfields (left,right))) + 1),writeToByteMap byteMap base bs,
                   {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| atomicWriteSeq : "\<lbrakk>  (left,right) \<in> dom memfields;  base \<ge> left ; base \<le> right \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base 1 bs Seq)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, (tid,bn,inum,WaitMsg msgNum)#memOpList,
                           msgNum + 1,messages@[(cacheNum,msgNum,
                           ToSeqWrite(the (memfields (left,right)) + 1) base bs (left,right) Seq)],
                             acks,memfields((left,right) \<mapsto> (the (memfields (left,right))) + 1),
                             writeToByteMap byteMap base bs,
                   {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| atomicWriteRace1 : "\<lbrakk>(left,right) \<in> dom memfields;  base \<ge> left ; base \<le> right ; race \<noteq> {}\<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base 1 bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,race)} \<union> objects, rest')} \<union> Ms, memGlobal))
             (Error StoreRace)"
| nonAtomicWriteRace1 : "\<lbrakk> (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right; asize \<noteq> 1 ; race \<noteq> {} ; (tid,bn,inum) \<notin> race\<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base asize bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,race)} \<union> objects, rest')} \<union> Ms, memGlobal))
             (Error StoreRace)"
| nonAtomicWriteRace2 : "\<lbrakk> (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right; asize \<noteq> 1 ; race \<noteq> {} \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base asize bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete, {(tid,bn,inum)} \<union> race)} \<union> objects, rest')} \<union> Ms, memGlobal))
             (Error StoreRace)"
| nonAtomicWriteFirst : "\<lbrakk> (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right; asize \<noteq> 1 \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base asize bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, Map.empty,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, memOpList,
                           msgNum + 1,messages@[(cacheNum,msgNum,
                           ToSeqWrite (the (memfields (left,right)) + 1) base bs (left,right) ord)],
                             acks,memfields((left,right) \<mapsto> (the (memfields (left,right))) + 1),
                             writeToByteMap byteMap base bs,
                   {((left,right),Heap, Map.empty((tid,bn,inum) \<mapsto> 1),{(tid,bn,inum)})}
                             \<union> objects, rest')} \<union> Ms, memGlobal))"
| nonAtomicWriteNext : "\<lbrakk> (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right; asize \<noteq> 1; complete (tid,bn,inum) = Some n;
                  n <  asize - 1 \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base asize bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{(tid,bn,inum)})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, memOpList,
                           msgNum + 1,messages@[(cacheNum,msgNum,
                           ToSeqWrite (the (memfields (left,right)) + 1) base bs (left,right) ord)],
                             acks,memfields((left,right) \<mapsto> (the (memfields (left,right))) + 1),
                                     writeToByteMap byteMap base bs,
                   {((left,right),Heap, complete((tid,bn,inum) \<mapsto> n + 1),{(tid,bn,inum)})}
                             \<union> objects, rest')} \<union> Ms, memGlobal))"
| nonAtomicWriteFinal : "\<lbrakk> (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right; asize \<noteq> 1; complete (tid,bn,inum) = Some (asize - 1) \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Write base asize bs ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{(tid,bn,inum)})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, memOpList,
                           msgNum + 1,messages@[(cacheNum,msgNum,
                           ToSeqWrite (the (memfields (left,right)) + 1) base bs (left,right) ord)],
                             acks,memfields((left,right) \<mapsto> (the (memfields (left,right))) + 1),
                               writeToByteMap byteMap base bs,
                   {((left,right),Heap, restrict_map complete (dom complete - {(tid,bn,inum)}),{})}
                             \<union> objects, rest')} \<union> Ms, memGlobal))"
| failReceiveFromLeader1 : "\<lbrakk> time \<le> the (memfields (left,right)) \<rbrakk> \<Longrightarrow>
        concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,(MemOpFail (left,right) time)#acks,
                 memfields, rest')} \<union> Ms, memGlobal))
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,acks,
                 memfields, rest')} \<union> Ms, memGlobal))"
| failReceiveFromLeader2 : "\<lbrakk> time > the (memfields (left,right)) \<rbrakk> \<Longrightarrow>
        concurrency
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,(MemOpFail (left,right) time)#acks,
                 memfields, rest')} \<union> Ms, memGlobal))
           (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,acks,
                 memfields((left,right) \<mapsto> time), rest')} \<union> Ms, memGlobal))"
| readRaceFail : "\<lbrakk> (left,right) \<in> dom memfields; base \<ge> left ; base \<le> right; race \<noteq> {}\<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Read base pos asize bnum ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,race)} \<union> objects, rest')} \<union> Ms, memGlobal))
             (Error LoadRace)"
| atomicReadRule : "\<lbrakk> ord \<noteq> Seq ; (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right ; getTid control = tid \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global,  {((cacheNum,toCommit, readBack), control,threadRest)} \<union> Ts,
               {(cacheNum, (tid,bn,inum,Read base 0 1 bnum ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, {((cacheNum,toCommit,
                readback((bn,inum) \<mapsto> setReadBack (the (readBack (bn,inum))) (readFromByteMap byteMap base bnum 0))),
                  control,threadRest)} \<union> Ts, {(cacheNum, memOpList,
                     msgNum,messages, acks, memfields,byteMap,
                   {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| atomicReadSeq : "\<lbrakk> (left,right) \<in> dom memfields;  base \<ge> left ; base \<le> right \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, Ts, {(cacheNum, (tid,bn,inum,Read base 0 1 bnum Seq)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, (tid,bn,inum,WaitToRead msgNum base bnum)#memOpList,
                           msgNum + 1,messages@[(cacheNum,msgNum,ToSeqCaches)],
                       acks,memfields,byteMap,
                   {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| finishSeqRead : "\<lbrakk> getTid control = tid \<rbrakk> \<Longrightarrow>
      concurrency
           (State (global, {((cacheNum,toCommit, readBack), control,threadRest)} \<union> Ts,
               {(cacheNum, (tid,bn,inum,WaitToRead msgNum base bnum)#memOpList,
                         msgNum,messages,(FinishSeq msgNum)#acks,memfields,byteMap, rest')} \<union> Ms, memGlobal))
            (State (global, {((cacheNum,toCommit,
               readback((bn,inum) \<mapsto> setReadBack (the (readBack (bn,inum))) (readFromByteMap byteMap base bnum 0))),
                      control,threadRest)} \<union>  Ts, {(cacheNum, memOpList,
                          msgNum,messages, acks, memfields,byteMap, rest')} \<union> Ms, memGlobal))"
| nonAtomicReadFirst : "\<lbrakk> (left,right) \<in> dom memfields; base \<ge> left ;
                 base \<le> right; asize \<noteq> 1 ; getTid control = tid \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global,  {((cacheNum,toCommit, readBack), control,threadRest)} \<union> Ts,
                {(cacheNum, (tid,bn,inum,Read base pos asize 1 ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global,  {((cacheNum,toCommit,
               readBack((bn,inum) \<mapsto> updateReadBack (the (readBack (bn,inum))) pos (the (byteMap (base + pos))))),
                   control,threadRest)} \<union> Ts,
                   {(cacheNum, memOpList, msgNum,messages,acks,memfields, byteMap,
                   {((left,right),Heap, complete((tid,bn,inum) \<mapsto> 1),{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| nonAtomicReadNext : "\<lbrakk> (left,right) \<in> dom memfields;
           base \<ge> left ; base \<le> right; asize \<noteq> 1; complete (tid,bn,inum) = Some n;
                  n <  asize - 1 ; getTid control = tid \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, {((cacheNum,toCommit, readBack), control,threadRest)} \<union> Ts,
               {(cacheNum, (tid,bn,inum,Read base pos asize 1 ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, {((cacheNum,toCommit,
               readBack((bn,inum) \<mapsto> updateReadBack (the (readBack (bn,inum))) pos (the (byteMap (base + pos))))),
                   control,threadRest)} \<union> Ts,
                  {(cacheNum, memOpList,msgNum,messages,acks,memfields, byteMap,
                   {((left,right),Heap, complete((tid,bn,inum) \<mapsto> n + 1),{})} \<union> objects, rest')} \<union> Ms, memGlobal))"
| nonAtomicReadFinal : "\<lbrakk> (left,right) \<in> dom memfields; base \<ge> left ; base \<le> right;
                    asize \<noteq> 1; complete (tid,bn,inum) = Some (asize - 1); getTid control = tid \<rbrakk> \<Longrightarrow>
       concurrency
           (State (global, {((cacheNum,toCommit,
              readBack((bn,inum) \<mapsto> updateReadBack (the (readBack (bn,inum))) pos (the (byteMap (base + pos))))),
                 control,threadRest)} \<union> Ts,
               {(cacheNum, (tid,bn,inum,Read base pos asize 1 ord)#memOpList,
                 msgNum,messages,acks, memfields,byteMap,
                       {((left,right),Heap, complete,{})} \<union> objects, rest')} \<union> Ms, memGlobal))
             (State (global, Ts, {(cacheNum, memOpList, msgNum,messages,acks,memfields,byteMap,
                   {((left,right),Heap, restrict_map complete (dom complete - {(tid,bn,inum)}),{})}
                             \<union> objects, rest')} \<union> Ms, memGlobal))"

end

end