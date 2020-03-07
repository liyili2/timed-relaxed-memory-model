(*Liyi Li Oct 1st, 2019 *)

theory AxiomaticModel
imports Main
begin

(* This document is the definition file of ATRCM. 
   An execution in ATRCM is (T,Tid,Loc,Lock,\<rho>,sbs,dds,rf):
   A set of Time points, a finite set of thread-IDs,
   a set of locations, a set of Lock keys,
   a map from time points to memory events,
   a family of sequenced-before relations (one for each thread),
   a set of data dapendencies, and a read-from relation.
   This model assumes that an RMW is always a single atomic element.
  *)


(* syntax definition for memory order on memory operations *)
datatype order = Relaxed | Release | Acquire | AcqRel | SeqCst

(*memory actions including memory operations and fence-like structures
  We define actions for atomic/non-atomic memory operations differently.
  An atomic memory operation contains four field, a Boolean value for marking if the action
  is a volatile memory operation (volatile model in LLVM), a value, a location and an order.
  A non-atomic memory operation contains a Boolean flag for volatile memory operation flag,
  a value, a location, an action-ID (the action-ID of the first event in the group)
  uniquely identify a group of non-atomic memory operations
  to be in the same group (meaning that they are from the same instruction and finishing the same task),
  a natural number representing the i-th position of the current memory operation in the group,
  and a natural number representing the total number of elements in the group.
  Fence-like structures include a memory fence with order, locks, a control fence representing
  the control dependency, and a call fence. A call fence usually comes in a pair of call fences with
  the calling function name, and a unique key identifying the two call fences in a pair. 
   *)
datatype ('aid,  'val, 'loc, 'lock,'name,'key) action =
    ARead bool 'val 'loc order
  | AWrite bool 'val 'loc order
  | RMW bool 'val 'loc order
  | NRead bool 'val 'loc 'aid nat nat
  | NWrite bool 'val 'loc 'aid nat nat
  | Fence order
  | Lock 'lock
  | UnLock 'lock
  | CallFence 'name 'key
  | ControlFence


(*check if a memory event's action is a write op (AWrite, RMW, NWrite) *)
fun isWriteBasic where
 "isWriteBasic (AWrite vol x y z) = True"
| "isWriteBasic (RMW vol x y z) = True"
| "isWriteBasic (NWrite vol x y z u v) = True"
| "isWriteBasic x = False"

(* check if a write is atomic *)
fun isAtomicWriteBase where
 "isAtomicWriteBase (AWrite vol x y z) = True"
| "isAtomicWriteBase (RMW vol x y z) = True"
| "isAtomicWriteBase x = False"

fun isWrite where
 "isWrite rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isWriteBasic z)"

(* check if an action is a write but not a rmw *)
fun isPureWriteBasic where
 "isPureWriteBasic (AWrite vol x y z) = True"
| "isPureWriteBasic (NWrite vol x y z u v) = True"
| "isPureWriteBasic x = False"

fun isPureWrite where
 "isPureWrite rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isPureWriteBasic z)"

(* check if an action is a read op ARead RMW NRead *)
fun isReadBasic where
"isReadBasic (ARead vol a x y) = True"
| "isReadBasic (RMW vol x y z) = True"
| "isReadBasic (NRead vol a x y u v) = True"
| "isReadBasic x = False"

fun isRead where
"isRead rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isReadBasic z)"

(* check if an action is a read but not a rmw *)
fun isPureReadBasic where
"isPureReadBasic (ARead vol a x y) = True"
| "isPureReadBasic (NRead vol a x y u v) = True"
| "isPureReadBasic x = False"

fun isPureRead where
"isPureRead rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isPureReadBasic z)"

(* check if an action is a memory location create 
fun isCreate where
"isCreate rho t = (case rho t of (Some (x,y,Create l)) \<Rightarrow> True | _ \<Rightarrow> False)"

 check if an action is a memory location free  
fun isFree where
"isFree rho t = (case rho t of (Some (x,y,Free l)) \<Rightarrow> True | _ \<Rightarrow> False)"
*)

(* check if an action is a RMW *)
fun isRMW where
"isRMW rho t = (case rho t of (Some (u,v,(RMW vol x y z))) \<Rightarrow> True | _ \<Rightarrow> False)"

(* check if an action is a write or a read, a memory operation is a write or a read *)
fun isMemOp where
 "isMemOp rho x = (isWrite rho x \<or> isPureRead rho x)"

(* check if an action is an atomic memory operation *)
fun isAtomicBasic where
 "isAtomicBasic (AWrite vol x y r) = True"
| "isAtomicBasic (RMW vol x y r) = True"
| "isAtomicBasic (ARead vol a x r) = True"
| "isAtomicBasic x = False"

fun isAtomic where
"isAtomic rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isAtomicBasic z)"

(* check if an action is a memory operation whose volatile flag is on (bool value to be true) *)
fun isVolatileBasic where
"isVolatileBasic (ARead vol a x y) = vol"
| "isVolatileBasic (RMW vol x y z) = vol"
| "isVolatileBasic (AWrite vol x y z) = vol"
| "isVolatileBasic (NRead vol a x y u v) = vol"
| "isVolatileBasic (NWrite vol x y z u v) = vol"
| "isVolatileBasic x = False"

fun isVolatile where
"isVolatile rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isVolatileBasic z)"

(* check if an action is an atomic memory operation whose order is SeqCst *)
fun isSeqAtomicBasic where
 "isSeqAtomicBasic (AWrite vol x y SeqCst) = True"
| "isSeqAtomicBasic (RMW vol x y SeqCst) = True"
| "isSeqAtomicBasic (ARead vol a x SeqCst) = True"
| "isSeqAtomicBasic x = False"

fun isSeqAtomic where
"isSeqAtomic rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isSeqAtomicBasic z)"

(* check if an action is an atomic read (ARead/rmw) whose order is SeqCst *)
fun isSeqRead where
"isSeqRead rho t = (isSeqAtomic rho t \<and> isRead rho t)"

(* check if an action is an atomic read but not rmw  whose order is SeqCst *)
definition isSeqPureRead where
"isSeqPureRead rho a = (isPureRead rho a \<and> isSeqAtomic rho a)"

(* check if an action is a fence whose order is SeqCst *)
fun isSeqFence where
"isSeqFence rho t = (case rho t of (Some (x,y,Fence SeqCst)) \<Rightarrow> True | _ \<Rightarrow> False)"

(* check if an action is a seqcst fence or seqcst atomic memory operation *)
fun hasSeq where
 "hasSeq rho x = (isSeqAtomic rho x \<or> isSeqFence rho x)"

(* check if an action is a memory fence *)
fun isRealFence where
"isRealFence rho t = (case rho t of Some (x,y,(Fence r)) \<Rightarrow> True | _ \<Rightarrow> False)"

(* check if an action is not a memory operation,
     a fence-like structure is an action that is not a memory operation *)
fun isFenceLikeBasic where
"isFenceLikeBasic (Fence x) = True"
| "isFenceLikeBasic (Lock l) = True"
| "isFenceLikeBasic (UnLock l) = True"
| "isFenceLikeBasic (CallFence a b) = True"
| "isFenceLikeBasic (ControlFence) = True"
| "isFenceLikeBasic x = False"

fun isFenceLike where
"isFenceLike rho t = (case rho t of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isFenceLikeBasic z)"

(* get the memory location of a read-write operation, and check if two ops have the same locations *)
fun acLoc where
"acLoc (ARead vol a x y) = Some x"
| "acLoc (RMW vol x y z) = Some y"
| "acLoc (AWrite vol x y z) = Some y"
| "acLoc (NRead vol a x y u v) = Some x"
| "acLoc (NWrite vol x y z u v) = Some y"
| "acLoc x = None"

fun getLoc where
"getLoc rho t = (case rho t of None \<Rightarrow> None | Some (x,y,z) \<Rightarrow> acLoc z)"


(* check if two memory locations from two actions are the same *)
fun isTheLoc where
"isTheLoc rho t loc = (case getLoc rho t of None \<Rightarrow> False | Some x \<Rightarrow> x = loc)"

fun sameLocBasic where
"sameLocBasic a b  = (case acLoc a of Some x \<Rightarrow>
                       (case acLoc b of Some y \<Rightarrow> if x = y then True else False | _ \<Rightarrow> False)
                     | _ \<Rightarrow> False)"

fun sameLoc where
"sameLoc rho a b = (case rho a of None \<Rightarrow> False
                            | Some (x,y,z) \<Rightarrow> (case rho b of None \<Rightarrow> False
                                  | Some (u,v,w) \<Rightarrow> sameLocBasic z w))"

(* get the tid of a memory event *)
fun getTid where
"getTid rho a = (case rho a of None \<Rightarrow> None | Some (x,y,z) \<Rightarrow> Some x)"

(* check if two events being in the same thread-ID *)
fun sameThread where
"sameThread rho a b =  (case getTid rho a of None \<Rightarrow> False
                  | Some x \<Rightarrow> (case getTid rho b of None \<Rightarrow> False | Some y \<Rightarrow> x = y))"

(* get the aid (action-ID) of a memory event *)
fun getAid where
"getAid rho t = (case rho t of None \<Rightarrow> None | Some (x,y,z) \<Rightarrow> Some y)"

(* check if two events being in the same action-ID *)
fun sameAid where
"sameAid rho a b = (case getAid rho a of None \<Rightarrow> False
       | Some y \<Rightarrow> (case getAid rho b of None \<Rightarrow> False | Some z \<Rightarrow> y = z))"

(* get the value of a read-write operation and check if two ops have the same value*)
fun acVal where
"acVal (ARead vol a x y) = Some a"
| "acVal (RMW vol x y z) = Some x"
| "acVal (AWrite vol x y z) = Some x"
| "acVal (NRead vol a x y u v) = Some a"
| "acVal (NWrite vol x y z u v) = Some x"
| "acVal x = None"

fun getVal where
"getVal rho t = (case rho t of None \<Rightarrow> None | Some (x,y,z) \<Rightarrow> acVal z)"

(* check if two events's actions having the same values *)
fun sameValBasic where
"sameValBasic a b  = (case acVal a of Some x \<Rightarrow>
                       (case acVal b of Some y \<Rightarrow> if x = y then True else False | _ \<Rightarrow> False)
                     | _ \<Rightarrow> False)"

fun sameVal where
"sameVal rho a b = (case rho a of None \<Rightarrow> False
                            | Some (x,y,z) \<Rightarrow> (case rho b of None \<Rightarrow> False
                                  | Some (u,v,w) \<Rightarrow> sameValBasic z w))"

(* get the order of an event's action *)
fun acOrderBasic where
"acOrderBasic (ARead vol x y z) = Some z"
| "acOrderBasic (AWrite vol x y z) = Some z"
| "acOrderBasic (RMW vol x y z) = Some z"
| "acOrderBasic (Fence x) = Some x"
| "acOrderBasic x = None"

fun acOrder where
"acOrder rho t = (case rho t of None \<Rightarrow> None | Some (x,y,z) \<Rightarrow> acOrderBasic z)"

(* the order of an event's action is not a relaxed *)
definition hasAtLeastAcqRel where
"hasAtLeastAcqRel rho t = (case acOrder rho t of None \<Rightarrow> False
                               | Some z \<Rightarrow> if z = Relaxed then False else True)"

(* the order of an event's action is not a relaxed or release *)
definition atLeastAcq where
"atLeastAcq rho t = (case acOrder rho t of None \<Rightarrow> False
                               | Some z \<Rightarrow> if z = Relaxed \<or> z = Release then False else True)"

(* the order of an event's action is not a relaxed or acquire *)
definition atLeastRel where
"atLeastRel rho t = (case acOrder rho t of None \<Rightarrow> False
                               | Some z \<Rightarrow> if z = Relaxed \<or> z = Acquire then False else True)"

(* the order of an event's action is acqrel or seqcst *)
definition atLeastAcqRel where
"atLeastAcqRel rho t = (case acOrder rho t of None \<Rightarrow> False
                               | Some z \<Rightarrow> if z = AcqRel \<or> z = SeqCst then True else False)"

(* the order of an event's action is acquire *)
definition isAcq where
"isAcq rho t = (case acOrder rho t of None \<Rightarrow> False
                               | Some z \<Rightarrow> if z = Acquire then True else False)"

(* the order of an event's action is release *)
definition isRel where
"isRel rho t = (case acOrder rho t of None \<Rightarrow> False
                               | Some z \<Rightarrow> if z = Release then True else False)"

(* an event's action is a release write *)
definition isRelWrite where
"isRelWrite rho x = (isRel rho x \<and> isWrite rho x)"

(* an event's action is a acquire read *)
definition isAcqRead where
"isAcqRead rho x = (isAcq rho x \<and> isRead rho x)"

(* check if an event's action is the same as another action *)
fun hasAction where
"hasAction rho t y = (case rho t of None \<Rightarrow> False | Some (u,v,w) \<Rightarrow> (if w = y then True else False))"

definition toLocalExecution where
"toLocalExecution tid f = (\<lambda> x . (case f x of None \<Rightarrow> None | Some (a,b) \<Rightarrow> if a = tid then Some b else None))"

(* get all thread ids in the co-domain of a rho *)
definition getAllTids where
"getAllTids f = {a . \<exists> b . (a,b) \<in> range f}"

(* get the additional dependencies of an event's action (memory operation) 
fun getDepSetBasic where
"getDepSetBasic (ARead vol a x y al) = Some al"
| "getDepSetBasic (RMW vol x y z al) = Some al"
| "getDepSetBasic (AWrite vol x y z al) = Some al"
| "getDepSetBasic (NRead vol a x y u v al) = Some al"
| "getDepSetBasic (NWrite vol x y z u v al) = Some al"
| "getDepSetBasic x = None"

fun getDepSet where
"getDepSet rho t = (case rho t of None \<Rightarrow> None | Some (x,y,z) \<Rightarrow> getDepSetBasic z)"
*)

type_synonym loc_type = int
type_synonym time_type = nat
type_synonym aid_type = nat

definition getLeast where
"getLeast S = (if S = {} then None else Some (SOME x. x \<in> S \<and> (\<forall>  y \<in> S . y = x \<or> y < x)))"

lemma natHasBottom : "\<lbrakk> getLeast (S::nat set) = p ; S \<noteq> {} \<rbrakk> \<Longrightarrow> (\<exists> (x::nat) . p = Some x)"
  by (meson getLeast_def)

(*a program is defined a a list of ('inst \<times> 'inst) list and each thread has a ('inst \<times> 'inst) list *)
locale axiomaticModel =
  fixes actions :: "(aid_type, 'val, loc_type, 'lock, 'name, 'callID) action set"
    and locations :: "loc_type set"
    and actionIDs :: "aid_type set"
    and times :: "time_type set"
    and threads :: "'tid set"
    and locks :: "'lock set"
    and names :: "'name set"
    and callIDs :: "'callID set"
begin

(* 
Here, we define some assumptions for some elements in an execution:
(T,Tid, Loc,Lock,\<rho>,sbs,dds,rf)
 the predicates of well-formed on time points T, tid set,
 sbs, dds, rf, and \<rho>
*)
(* A well-formed T requires that it does not exist a backward edge in rf. *)
definition wellformedTime :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
                    (time_type \<times> time_type) set \<Rightarrow> bool" where
"wellformedTime T rho rf = (0 \<notin> T \<and> T \<subseteq> times \<and> (\<forall> t1 t2 . (t1,t2) \<in> rf \<longrightarrow> t1 \<in> T \<and> t2 \<in> T)
                            \<and> (\<forall> t act . rho t = Some act \<longrightarrow> t \<in> T)
                            \<and> (\<forall> t . t \<in> T \<longrightarrow> (\<exists> act . rho t = Some act)))"

(* Well-formed assumption for the thread-ID set, as every event in \<rho> should be a valid thread-ID. *)
definition wellformedTid :: "'tid set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"wellformedTid Tid rho = (Tid \<subseteq> threads \<and>
                            (\<forall> t tid aid ac . rho t = Some (tid,aid,ac) \<longrightarrow> tid \<in> Tid))"

(* Well-formed assumption for sbs, such that every time points in the relation must be a valid one in T *)
definition wellformedSB1 :: "'tid set \<Rightarrow> time_type set
                                      \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option) \<Rightarrow> bool" where
"wellformedSB1 Tid T sbs = (\<forall> t S a b . sbs t = Some S \<and> (a,b) \<in> S \<longrightarrow> t \<in> Tid \<and> a \<in> T \<and> b \<in> T)"

(* each sb in sbs also needs to be disjointedly unioned.*)
definition wellformedSB2 :: "'tid set \<Rightarrow> time_type set
                                      \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option) \<Rightarrow> bool" where
"wellformedSB2 Tid T sbs = (\<forall> t1 t2 S1 S2 . t1 \<noteq> t2 \<and> sbs t1 = Some S1 \<and> sbs t2 = Some S2
                            \<longrightarrow> Field (S1) \<inter> Field (S2) = {})"
definition wellformedSB where
"wellformedSB Tid T sbs = (wellformedSB1 Tid T sbs \<and> wellformedSB2 Tid T sbs)"

(* all relations of dds should be contained in sbs, so it is obviously dds \<union> sbs+ is acyclic.*)
definition wellformedDD where
"wellformedDD Tid sbs dds = (\<forall> tid . trancl (the (dds tid)) \<subseteq> trancl (the (sbs tid)))"

(* Well-formed rf needs to satisfy that for every pair (a,b) in rf, 
   a is a time point of write, while b is a time point of read. *)
definition wellformedRF where
"wellformedRF T rho rf = ((\<forall> a b . (a,b) \<in> rf \<longrightarrow> a \<in> T \<and> b \<in> T)
                       \<and> (\<forall> a b . (a,b) \<in> rf \<longrightarrow> isWrite rho a \<and> isRead rho b \<and> sameLoc rho a b))"

definition rfAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rfAssumption rf rho = ((\<forall> a b . (a,b) \<in> rf
        \<longrightarrow> isWrite rho a \<and> isRead rho b \<and> sameLoc rho a b \<and> a < b \<and> sameVal rho a b) \<and>
          (\<forall> a1 a2 b .  (a1,b) \<in> rf \<and> (a2,b) \<in> rf \<longrightarrow> (a1 = a2)))"


definition sbAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"sbAssumption sb rho = (\<forall> a b aid1 aid2  . (a,b) \<in> sb \<longrightarrow>
           getAid rho a = Some aid1 \<and> getAid rho b = Some aid2 \<and> sameThread rho a b
             \<and> aid1 < aid2 \<and> \<not> (\<exists> z . aid1 < z \<and> z < aid2))"

(* The following two assumptions assume that the order of a group of non-atomic events
   is in the increasing of the order of the position number of the non-atomic actions of the events.
   This assumption is just for simplicity.  *)
definition sbNReadAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"sbNReadAssumption sb rho = (\<forall> a b tid1 aid1  tid2 aid2 x t na nb n v v' vol . (a,b) \<in> trancl sb \<and>
           rho a = Some (tid1, aid1, NRead vol v x t na n) \<and> rho b = Some (tid2,aid2,NRead vol v' x t nb n)
             \<and> a < b \<longrightarrow> na < nb)"

definition sbNWriteAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"sbNWriteAssumption sb rho = (\<forall> a b tid1 aid1  tid2 aid2 v1 v2 x t na nb n vol . (a,b) \<in> trancl sb \<and>
           rho a = Some (tid1, aid1, NWrite vol v1 x t na n) \<and> rho b = Some (tid2,aid2,NWrite vol v2 x t nb n)
             \<and> a < b \<longrightarrow> na < nb)"

definition sbAllAssumptions where
"sbAllAssumptions sb rho = (sbAssumption sb rho \<and> sbNReadAssumption sb rho \<and> sbNWriteAssumption sb rho)"

definition allSbAllAssumptions where
"allSbAllAssumptions Tids sbs rho = (\<forall> tid \<in> Tids .
                        (\<forall> sb . sbs tid = Some sb \<longrightarrow> sbAllAssumptions sb rho))"

(* The assumption about the range of \<rho>. The domain of it is larger than T,
    and there is a unique action id for every event in the range of \<rho>. *)
definition rhoAssumption where
"rhoAssumption T rho = (rho 0 = None
          \<and> (\<forall> t t1  . t \<in> T \<and> t1 \<in> T \<and> sameAid rho t t1 \<longrightarrow> t = t1) \<and> T \<subseteq> dom rho)"

(*These two assumptions restricts the write-read pairs of non-atomic operations in rf. 
  We assume that in an execution,
   a write-read pair including a non-atomic memory operation happens iff
   every event in the group of the non-atomic operations happens in the execution, 
    and only the non-atomic memory operation in the group with its position number and ttoal
    the same can join the communication as an element of a pair in rf.
    Combining this assumption with the above assumptions that non-atomic
    operations must come in order, it means that only the last memory operation of a group of
    non-atomic operations can join the communication in a rf in an execution.
  This can be turned into a relation in the model to select valid candidate executions,
  so that the non-satisfied executions can be viewed as a communication having a race
   since there is a non-atomic instruction that does not finish all messages sending. 
   At this point, we just leave it as an assumption.  *)
definition rfNWriteAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rfNWriteAssumption rf rho = (\<forall> a b tid1 aid1 v x t na n vol . (a,b) \<in> rf
        \<and> rho a = Some (tid1, aid1, NWrite vol v x t na n)  \<longrightarrow> na = n)"

definition rfNReadAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rfNReadAssumption rf rho = (\<forall> a b tid1 aid1 x t na n v vol . (a,b) \<in> rf
        \<and> rho b = Some (tid1, aid1, NRead vol v x t na n)  \<longrightarrow> na = n)"

definition rfAllAssumption where
"rfAllAssumption rf rho = (rfAssumption rf rho \<and> rfNWriteAssumption rf rho \<and> rfNReadAssumption rf rho)"

(* defining a relation collecting the sb-position relation on all fence-like ops in each thread
   This relation set all fences not crossing each other in an execution. *)
inductive_set fenceRelation :: "time_type set 
    \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  fenceLikeRule : "\<lbrakk> (a,b) \<in> trancl sb;
               isFenceLike rho a; isFenceLike rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> fenceRelation T rho sb"

(* defining control dependence,
   control dependence happens when there is a binary branching inst in the time of the op. 
    no writes can go cross a control fence, but reads can go cross a control fence if there is no
    data dependency in the conditions of the branching *)
inductive_set controldep :: "time_type set 
    \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  controlWriteRule1: "\<lbrakk> (a,b) \<in> trancl sb;
             rho b = Some (tid, aid, ControlFence); {a,b} \<subseteq> T; isWrite rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> controldep T rho sb"
| controlWriteRule2: "\<lbrakk> (a,b) \<in> trancl sb;
             rho a = Some (tid, aid, ControlFence); {a,b} \<subseteq> T; isWrite rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> controldep T rho sb"

(* call/lock dependency is like a acqrel fence in each thread to indicate that
    a memory op cannot go cross a function call (lib call). 
   this fence is useful in doing function call optimization
   i.e. declaring a function is an inline function *)
inductive_set calldep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  callFence1: "\<lbrakk> (a,b) \<in> trancl sb; rho b = Some (tid,aid,CallFence name key);
                    isMemOp rho a \<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep T rho sb"
| callFence2: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tid,aid,CallFence name key);
                isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep T rho sb"
| lockRule1: "\<lbrakk> (a,b) \<in> trancl sb; rho b = Some (tid, aid, (Lock l));
                isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep T rho sb"
| lockRule2: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tid, aid, (Lock l));
                isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep T rho sb"
| unLockRule1: "\<lbrakk> (a,b) \<in> trancl sb; rho b = Some (tid,aid,(UnLock l));
                   isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep T rho sb"
| unLockRule2: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tid,aid,(UnLock l));
                   isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep T rho sb"
(*| createRule1: "\<lbrakk> (a,b) \<in> trancl sb; isCreate rho b; {a,b} \<subseteq> E; isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| createRule2: "\<lbrakk> (a,b) \<in> trancl sb; isCreate rho a;{a,b} \<subseteq> E;isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| freeRule1: "\<lbrakk> (a,b) \<in> trancl sb; isFree rho b; {a,b} \<subseteq> E; isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| freeRule2: "\<lbrakk> (a,b) \<in> trancl sb; isFree rho a; {a,b} \<subseteq> E; isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb" *)

(* volatile dependency in all threads.
   LLVM volatile model indicates that any two volatile memory operations cannot switch order. *)
inductive_set volatileDep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
 volDef : "\<lbrakk> (a,b) \<in> trancl sb; isVolatile rho a; isVolatile rho b \<rbrakk>
           \<Longrightarrow> (a,b) \<in> volatileDep T rho sb"

(* define data dependency in all threads and additional dependencies.
   Another way of defining data dependency by compiling additional data dependency
   on memory operations and having basic dependency from the relations of different
   memory operations. It will be a simpler proof for connecting ATRCM with the LLVM operational model.

inductive_set addDataDep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
 additionalDep : "\<lbrakk> (a,b) \<in> trancl sb; {a,b} \<subseteq> E; getDepSet rho b = Some bl;
                     getAid rho a = Some aid; aid \<in> set bl\<rbrakk>
           \<Longrightarrow> (a,b) \<in> addDataDep E rho sb"


inductive_set basicDatadep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  wwdependence: "\<lbrakk> (a,b) \<in> trancl sb;  {a,b} \<subseteq> E; isWrite rho a; isWrite rho b; sameLoc rho a b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> basicDatadep E rho sb"
| rwdependence: "\<lbrakk> (a,b) \<in> trancl sb; {a,b} \<subseteq> E; isPureRead rho a; isWrite rho b; sameLoc rho a b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> basicDatadep E rho sb"
| wrdependence: "\<lbrakk> (a,b) \<in> trancl sb; {a,b} \<subseteq> E; isWrite rho a; isPureRead rho b; sameLoc rho a b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> basicDatadep E rho sb"

definition datadep where
"datadep E rho sb = (addDataDep E rho sb) \<union> basicDatadep E rho sb"
*)

(* memory ordering dependency in a single thread.
   Most memory orders except SeqCst order only have single-threaded effects.
   The current seqcst + read or seqcst + write operations are too weak
   according to the C++ documentation. Needs the version here to match RC11. *)
inductive_set singleorderdep :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: " (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" where
  readAcqRule: "\<lbrakk> (a,b) \<in> trancl sb; isAcqRead rho a;
                  isWrite rho b \<or> isPureRead rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| readSeqRule1: "\<lbrakk> (a,b) \<in> trancl sb; isSeqAtomic rho a; isPureRead rho a; 
                   isWrite rho b \<or> isRead rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| readSeqRule2: "\<lbrakk> (a,b) \<in> trancl sb; isSeqAtomic rho b; isPureRead rho b; isWrite rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| writeRelRule: "\<lbrakk> (a,b) \<in> trancl sb; isRelWrite rho b;{a,b} \<subseteq> E;
                  isWrite rho a \<or> isRead rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| writeSeqRule1: "\<lbrakk> (a,b) \<in> trancl sb; isPureWrite rho b; isSeqAtomic rho b; {a,b} \<subseteq> E;
                     isWrite rho a \<or> isRead rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| writeSeqRule2: "\<lbrakk> (a,b) \<in> trancl sb; isPureWrite rho a; isSeqAtomic rho a;
                     isWrite rho b \<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| rmwAllRule1: "\<lbrakk> (a,b) \<in> trancl sb; isRMW rho b; atLeastAcqRel rho b; isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| rmwAllRule2: "\<lbrakk> (a,b) \<in> trancl sb; isRMW rho a; atLeastAcqRel rho a; isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| acqFence1 : "\<lbrakk> (a,b) \<in> trancl sb; isRealFence rho a; isAcq rho a; isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| acqFence2 : "\<lbrakk> (a,b) \<in> trancl sb; isRealFence rho b; isAcq rho b;isRead rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| relFence1 : "\<lbrakk> (a,b) \<in> trancl sb; isRealFence rho b; isRel rho b; isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| relFence2 : "\<lbrakk> (a,b) \<in> trancl sb; isRealFence rho a; isRel rho a; isWrite rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| acqRelUpFence1 : "\<lbrakk> (a,b) \<in> trancl sb; isRealFence rho b;
                            atLeastAcqRel rho b; isMemOp rho a\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"
| acqRelUpFence2 : "\<lbrakk> (a,b) \<in> trancl sb; isRealFence rho a;
                            atLeastAcqRel rho a; isMemOp rho b\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep T rho sb"


(* define the true program order relation,
    it is a combination of all single thread dependency. *)
inductive_set po :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set"
    and dd :: "(time_type \<times> time_type) set" where
 callRule : "(a,b) \<in> calldep T rho sb \<Longrightarrow> (a,b) \<in> po T rho sb dd"
| controlRule : "(a,b) \<in> controldep T rho sb \<Longrightarrow> (a,b) \<in> po T rho sb dd"
| dataRule : "(a,b) \<in> dd \<Longrightarrow> (a,b) \<in> po T rho sb dd"
| volatileRule : "(a,b) \<in> volatileDep T rho sb \<Longrightarrow> (a,b) \<in> po T rho sb dd"
| singleOrderRule : "(a,b) \<in> singleorderdep T rho sb \<Longrightarrow> (a,b) \<in> po T rho sb dd"

(* define a program order family (pos) as the transitive closure all po for all threads *)
definition pos where
"pos Tid T rho sbs dds = trancl (\<Union> tid \<in> Tid . po T rho (the (sbs tid)) (the (dds tid)))"

(* a complete set for af, every dependency has an clear edge from one event to the other,
   these edges can act as an indication of which event should happen early than another event.
   if there is no edges between two events, it means that either one can happen early, so 
   it essentially means that there are two edges connecting this two. 
   this process tries to add all two edges on no connected events. 
inductive_set completeAf :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" where
completeLeft : "\<lbrakk> \<not> (a,b) \<in> trancl (af E rho sb); \<not> (b,a) \<in> trancl (af E rho sb) \<rbrakk>
             \<Longrightarrow> (a,b) \<in> completeAf E rho sb"
| completeRight : "\<lbrakk> \<not> (a,b) \<in> trancl (af E rho sb); \<not> (b,a) \<in> trancl (af E rho sb) \<rbrakk>
             \<Longrightarrow> (b,a) \<in> completeAf E rho sb"
*)

(* get a set of initial state, where an execution can start with such time 
inductive_set initialStates :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> time_type set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" where
genInitialState : "\<lbrakk> \<not> (\<exists> c . (c,a) \<in> af E rho sb) \<rbrakk> \<Longrightarrow> a \<in> initialStates E rho sb"

definition allowedSingleExecutionSet :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type set \<times> (time_type \<times> time_type) set)" where
"allowedSingleExecutionSet E rho sb
    = (initialStates E rho sb, af E rho sb \<union> completeAf E rho sb)"

inductive allowedExecutionInductive where
allowedBasic : "allowedExecutionInductive (a,{},R)"
| allowedInductive : "\<lbrakk> allowedExecutionInductive (a', S, R); getBottom (insert a' S) = Some a' \<rbrakk>
                  \<Longrightarrow> allowedExecutionInductive (a,insert a' S,R)"

(* define what is an allowed execution in a single thread context *)
definition isAllowedSingleExecution :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> bool" where
"isAllowedSingleExecution E rho po =
  (if E = {} then True else
   (case allowedSingleExecutionSet E rho po of (init,R)
             \<Rightarrow> (the (getLeast E) \<in> init
                 \<and> allowedExecutionInductive (the (getLeast E), E - {the (getLeast E)}, R))))"
*)

(* defining an allowed execution in each single thread
     by checking if there is an edge from a later time point to a earlier time point*)
definition isAllowedSingleExecution :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set \<Rightarrow> bool" where
"isAllowedSingleExecution T rho sb dd = (\<forall> a b . (a,b) \<in> po T rho sb dd \<longrightarrow> a < b)"

fun selectTimeByTid where
"selectTimeByTid tid T rho = {t . t \<in> T \<and> (\<exists> tid' aid ac . rho t = Some (tid',aid,ac) \<and> tid = tid')}"

(* the predicate for each thread in the tid-set to satisfy the allowed execution predicate above. *)
definition satE :: "'tid set \<Rightarrow>
          time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
            ('tid \<Rightarrow> (time_type \<times> time_type) set option)
      \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option) \<Rightarrow> bool" where
"satE Tid T rho sbs dds = (\<forall> tid \<in> Tid . 
                   isAllowedSingleExecution (selectTimeByTid tid T rho) rho (the (sbs tid)) (the (dds tid)))"

(*
definition localTimes where
"localTimes ts f tid = {x . x \<in> ts \<and> (\<exists> h . f x = Some (tid, h))}"
*)

(* Here, we start the definition of multi-threaded behaviors in ATRCM.
   Basically, it defines two things. First, it defines the global total order of
   SC atomics. Second, it defines a multi-threaded memory communication scheduler. *)
(* defining the existence of a seqcst fence in the middle of two points *)
definition seqFenceInMid where
"seqFenceInMid T rho a b = (\<exists> t . t \<in> T \<and> a < t \<and> t < b \<and> isSeqFence rho t)"

(* defining the existence of a seqcst read in the middle of two points *)
definition seqReadInMid where
"seqReadInMid T rho a b x = (\<exists> t . t \<in> T \<and> a < t \<and> t < b \<and> isSeqRead rho t \<and> getLoc rho t = Some x)"

(* check if a non-atomic write is the final one in its group,
             if so, then it is able to be read by another time point in rf *)
definition isFinalNWrite where
"isFinalNWrite rho t = (case rho t of Some (x,y,NWrite vol v loc aid i n) \<Rightarrow> i = n
                                          | _ \<Rightarrow> False)"

(* defining the existence of a write with the same location in the middle of two points *)
definition writeInMid where
"writeInMid T rho a b loc = (\<exists> t .
                        t \<in> T \<and> a < t \<and> t < b \<and> isTheLoc rho t loc \<and>
            ((isWrite rho t \<and> isAtomic rho t) \<or>
            (isWrite rho t \<and> \<not> isAtomic rho t \<and> isFinalNWrite rho t)))"

(* defining the existence of a write with the same location in the middle of two points *)
definition sameThreadWriteInMid where
"sameThreadWriteInMid T rho a b loc = (\<exists> t .
                        t \<in> T \<and> a < t \<and> t < b \<and> isTheLoc rho t loc \<and>
            ((isWrite rho t \<and> isAtomic rho t) \<or>
            (isWrite rho t \<and> \<not> isAtomic rho t \<and> isFinalNWrite rho t))
                          \<and> sameThread rho t b)"

(* tr collects all write-read pairs in a thread that does not appear in rf*)
inductive_set tr ::"time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> loc_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
trEmpty : "\<lbrakk> \<not> sameThreadWriteInMid T rho a b x; isRead rho b; getLoc rho b = Some x;
                       a = 0; b \<in> T\<rbrakk> \<Longrightarrow> (a,x,b) \<in> tr T rho rf"
| trGet : "\<lbrakk> \<not> sameThreadWriteInMid E rho a b x; isWrite rho a;isRead rho b;
             getLoc rho b = Some x;sameLoc rho a b;sameThread rho a b; b \<in> T \<rbrakk> \<Longrightarrow> (a,x,b) \<in> tr T rho rf"

lemma trZero : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ;(a,x,b) \<in> tr T \<rho> rf\<rbrakk>
         \<Longrightarrow> a \<noteq> 0"
  apply (erule tr.cases)
   apply (simp add: wellformedTime_def rhoAssumption_def wellformedRF_def,clarsimp)
  apply (simp add: wellformedTime_def rhoAssumption_def wellformedRF_def,clarsimp)
  apply (subgoal_tac "a \<in> T \<and> 0 \<notin> T \<longrightarrow> a \<noteq> 0")
   apply simp
  by auto

lemma trReadInSet : "(a,x,b) \<in> tr T \<rho> rf \<Longrightarrow> b \<in> T"
  apply (erule tr.cases)
  by auto

lemma isWriteInTR : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ;(a,x,b) \<in> tr T \<rho> rf\<rbrakk>
          \<Longrightarrow> isWrite \<rho> a"
  apply (erule tr.cases)
  by (simp add: wellformedTime_def rhoAssumption_def wellformedRF_def,clarsimp)

lemma sameLocInTR : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ;(a,x,b) \<in> tr T \<rho> rf\<rbrakk>
          \<Longrightarrow> sameLoc \<rho> a b"
  apply (erule tr.cases)
  by (simp add: wellformedTime_def rhoAssumption_def wellformedRF_def,clarsimp)

lemma locXInTR : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ;(a,x,b) \<in> tr T \<rho> rf\<rbrakk>
          \<Longrightarrow> getLoc \<rho> b = Some x"
  apply (erule tr.cases)
  by (simp add: wellformedTime_def rhoAssumption_def wellformedRF_def,clarsimp)

(* fullRf = rf \<union> tr *)
definition fullRf where
"fullRf T rho rf = ({(a,x,b) . (a,b) \<in> rf \<and> getLoc rho a = Some x} \<union> tr T rho rf)"

lemma fullRfReadInSet : "\<lbrakk> rhoAssumption T \<rho>;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ; (a,x,b) \<in> fullRf T \<rho> rf\<rbrakk> 
            \<Longrightarrow> b \<in> T"
  apply (simp add: fullRf_def)
  apply (case_tac "(a, x, b) \<in> tr T \<rho> rf",clarsimp)
   apply (simp add: trReadInSet)
  apply clarsimp
  by (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)

lemma isWriteInFullRf : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ; (a,x,b) \<in> fullRf T \<rho> rf\<rbrakk> 
            \<Longrightarrow> isWrite \<rho> a"
  apply (simp add: fullRf_def)
  apply (case_tac "\<rho> a")
   apply clarsimp
   apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def,clarsimp)
  apply (subgoal_tac "a \<in> T \<and> T \<subseteq> dom \<rho> \<longrightarrow> \<rho> a \<noteq> None")
    apply clarsimp
  apply blast
  apply (case_tac "(a, x, b) \<in> tr T \<rho> rf",clarsimp)
   apply (subgoal_tac " isWrite \<rho> a")
    apply simp
   apply (erule_tac a = a and x = x and b = b and T = T and \<rho> = \<rho> and rf = rf in isWriteInTR)
  apply clarsimp+
  apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "b" in allE)
  by auto

lemma sameLocInFullRf : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ; (a,x,b) \<in> fullRf T \<rho> rf\<rbrakk> 
            \<Longrightarrow> sameLoc \<rho> a b"
  apply (simp add: fullRf_def)
  apply (case_tac "\<rho> a")
   apply clarsimp
   apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def,clarsimp)
  apply (subgoal_tac "a \<in> T \<and> T \<subseteq> dom \<rho> \<longrightarrow> \<rho> a \<noteq> None")
    apply clarsimp
  apply blast
  apply (case_tac "(a, x, b) \<in> tr T \<rho> rf",clarsimp)
   apply (subgoal_tac "sameLoc \<rho> a b")
    apply simp
   apply (erule_tac a = a and x = x and b = b and T = T and \<rho> = \<rho> and rf = rf in sameLocInTR)
  apply clarsimp+
  apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "b" in allE)
  by auto

lemma locXInFullRf : "\<lbrakk> rhoAssumption T \<rho>; a \<in> T; b \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ; (a,x,b) \<in> fullRf T \<rho> rf\<rbrakk> 
            \<Longrightarrow> getLoc \<rho> b = Some x"
  apply (simp add: fullRf_def)
  apply (case_tac "\<rho> b")
   apply clarsimp
   apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def,clarsimp)
  apply (subgoal_tac "b \<in> T \<and> T \<subseteq> dom \<rho> \<longrightarrow> \<rho> b \<noteq> None")
    apply clarsimp
  apply blast
  apply (case_tac "(a, x, b) \<in> tr T \<rho> rf",clarsimp)
   apply (subgoal_tac "getLoc \<rho> b = Some x")
    apply simp
   apply (erule_tac a = a and x = x and b = b and T = T and \<rho> = \<rho> and rf = rf in locXInTR)
  apply clarsimp+
  apply (simp add: wellformedRF_def,clarsimp)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "b" in allE)
  apply (erule_tac x = "b" in allE)
  apply clarsimp
  apply (case_tac "\<rho> a")
   apply clarsimp
  apply clarsimp
  apply (case_tac "acLoc ba")
   apply clarsimp
  apply clarsimp
  apply (case_tac "x = ad")
  by clarsimp+

lemma sameLocTwoInFullRf: "\<lbrakk> rhoAssumption T \<rho>; s \<in> T; t \<in> T;
       wellformedTime T \<rho> rf ; wellformedRF T \<rho> rf ; (s,x,a) \<in> fullRf T \<rho> rf; (t,x,b) \<in> fullRf T \<rho> rf\<rbrakk> 
            \<Longrightarrow> sameLoc \<rho> s t"
  apply (subgoal_tac "a \<in> T")
   prefer 2
  apply (simp add: fullRfReadInSet)
  apply (subgoal_tac "b \<in> T")
   prefer 2
  apply (simp add: fullRfReadInSet)
  apply (subgoal_tac "getLoc \<rho> a = Some x")
   prefer 2
   apply (erule_tac T = T and \<rho> = \<rho> and a = s and b = a and x = x and rf = rf in locXInFullRf)
  apply (simp,simp,simp,simp,simp)
  apply (subgoal_tac "getLoc \<rho> b = Some x")
   prefer 2
   apply (erule_tac T = T and \<rho> = \<rho> and a = t and b = b and x = x and rf = rf in locXInFullRf)
  apply (simp,simp,simp,simp,simp)
  apply (subgoal_tac "sameLoc \<rho> s a")
   prefer 2
  thm sameLocInFullRf
  apply (erule_tac T = T and \<rho> = \<rho> and a = s and b = a and x = x and rf = rf in sameLocInFullRf)
  apply (simp,simp,simp,simp,simp)
  apply (subgoal_tac "sameLoc \<rho> t b")
  prefer 2
   apply (erule_tac T = T and \<rho> = \<rho> and a = t and b = b and x = x and rf = rf in sameLocInFullRf)
       apply (simp,simp,simp,simp,simp)
  apply auto
  apply (case_tac "\<rho> a")
   apply clarsimp
  apply (case_tac "\<rho> b")
   apply clarsimp
  apply (case_tac "\<rho> s")
   apply clarsimp
  apply (case_tac "\<rho> t")
   apply clarsimp+
  apply (case_tac "acLoc bb")
   apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def,clarsimp)
  apply (case_tac "acLoc bc")
   apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def,clarsimp)
  apply (case_tac "ah = x")
   apply clarsimp
  apply (case_tac "ai = x")
  by clarsimp+

definition full_rf where
"full_rf T rho rf = { (a,b) . \<exists> x . (a,x,b) \<in> (fullRf T rho rf) }"

(* sr is to define write-read pairs for a seqcst-read/seqcst-fence.
   we view the seqcst fence as a universal read op to observe a value for a location for every location *)
inductive_set sr :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> loc_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
  fromSeqFence : "\<lbrakk> {a,b} \<subseteq> T; a < b; isWrite rho a;  isSeqFence rho b;
                     getLoc rho a = Some x; \<not> seqFenceInMid T rho a b;
                   \<not> writeInMid T rho a b x; \<not> seqReadInMid T rho a b x\<rbrakk> \<Longrightarrow> (a,x,b) \<in> sr T rho rf"
| seqFenceInduct : "\<lbrakk> (a,x,b') \<in> sr T rho rf; b' < b; b \<in> T; isSeqFence rho b;
                       isWrite rho a; getLoc rho a = Some x;
                       \<not> seqFenceInMid T rho b' b; \<not> writeInMid T rho b' b x; \<not> seqReadInMid T rho b' b x\<rbrakk>
                          \<Longrightarrow> (a,x,b) \<in> sr T rho rf"
|  fromSeqRead : "\<lbrakk> {a,b} \<subseteq> T; a < b; isWrite rho a;  isSeqRead rho b;
                     getLoc rho a = Some x; sameLoc rho a b; \<not> seqFenceInMid T rho a b;
                   \<not> writeInMid T rho a b x; \<not> seqReadInMid T rho a b x\<rbrakk> \<Longrightarrow> (a,x,b) \<in> sr T rho rf"
| seqFenceInductRead : "\<lbrakk> (a,x,b') \<in> sr T rho rf; b' < b; b \<in> T; isSeqRead rho b;
                       isWrite rho a; getLoc rho a = Some x; sameLoc rho a b;
                       \<not> seqFenceInMid T rho b' b; \<not> writeInMid T rho b' b x; \<not> seqReadInMid T rho b' b x\<rbrakk>
                          \<Longrightarrow> (a,x,b) \<in> sr T rho rf"
| seqFenceEmpty : "\<lbrakk> isSeqFence rho b;
                      \<not> seqFenceInMid T rho 0 b;
                   \<not> writeInMid E rho 0 b x; \<not> seqReadInMid T rho 0 b x\<rbrakk>
                          \<Longrightarrow> (0,x,b) \<in> sr T rho rf"
| seqReadEmpty : "\<lbrakk>  isSeqRead rho b;
                     getLoc rho b = Some x; \<not> seqFenceInMid T rho 0 b;
                   \<not> writeInMid T rho 0 b x; \<not> seqReadInMid T rho 0 b x\<rbrakk>
                          \<Longrightarrow> (0,x,b) \<in> sr T rho rf"

(* cw is tr \<union> sr \<union> rf *)
definition cw where
"cw E rho rf = ({(a,x,b) . (a,b) \<in> rf \<and> getLoc rho a = Some x} \<union> tr E rho rf \<union> sr E rho rf)"

(*define cocw relation meaning that a write-read relation that cannot appear in an execution of a rf *)

(* check the unqulified full-rf relations on seqcst atomics. 
    if there is a sequence fence or sequence read-write in the middle with the same location *)
inductive_set seqCocw :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
 seqCocwWrite : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; t \<in> T; a < t; t < b;
                     isWrite rho t; isSeqAtomic rho t; getLoc rho t = Some x \<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw T rho rf"
| seqCocwFence : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; t \<in> T; a < t; t < b; isSeqFence rho t;
                      (a,x,t) \<notin> cw T rho rf\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw T rho rf"
| seqCocwRead : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; t \<in> T; a < t; t < b; isSeqRead rho t;
                        sameLoc rho a t; (a,x,t) \<notin> cw T rho rf\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw T rho rf"
| seqCocwSame : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; t \<in> T; a \<noteq> t; (t,x,b) \<in> cw T rho rf\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw T rho rf"

(* in this model, since we have single thread non-determinsm of event moving,
   the cross thread model can be defined very simply. reads in a thread receiving 
     writes from another thread are in a FIFO order, the crossCocw is to rule out un-FIFO order read-writes.*)
inductive_set fifoCocw :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
nonfifoOrder : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; (c,y,d) \<in> fullRf T rho rf; a > c ; d > b\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> fifoCocw T rho rf"

inductive_set coherenceCocw :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
 coherenceCocw1 : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; (s,x,t) \<in> fullRf T rho rf;
                         a < s ; b > t; sameThread rho b t\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> coherenceCocw T rho rf"
| coherenceCocw2 : "\<lbrakk>(a,x,b) \<in> fullRf T rho rf ; (s,x,t) \<in> fullRf T rho rf;
                         a < s ; b > t; sameThread rho b t; sameThread rho a s\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> coherenceCocw T rho rf"

(* cocw for fifo order, cocw must be empty *)
definition cocwFIFO where
"cocwFIFO T rho rf = seqCocw T rho rf \<union> fifoCocw T rho rf"

(* cocw for coherence order, cocw must be empty *)
definition cocw where
"cocw T rho rf = seqCocw T rho rf \<union> coherenceCocw T rho rf"

(* defining memory loc creation property. Every mem-op must happen after its loc creates. 
inductive_set createPro :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)" where
 createBeforeUse : "\<lbrakk>a \<in> E; b \<in> E; a < b;
                       sameLoc rho a b;  isCreate rho a; \<not> isCreate rho b\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> createPro E rho"

inductive_set freePro :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)" where
 notUseAfterFree : "\<lbrakk>a \<in> E; b \<in> E; a < b;
                       sameLoc rho a b;  isFree rho b; \<not> isFree rho a\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> freePro E rho"
*)
(* the predicate is useful in proving all executions generated from a program. 
   to check if there is potential write to a location before the location exists. 
definition satCreationAndFree where
"satCreationAndFree T rho = ((\<forall> a b . a \<in> T \<and> b \<in> T \<and> sameLoc rho a b \<and> isCreate rho a
                           \<longrightarrow> (a,b) \<in> createPro T rho)
                          \<and> (\<forall> a b . a \<in> T \<and> b \<in> T \<and> sameLoc rho a b \<and> isFree rho b 
                           \<longrightarrow> (a,b) \<in> freePro T rho))"
*)
(* an execution for FIFO order must sat the predicate *)
definition satFIFO where
"satFIFO Tid T rho sbs dds rf = (rhoAssumption T rho \<and> rfAllAssumption rf rho
                           \<and> (satE Tid T rho sbs dds \<and> (cocwFIFO T rho rf = {})))"

(* an execution for coherence order must sat the predicate *)
definition sat where
"sat Tid T rho sbs dds rf = (satE Tid T rho sbs dds \<and> (cocw T rho rf = {}))"

lemma sat_le: 
  fixes t1 t2 a b x
  assumes sat1: "sat Tid T \<rho> sbs dds rf"
      and FullRFa : "(t1,x,a) \<in> fullRf T \<rho> rf"
      and FullRFb : "(t2,x,b) \<in> fullRf T \<rho> rf"
      and AgtB: "a > b"
      and sameThd : "sameThread \<rho> a b"
    shows "t1 \<ge> t2"
proof -
  from sat1 
  have COCW_empty: "cocw T \<rho> rf = {}"
    by (simp add: sat_def)
  from COCW_empty
  have Coherence_empty: "coherenceCocw T \<rho> rf = {}"
    by (simp add: cocw_def)
  from  FullRFa and  FullRFb and AgtB and sameThd and coherenceCocw1
  have B1: "t1 < t2 \<longrightarrow> (t1,a) \<in> coherenceCocw T \<rho> rf"
    by (clarsimp )
  from B1
  have B2: "(t1,a) \<notin> coherenceCocw T \<rho> rf \<longrightarrow> t1 \<ge> t2"
    by clarsimp
  from B2 and Coherence_empty
  show "t1 \<ge> t2"
    by (simp add: B2 Coherence_empty)
qed


(* define locks model *)
definition termInMid :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
     \<Rightarrow> time_type \<Rightarrow> time_type \<Rightarrow> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action \<Rightarrow> bool" where
"termInMid T rho a b e = (\<exists> t tid aid ac . t \<in> T \<and> a < t \<and> t < b
                     \<and> rho t = Some (tid,aid,ac) \<and> ac = e)"

definition termInSameTid :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
     \<Rightarrow> time_type \<Rightarrow> time_type \<Rightarrow> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action \<Rightarrow> bool" where
"termInSameTid T rho a b e = (\<exists> t tid aid ac . t \<in> T \<and> a < t \<and> t < b
                     \<and> rho t = Some (tid,aid,ac) \<and> ac = e \<and> sameThread rho a t \<and> sameThread rho t b)"

(* define the predicate for lock/unlock actions *)
definition lockProp where
"lockProp t l rho T = ((\<forall> t1 t2 . t1 \<in> T \<and> t2 \<in> T \<and> t < t1 \<and> t < t2 \<and> sameThread rho t t1 
                            \<longrightarrow> \<not> hasAction rho t1 (UnLock l) \<and> \<not> hasAction rho t2 (Lock l))
                         \<or> (\<exists> t' \<in> T . t < t' \<and> sameThread rho t t' \<and> hasAction rho t' (UnLock l)
                             \<and> \<not> termInMid T rho t t' (Lock l) \<and> \<not> termInSameTid T rho t t' (UnLock l)))"

definition locksProp where
"locksProp T rho = (\<forall> t \<in> T . (\<forall> l \<in> locks . hasAction rho t (Lock l) \<longrightarrow> lockProp t l rho T))"

(* define a valid execution that needs to satisfy,
   an execution is (Tid, T, rho, sb, rf), and the validExecution predicate defines when an execution is valid.*)
(* for FIFO execution *)
definition validExecutionFIFO where
"validExecutionFIFO Tid T rho sbs dds rf = 
  (wellformedTime T rho rf \<and> wellformedTid Tid rho \<and> wellformedSB Tid T sbs \<and> wellformedDD Tid sbs dds
   \<and> wellformedRF T rho rf \<and> rhoAssumption T rho \<and> rfAllAssumption rf rho
   \<and> allSbAllAssumptions Tid sbs rho \<and> (locksProp T rho \<and> satFIFO Tid T rho sbs dds rf))"

(* for coherence execution *)
definition validExecution where
"validExecution Tid T rho sbs dds rf = 
  (wellformedTime T rho rf \<and> wellformedTid Tid rho \<and> wellformedSB Tid T sbs 
  \<and> wellformedDD Tid sbs dds \<and> wellformedRF T rho rf \<and>
   rhoAssumption T rho \<and> rfAllAssumption rf rho \<and> allSbAllAssumptions Tid sbs rho \<and>
  (locksProp T rho \<and> sat Tid T rho sbs dds rf))"

(* define race condition *)
fun existOtherOp :: "time_type \<Rightarrow> loc_type
               \<Rightarrow> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action \<Rightarrow> bool" where
"existOtherOp key loc (ARead vol v x y) = (if loc = x then True else False)"
| "existOtherOp key loc (AWrite vol v x y) = (if loc = x then True else False)"
| "existOtherOp key loc (RMW vol v x y) = (if loc = x then True else False)"
| "existOtherOp key loc (NRead vol v x t na n) = (if key = t then False else
                                             (if loc = x then True else False))"
| "existOtherOp key loc (NWrite vol v x t na n) = (if key = t then False else
                                             (if loc = x then True else False))"
| "existOtherOp key loc x = False"

fun existOtherOpInTuple :: "time_type \<Rightarrow> loc_type
               \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option \<Rightarrow> bool" where
"existOtherOpInTuple key loc None = False"
| "existOtherOpInTuple key loc (Some (x,y,z)) = existOtherOp key loc z"

fun existOthers :: "time_type \<Rightarrow> loc_type
               \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option) \<Rightarrow> time_type set \<Rightarrow> bool" where
"existOthers key loc rho T = (\<exists> t \<in> T . existOtherOpInTuple key loc (rho t))"

fun raceDef where
"raceDef T rho = (\<exists> t1 t2 tid aid1 aid2 v v' x t n vol . t1 \<in> T \<and> t2 \<in> T
                       \<and> rho t1 = Some (tid,aid1, NRead vol v x t 1 n)
                       \<and> rho t2 = Some (tid, aid2, NRead vol v' x t n n) 
                     \<longrightarrow> existOthers t x rho {h . h \<in> T \<and> h < t2})"

(* define an observable memory on every location , every thread every time.
  for every thread, every time, every location, there is a unique time point for
    the given place to define its value.  
   i.e. a read at time t reads x from a write at time t' at thread i. so, at time t, thread i, 
     the location x, the memory is t' meaning that the value is given by the event defined at time t'
    if a thread, time, location does not have any previous time point,
    the time point is set to None meaning reading the initial value. 
*)
inductive_set seqPos :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option) \<Rightarrow> loc_type set
                  \<Rightarrow> ('tid \<times> time_type \<times> loc_type) set"
   for T :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option)"
    and Locs :: "loc_type set" where
moSeqAtomic : "\<lbrakk> t \<in> T;  isSeqAtomic rho t; getLoc rho t = Some x; x \<in> Locs;getTid rho t = Some tid\<rbrakk>
                \<Longrightarrow> (tid,t,x) \<in> seqPos T rho Locs"
| moSeqFence : "\<lbrakk> t \<in> T; isSeqFence rho t; x \<in> Locs; getTid rho t = Some tid\<rbrakk>
                \<Longrightarrow> (tid,t,x) \<in> seqPos T rho Locs"

definition hasPrevMem where
"hasPrevMem T t sb = (\<exists> t' \<in> T . (t',t) \<in> trancl sb)"

definition hasReadFrom where
"hasReadFrom T t rf = (\<exists> t' \<in> T . (t',t) \<in> rf)"

definition sameLocInMid where
"sameLocInMid T rho a b tid x =
   (\<exists> t . a < t \<and> t < b \<and>  t \<in> T \<and> getLoc rho t = Some x \<and> getTid rho t = Some tid)"

definition seqPosInMid where
"seqPosInMid T Tids rho Locs a b x =
            (\<exists> t tid . t \<in> T \<and> tid \<in> Tids \<and> a < t \<and> t < b \<and> (tid,t,x) \<in> seqPos T rho Locs)"

fun sameMemContentAux where
"sameMemContentAux (AWrite vol1 x y z) (AWrite vol2 u v w) = (if x = u \<and> y = v then True else False)"
| "sameMemContentAux (RMW vol1 x y z) (RMW vol2 u v w) = (if x = u \<and> y = v then True else False)"
| "sameMemContentAux (NWrite vol1 x y z n1 n2) (NWrite vol2 u v w n3 n4) = (if x = u \<and> y = v then True else False)"
| "sameMemContentAux x y = False"

definition sameMemContent :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option) \<Rightarrow> time_type option
         \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option) \<Rightarrow> time_type option \<Rightarrow> bool " where
"sameMemContent rho1 a rho2 b = (a = None \<and> b = None \<or>
             (\<forall> a' b' . a = Some a' \<and> b = Some b' \<longrightarrow> 
                (\<forall> tid1 aid1 tid2 aid2 ac1 ac2 . rho1 a' = Some (tid1,aid1,ac1) \<and> rho2 b' = Some (tid2,aid2,ac2)
                            \<and> sameMemContentAux ac1 ac2)))"

(* define observable memory, useful for proving mo order and
    usage in proving properties about the whole executions for a program
inductive_set observeMem :: "'tid set \<Rightarrow> time_type set
              \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option)
               \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option)
               \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option)
               \<Rightarrow> (time_type \<times> time_type) set
               \<Rightarrow> loc_type set \<Rightarrow>
                           ('tid \<times> time_type \<times> loc_type \<times> time_type) set"
for Tids :: "'tid set"
    and E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option)"
    and sbs :: "('tid \<Rightarrow> (time_type \<times> time_type) set option)"
    and dds :: "('tid \<Rightarrow> (time_type \<times> time_type) set option)"
    and rf :: "(time_type \<times> time_type) set"
     and Locs :: "loc_type set" where
 moBase1 : "\<lbrakk> tid \<in> Tids; t \<in> E; sbs tid = Some sb; \<not> hasPrevMem E t sb; getTid rho t = Some tid;
                    isFenceLike rho t; x \<in> Locs\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,0) \<in> observeMem Tids E rho sbs dds rf Locs"
| moReadBase1 : "\<lbrakk> tid \<in> Tids; t \<in> E; sbs tid = Some sb; \<not> hasPrevMem E t sb; getTid rho t = Some tid;
                      isPureRead rho t; getLoc rho t = Some x; \<not> hasReadFrom E t rf \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,0) \<in> observeMem Tids E rho sbs dds rf Locs"
| moReadBase2 : "\<lbrakk> tid \<in> Tids; t \<in> E; sbs tid = Some sb; \<not> hasPrevMem E t sb; y \<in> Locs;
                  getTid rho t = Some tid; isMemOp rho t; getLoc rho t = Some x; x \<noteq> y \<rbrakk> 
                  \<Longrightarrow> (tid,t,y,0) \<in> observeMem Tids E rho sbs dds rf Locs"
| moWriteOther1 : "\<lbrakk> tid \<in> Tids; t \<in> E; y \<in> Locs; getTid rho t = Some tid;
                    isWrite rho t; isAtomic rho t; getLoc rho t = Some x; x \<noteq> y;
                   (tid, t'', y, a) \<in> observeMem Tids E rho sbs dds rf Locs; t'' < t;
                     \<not> sameLocInMid E rho t'' t tid y;\<not> seqPosInMid E Tids rho Locs t'' t y\<rbrakk> 
                  \<Longrightarrow> (tid,t,y,a) \<in> observeMem Tids E rho sbs rf Locs"
| moWriteOther2 : "\<lbrakk> tid \<in> Tids; t \<in> E; y \<in> Locs; getTid rho t = Some tid; isAtomic rho t;
                     isWrite rho t; getLoc rho t = Some x; x \<noteq> y; (tid',t'',y) \<in> seqPos E rho Locs;
                   (tid', t'', y, a) \<in> observeMem Tids E rho sbs dds rf Locs; t'' < t;
                     \<not> sameLocInMid E rho t'' t tid y;\<not> seqPosInMid E Tids rho Locs t'' t y\<rbrakk> 
                  \<Longrightarrow> (tid,t,y,a) \<in> observeMem Tids E rho sbs dds rf Locs"
| moAtomicWrite : "\<lbrakk> tid \<in> Tids; t \<in> E; getTid rho t = Some tid;
                    isAtomic rho t; isWrite rho t; getLoc rho t = Some x \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,t) \<in> observeMem Tids E rho sbs dds rf Locs"
| moNWriteBase : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' cur num axl); num \<noteq> cur;
                     sbs tid = Some sb; \<not> hasPrevMem E t sb\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,0) \<in> observeMem Tids E rho sbs dds rf Locs"
| moNWriteNoUpdate : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' cur num axl); num \<noteq> cur;
                         (tid, t'', x, a) \<in> observeMem Tids E rho sbs dds rf Locs; t'' < t;
                         \<not> sameLocInMid E rho t'' t tid x; \<not> seqPosInMid E Tids rho Locs t'' t x \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs dds rf Locs"
| moNWriteNoUpdateSeq : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' cur num axl); num \<noteq> cur;
                         (tid', t'', x, a) \<in> observeMem Tids E rho sbs dds rf Locs; t'' < t;
                        (tid',t'',x) \<in> seqPos E rho Locs;
                         \<not> sameLocInMid E rho t'' t tid x;\<not> seqPosInMid E Tids rho Locs t'' t x \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs dds rf Locs"
| moNWriteUpdate : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' num num axl) \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,t) \<in> observeMem Tids E rho sbs dds rf Locs"
| moFenceLike1 : "\<lbrakk> tid \<in> Tids; t \<in> E; getTid rho t = Some tid;
                    isFenceLike rho t; x \<in> Locs; \<not> isSeqFence rho t;
                  (tid, t'', x, a) \<in> observeMem Tids E rho sbs dds rf Locs; t'' < t;
                   \<not> sameLocInMid E rho t'' t tid x;\<not> seqPosInMid E Tids rho Locs t'' t x\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs dds rf Locs"
| moFenceLike2 : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,ac); getTid rho t = Some tid;
                    isFenceLike rho t; \<not> isSeqFence rho t;  x \<in> Locs;
                  (tid', t'', x, a) \<in> observeMem Tids E rho sbs dds rf Locs; t'' < t;
                    (tid',t'',x) \<in> seqPos E rho Locs;
                   \<not> samLocInMid E rho t'' t tid x;\<not> seqPosInMid E Tids rho Locs t'' t x\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs rf Locs"
| moSeqFence : "\<lbrakk> tid \<in> Tids; t \<in> E; isSeqFence rho t; getTid rho t = Some tid; x \<in> Locs;
                  (t'', x, t) \<in> cw E rho rf\<rbrakk> 
                  \<Longrightarrow> (tid,t,x, t'') \<in> observeMem Tids E rho sbs rf Locs"
*)

(* One of the good things in ATRCM is that we don't need to define a modification order.
   For any execution, there exists a modification order, and we just need to retrieve that.*)
(* define the modification order for a location x*)
definition mox where
"mox T rho = {(a,x,b) . {a,b} \<subseteq> T \<and> a < b \<and> sameLoc rho a b
                  \<and> isWrite rho a \<and> isWrite rho b \<and> getLoc rho a = Some x}"

definition moUnion where
"moUnion T rho Locs = trancl {(a,b) . (\<exists> x \<in> Locs . (a,x,b) \<in> mox T rho)}"

(* define all the locations in an execution *)
definition theLocs where
"theLocs T rho = {x. (\<exists> t \<in> T . getLoc rho t = Some x)}"

(* prove that coherence are in modification order. *)
lemma SatMo :
  fixes Tid T \<rho> sb rf Locs x tid a b t1 t2
  assumes A1 : "validExecution Tid T \<rho> sbs dds rf"
  and A2 : "Locs = theLocs T \<rho>"
  and A3 : "sameThread \<rho> a b"
  and A4 : "(t1,x, a) \<in> fullRf T \<rho> rf"
  and A5 : "(t2,x, b) \<in> fullRf T \<rho> rf"
  and A6 :  "a > b"
  and A7 :  "t1 \<noteq> t2"
  and A8 : "t1 \<in> T"
  and A9 : "t2 \<in> T"
shows "(t2,x,t1) \<in> (mox T \<rho>)"
using A8 and A9
proof (simp add: mox_def)
  from A1
  have B1 : "wellformedTime T \<rho> rf"
  and B2: "wellformedTid Tid \<rho>" 
  and B3 : "wellformedSB Tid T sbs"
  and B4 : "wellformedRF T \<rho> rf"
  and B5 : "rhoAssumption T \<rho>" 
  and B6 : "rfAllAssumption rf \<rho>"
  and B7 : "allSbAllAssumptions Tid sbs \<rho>"
  and B8 : "locksProp T \<rho>" 
  and B9 : "sat Tid T \<rho> sbs dds rf"
    by (simp add: validExecution_def)+
    show "t2 < t1 \<and>
    (case \<rho> t2 of None \<Rightarrow> False | Some (xa, y, z) \<Rightarrow> (case \<rho> t1 of None \<Rightarrow> False | Some (u, v, x) \<Rightarrow> sameLocBasic z x)) \<and>
    (case \<rho> t2 of None \<Rightarrow> False | Some (xa, y, x) \<Rightarrow> isWriteBasic x) \<and>
    (case \<rho> t1 of None \<Rightarrow> False | Some (xa, y, x) \<Rightarrow> isWriteBasic x) \<and>
              (case \<rho> t2 of None \<Rightarrow> None | Some (xa, y, x) \<Rightarrow> acLoc x) = Some x"
    proof (rule_tac conjI)
      from B9 and  A4 and A5 and A6 and A3
      have LessEq : "t2 \<le> t1"
        by (simp add: sat_le)
      from A7 and LessEq
      show "t2 < t1" by simp
    next
      from A4 and A5 and A8 and A9 and B1 and B4 and B5
      have CrossSameLoc : "sameLoc \<rho> t2 t1"
        by (rule_tac T = T and \<rho> = \<rho> and rf = rf and s = t2
                       and a = b and t = t1 and b = a and x = x in sameLocTwoInFullRf,clarsimp+)
      from A4 and B1 and B4 and B5
      have AInT : "a \<in> T"
        by (simp add: fullRfReadInSet)
      from A5 and B1 and B4 and B5
      have BInT : "b \<in> T"
        by (simp add: fullRfReadInSet)
      from A4 and A8 and AInT and B1 and B4 and B5
      have IsWriteT1 : "isWrite \<rho> t1"
        by (rule_tac T = T and \<rho> = \<rho> and rf = rf
                       and a = t1 and b = a and x = x in isWriteInFullRf,clarsimp+)
      from A5 and A9 and BInT and B1 and B4 and B5
      have IsWriteT2 : "isWrite \<rho> t2"
        by (rule_tac T = T and \<rho> = \<rho> and rf = rf
                       and a = t2 and b = b and x = x in isWriteInFullRf,clarsimp+)
      from A5 and A9 and BInT and B1 and B4 and B5
      have GetLocT2 : "getLoc \<rho> b = Some x"
        by (rule_tac T = T and \<rho> = \<rho> and rf = rf
                       and a = t2 and b = b and x = x in locXInFullRf,clarsimp+)
      from A5 and A9 and BInT and B1 and B4 and B5
      have sameLocT2 : "sameLoc \<rho> t2 b"
        by (rule_tac T = T and \<rho> = \<rho> and rf = rf
                       and a = t2 and b = b and x = x in sameLocInFullRf,clarsimp+)
      from A4 and A5 and A8 and A9 and B1 and B4 and B5
      have CrossSameLoc : "sameLoc \<rho> t2 t1"
        by (rule_tac T = T and \<rho> = \<rho> and rf = rf and s = t2
                       and a = b and t = t1 and b = a and x = x in sameLocTwoInFullRf,clarsimp+)
      from A4 and A5 and A8 and A9 and B1 and B4 and B5 and CrossSameLoc
              and IsWriteT1 and IsWriteT2 and GetLocT2 and sameLocT2
      show "(case \<rho> t2 of None \<Rightarrow> False | Some (xa, y, z) \<Rightarrow>
                (case \<rho> t1 of None \<Rightarrow> False | Some (u, v, x) \<Rightarrow> sameLocBasic z x)) \<and>
    (case \<rho> t2 of None \<Rightarrow> False | Some (xa, y, x) \<Rightarrow> isWriteBasic x) \<and>
    (case \<rho> t1 of None \<Rightarrow> False | Some (xa, y, x) \<Rightarrow> isWriteBasic x)
                \<and> (case \<rho> t2 of None \<Rightarrow> None | Some (xa, y, x) \<Rightarrow> acLoc x) = Some x"
        apply (case_tac "\<rho> t2")
         apply (simp add: wellformedTime_def rhoAssumption_def, clarsimp+)
        apply (case_tac "\<rho> t1")
         apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)
        apply (case_tac "\<rho> b")
         apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)
        apply clarsimp
        apply (case_tac "acLoc ba")
         apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)
        apply clarsimp
        apply (case_tac "acLoc baa")
         apply (simp add: wellformedTime_def wellformedRF_def rhoAssumption_def)
        apply clarsimp
        apply (case_tac "af = x")
        by clarsimp+
    qed
  qed


end

end