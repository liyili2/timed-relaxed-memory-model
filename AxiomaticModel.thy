theory AxiomaticModel
imports Main
begin

(* locks in the SC11 model is strange, since it locks a memory location which is impossible to implement.
   the division between a atomic location and a non-atomic location in an execution is strange \
  hypothetical_release_sequence definition is strange, and why rmw release can break the same thread requirement? 
  synchorniaze-with relation too complicated and unnecessary 
   likely that if a read of release do not read a value from a write acquire, then the SC11 model rejects
   however, consider the following program:
   a: write x b: fence release, thread 2: c: read x d: fence acquire, can c read value a,
    the C11 model does not forbid c reading value from a,
    happens-before definition is too restritive. 
    if we require happens-before writes to satisfy modification order, then the follow program is not valid:
     T1                T2
    x = 1             y=1
    a = y//a = 0      b=x//b=0
    even if relaxed flag is given in this case, this program is disallowed according to the C11 model defined by Batty,
    which is wrong

    In a sense, the SC11 model also says very little about relaxed atomics and any relations that are not
      in the synchronized-with relations.
     For example, if we have
     T1                          T2
    x-relaxed = 1                z-relaxed = 2
                                 y-release = 1
    a = y-acquired //a = 0       b=x-relaxed   //b=0
    c = z-relaxed //c = 0

    it is also a valid program, but the SC11 model does not talk about thing about the behavior of the
    program if a gets value 1, because it is not in the sw-relation.

     T1                          T2                        T3
    x-relaxed = 1                z-release = 2
                                 y-release = 1
    a = y-acquired //a = 0       b=x-relaxed   //b=1
    c = z-acquired //c = 2

  why need to focus on atomic/non-atomic memory locations. 
   Does non-atomic memory operations do not need to follow modification order?

   does sc read must read value from sc write? 
  *)





datatype order = Relaxed | Release | Acquire | AcqRel | SeqCst

datatype ('aid,  'val, 'loc, 'lock,'name,'key) action =
   ARead bool 'val 'loc order "'aid list" | AWrite bool 'val 'loc order "'aid list" | RMW bool 'val 'loc order "'aid list"
  | NRead bool 'val 'loc 'aid nat nat "'aid list" | NWrite bool 'val 'loc 'aid nat nat "'aid list"
  | Fence order | Lock 'lock | UnLock 'lock
  | CallFence 'name 'key
  | ControlFence
  | Create 'loc
  | Free 'loc

fun isWrite where
 "isWrite (AWrite vol x y z al) = True"
| "isWrite (RMW vol x y z al) = True"
| "isWrite (NWrite vol x y z u v al) = True"
| "isWrite x = False"

fun isAtomicWrite where
 "isAtomicWrite (AWrite vol x y z al) = True"
| "isAtomicWrite (RMW vol x y z al) = True"
| "isAtomicWrite x = False"

fun isWriteInTuple where
 "isWriteInTuple None = False"
| "isWriteInTuple (Some (x,y,z)) = isWrite z"

fun isRead where
"isRead (ARead vol a x y al) = True"
| "isRead (RMW vol x y z al) = True"
| "isRead (NRead vol a x y u v al) = True"
| "isRead x = False"

fun isReadInTuple where
"isReadInTuple (Some (x,y,z)) = isRead z"
| "isReadInTuple None = False"

fun isPureRead where
"isPureRead (ARead vol a x y al) = True"
| "isPureRead (NRead vol a x y u v al) = True"
| "isPureRead x = False"

fun isPureReadInTuple where
"isPureReadInTuple (Some (x,y,z)) = isPureRead z"
| "isPureReadInTuple None = False"

fun isCreate where
"isCreate (Some (x,y,Create l)) = True"
| "isCreate x = False"

fun isFree where
"isFree (Some (x,y,Free l)) = True"
| "isFree x = False"

fun isRMW where
"isRMW (RMW vol x y z al) = True"
| "isRMW x = False"

fun isRMWInTuple where
"isRMWInTuple None = False"
| "isRMWInTuple (Some (x,y,z)) = isRMW z"

fun isMemOp where
 "isMemOp x = (isWrite x \<or> isPureRead x)"

fun isMemOpInTuple where
"isMemOpInTuple None = False"
| "isMemOpInTuple (Some (x,y,z)) = isMemOp z"

fun isAtomic where
 "isAtomic (AWrite vol x y r al) = True"
| "isAtomic (RMW vol x y r al) = True"
| "isAtomic (ARead vol a x r al) = True"
| "isAtomic x = False"

definition isAtomicInTuple where
"isAtomicInTuple rho a = (case rho a of None \<Rightarrow> False | Some (x,y,z) \<Rightarrow> isAtomic z)"

fun isVolatile where
"isVolatile (ARead vol a x y al) = vol"
| "isVolatile (RMW vol x y z al) = vol"
| "isVolatile (AWrite vol x y z al) = vol"
| "isVolatile (NRead vol a x y u v al) = vol"
| "isVolatile (NWrite vol x y z u v al) = vol"
| "isVolatile x = False"

fun isSeqAtomic where
 "isSeqAtomic (AWrite vol x y SeqCst al) = True"
| "isSeqAtomic (RMW vol x y SeqCst al) = True"
| "isSeqAtomic (ARead vol a x SeqCst al) = True"
| "isSeqAtomic x = False"

fun isSeqAtomicInTuple where
"isSeqAtomicInTuple (Some (x,y,z)) = isSeqAtomic z"
| "isSeqAtomicInTuple None = False"

fun isSeqFence where
"isSeqFence (Some (x,y,Fence SeqCst)) = True"
| "isSeqFence x = False"

fun hasSeqInTuple where
 "hasSeqInTuple x = (isSeqAtomicInTuple x \<or> isSeqFence x)"

fun isRealFence where
"isRealFence (Fence r) = True"
| "isRealFence x = False"

definition isRealFenceInTuple where
"isRealFenceInTuple rho x = (case rho x of None \<Rightarrow> False | (Some (u,v,w)) \<Rightarrow> isRealFence w)"

fun isFenceLike where
"isFenceLike (Fence x) = True"
| "isFenceLike (Lock l) = True"
| "isFenceLike (UnLock l) = True"
| "isFenceLike (CallFence a b) = True"
| "isFenceLike (ControlFence) = True"
| "isFenceLike (Create l) = True"
| "isFenceLike (Free l) = True"
| "isFenceLike x = False"

fun isFenceLikeTuple where
"isFenceLikeTuple None = False"
| "isFenceLikeTuple (Some (x,y,z)) = isFenceLike z"

(* get the memory location of a read-write operation, and check if two ops have the same locations *)
fun acLoc where
"acLoc (ARead vol a x y al) = Some x"
| "acLoc (RMW vol x y z al) = Some y"
| "acLoc (AWrite vol x y z al) = Some y"
| "acLoc (NRead vol a x y u v al) = Some x"
| "acLoc (NWrite vol x y z u v al) = Some y"
| "acLoc (Create l) = Some l"
| "acLoc x = None"

fun getLocInTuple where
"getLocInTuple None = None"
| "getLocInTuple (Some (x,y,z)) = acLoc z"

fun isTheLoc where
"isTheLoc a loc = (case acLoc a of Some x \<Rightarrow> x = loc | _ \<Rightarrow> False)"

fun isTheLocInTuple where
"isTheLocInTuple None loc = False"
| "isTheLocInTuple (Some (x,y,z)) loc = isTheLoc z loc"

fun sameLoc where
"sameLoc a b  = (case acLoc a of Some x \<Rightarrow>
                       (case acLoc b of Some y \<Rightarrow> if x = y then True else False | _ \<Rightarrow> False)
                     | _ \<Rightarrow> False)"

fun sameLocInTuple where
"sameLocInTuple rho a b = (case rho a of None \<Rightarrow> False
                            | Some (x,y,z) \<Rightarrow> (case rho b of None \<Rightarrow> False
                                  | Some (u,v,w) \<Rightarrow> sameLoc z w))"

fun sameThread where
"sameThread rho a b = (case rho a of Some (x,y,z) \<Rightarrow>
                    (case rho b of Some (u,v,w) \<Rightarrow> if x = u then True else False
                                 | _ \<Rightarrow> False)
                       | _ \<Rightarrow> False)"

(* get the value of a read-write operation and check if two ops have the same value*)
fun acVal where
"acVal (ARead vol a x y al) = Some a"
| "acVal (RMW vol x y z al) = Some x"
| "acVal (AWrite vol x y z al) = Some x"
| "acVal (NRead vol a x y u v al) = Some a"
| "acVal (NWrite vol x y z u v al) = Some x"
| "acVal x = None"

fun geValInTuple where
"geValInTuple None = None"
| "geValInTuple (Some (x,y,z)) = acVal z"

fun sameVal where
"sameVal a b  = (case acVal a of Some x \<Rightarrow>
                       (case acVal b of Some y \<Rightarrow> if x = y then True else False | _ \<Rightarrow> False)
                     | _ \<Rightarrow> False)"

fun sameValInTuple where
"sameValInTuple rho a b = (case rho a of None \<Rightarrow> False
                            | Some (x,y,z) \<Rightarrow> (case rho b of None \<Rightarrow> False
                                  | Some (u,v,w) \<Rightarrow> sameVal z w))"

fun acOrder where
"acOrder (ARead vol x y z al) = Some z"
| "acOrder (AWrite vol x y z al) = Some z"
| "acOrder (RMW vol x y z al) = Some z"
| "acOrder (Fence x) = Some x"
| "acOrder x = None"

definition hasAtLeastAcqRel where
"hasAtLeastAcqRel ac = (case acOrder ac of None \<Rightarrow> False
                                         | Some z \<Rightarrow> if z = Relaxed then False else True)"

definition atLeastAcq where
"atLeastAcq ac = (case acOrder ac of None \<Rightarrow> False | Some z \<Rightarrow> if z = Relaxed \<or> z = Release then False else True)"

definition atLeastRel where
"atLeastRel ac = (case acOrder ac of None \<Rightarrow> False | Some z \<Rightarrow> if z = Relaxed \<or> z = Acquire then False else True)"

definition isRelWrite where
"isRelWrite rho x = (case rho x of None \<Rightarrow> False | Some (u,v,w)
                         \<Rightarrow> (isWrite w \<or> isRealFence w) \<and> atLeastRel w)"

definition isAcqRead where
"isAcqRead rho x = (case rho x of None \<Rightarrow> False | Some (u,v,w)
                         \<Rightarrow> (isRead w \<or> isRealFence w) \<and> atLeastAcq w)"


fun hasAction where
"hasAction (Some (u,v,w)) y = (if w = y then True else False)"
| "hasAction None y = False"


definition toLocalExecution where
"toLocalExecution tid f = (\<lambda> x . (case f x of None \<Rightarrow> None | Some (a,b) \<Rightarrow> if a = tid then Some b else None))"

definition getAllTids where
"getAllTids f = {a . \<exists> b . (a,b) \<in> range f}"

fun getDepSet where
"getDepSet (ARead vol a x y al) = Some al"
| "getDepSet (RMW vol x y z al) = Some al"
| "getDepSet (AWrite vol x y z al) = Some al"
| "getDepSet (NRead vol a x y u v al) = Some al"
| "getDepSet (NWrite vol x y z u v al) = Some al"
| "getDepSet x = None"

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

definition wellformedTime :: "time_type set \<Rightarrow>
                    (time_type \<times> time_type) set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"wellformedTime T rf rho = (T \<subseteq> times \<and> (\<forall> t1 t2 . (t1,t2) \<in> rf \<longrightarrow> t1 \<in> T \<and> t2 \<in> T)
                            \<and> (\<forall> t act . rho t = Some act \<longrightarrow> t \<in> T))"

definition wellformedTid :: "'tid set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"wellformedTid Tid rho = (Tid \<subseteq> threads \<and>
                            (\<forall> t tid aid ac . rho t = Some (tid,aid,ac) \<longrightarrow> tid \<in> Tid))"

definition wellformedSB :: "'tid set \<Rightarrow> time_type set \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option) \<Rightarrow> bool" where
"wellformedSB Tid T sb = (\<forall> t S a b . sb t = Some S \<and> (a,b) \<in> S \<longrightarrow> t \<in> Tid \<and> a \<in> T \<and> b \<in> T)"

definition sbAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"sbAssumption sb rho = (\<forall> a b tid aid1 ac1 aid2 ac2 . (a,b) \<in> sb \<longrightarrow>
           rho a = Some (tid, aid1,ac1) \<and> rho b = Some (tid, aid2,ac2)
             \<and> aid1 < aid2 \<and> \<not> (\<exists> z . aid1 < z \<and> z < aid2))"

definition sbNReadAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"sbNReadAssumption sb rho = (\<forall> a b tid1 aid1  tid2 aid2 x t na nb n v v' al vol . (a,b) \<in> trancl sb \<and>
           rho a = Some (tid1, aid1, NRead vol v x t na n al) \<and> rho b = Some (tid2,aid2,NRead vol v' x t nb n al)
             \<and> a < b \<longrightarrow> na < nb)"

definition sbNWriteAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"sbNWriteAssumption sb rho = (\<forall> a b tid1 aid1  tid2 aid2 v1 v2 x t na nb n al vol . (a,b) \<in> trancl sb \<and>
           rho a = Some (tid1, aid1, NWrite vol v1 x t na n al) \<and> rho b = Some (tid2,aid2,NWrite vol v2 x t nb n al)
             \<and> a < b \<longrightarrow> na < nb)"

definition sbAllAssumptions where
"sbAllAssumptions sb rho = (sbAssumption sb rho \<and> sbNReadAssumption sb rho \<and> sbNWriteAssumption sb rho)"

definition rhoAssumption :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rhoAssumption rho = (\<forall> t t1 tid aid ac tid1 ac1 . t \<in> times \<and> t1 \<in> times \<and> rho t = Some (tid, aid, ac)
                      \<and> rho t1 = Some (tid1, aid, ac1) \<longrightarrow> t = t1)"

definition rfAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rfAssumption rf rho = ((\<forall> a b tid1 aid1 ac1 tid2 aid2 ac2 . (a,b) \<in> rf
        \<longrightarrow> rho a = Some (tid1, aid1, ac1) \<and> rho b = Some (tid2, aid2, ac2)
           \<and> isWrite ac1 \<and> isRead ac2 \<and> sameLoc ac1 ac2 \<and> a < b \<and> sameVal ac1 ac2) \<and>
          (\<forall> a1 a2 b .  (a1,b) \<in> rf \<and> (a2,b) \<in> rf \<longrightarrow> (a1 = a2)))"

definition rfNWriteAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rfNWriteAssumption rf rho = (\<forall> a b tid1 aid1 v x t na n al vol . (a,b) \<in> rf
        \<and> rho a = Some (tid1, aid1, NWrite vol v x t na n al)  \<longrightarrow> na = n)"

definition rfNReadAssumption :: "(time_type \<times> time_type) set
                          \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool" where
"rfNReadAssumption rf rho = (\<forall> a b tid1 aid1 x t na n v al vol . (a,b) \<in> rf
        \<and> rho b = Some (tid1, aid1, NRead vol v x t na n al)  \<longrightarrow> na = n)"

definition rfAllAssumption where
"rfAllAssumption rf rho = (rfAssumption rf rho \<and> rfNWriteAssumption rf rho \<and> rfNReadAssumption rf rho)"

(* defining a relation collecting the sb-position relation on all fence like ops in each thread *)
inductive_set fenceRelation :: "time_type set 
    \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  fenceLikeRule : "\<lbrakk> (a,b) \<in> trancl sb;
               isFenceLikeTuple (rho a); isFenceLikeTuple (rho b)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> fenceRelation E rho sb"

(* defining control dependence,
   control dependence happens when there is a binary branching inst in the time of the op. 
    no writes can go cross a control fence, but reads can go cross a control fence if there is no
    data dependency in the conditions of the branching *)
inductive_set controldep :: "time_type set 
    \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  controlWriteRule1: "\<lbrakk> (a,b) \<in> trancl sb;
             rho b = Some (tid, aid, ControlFence); {a,b} \<subseteq> E; isWriteInTuple (rho a)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> controldep E rho sb"
| controlWriteRule2: "\<lbrakk> (a,b) \<in> trancl sb;
             rho a = Some (tid, aid, ControlFence); {a,b} \<subseteq> E; isWriteInTuple (rho b)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> controldep E rho sb"

(* call dependency is like a acqrel fence in each thread to indicate that
    a memory op cannot go cross a function call (lib call). 
   this fence is useful in doing function call optimization
   i.e. declaring a function is an inline function *)
inductive_set calldep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  callFence1: "\<lbrakk> (a,b) \<in> trancl sb; rho b = Some (tid,aid,CallFence name key); {a,b} \<subseteq> E;
                    isMemOpInTuple (rho a)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| callFence2: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tid,aid,CallFence name key); {a,b} \<subseteq> E;
                isMemOpInTuple (rho b)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| lockRule1: "\<lbrakk> (a,b) \<in> trancl sb; rho b = Some (tid, aid, (Lock l)); {a,b} \<subseteq> E;
                isMemOpInTuple (rho a)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| lockRule2: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tid, aid, (Lock l)); {a,b} \<subseteq> E;
                isMemOpInTuple (rho b)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| unLockRule1: "\<lbrakk> (a,b) \<in> trancl sb; rho b = Some (tid,aid,(UnLock l)); {a,b} \<subseteq> E;
                   isMemOpInTuple (rho a)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"
| unLockRule2: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tid,aid,(UnLock l)); {a,b} \<subseteq> E;
                    isMemOpInTuple (rho b)\<rbrakk>
           \<Longrightarrow> (a,b) \<in> calldep E rho sb"

(* volatile dependency in all threads *)
inductive_set volatileDep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
 volDef : "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tida,aida,aca);
                    (rho b) = Some (tidb,aidb,acb); {a,b} \<subseteq> E; isVolatile aca; isVolatile acb \<rbrakk>
           \<Longrightarrow> (a,b) \<in> volatileDep E rho sb"

(* define data dependency in all threads *)
inductive_set addDataDep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
 additionalDep : "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tida,aida,aca);
                    (rho b) = Some (tidb,aidb,acb); {a,b} \<subseteq> E; getDepSet acb = Some al; aida \<in> set al\<rbrakk>
           \<Longrightarrow> (a,b) \<in> addDataDep E rho sb"

inductive_set basicDatadep :: "time_type set  \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" 
  where
  wwdependence: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tida,aida,aca);
                    (rho b) = Some (tidb,aidb,acb); {a,b} \<subseteq> E; isWrite aca; isWrite acb; sameLoc aca acb\<rbrakk>
           \<Longrightarrow> (a,b) \<in> basicDatadep E rho sb"
| rwdependence: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tida,aida,aca);
              rho b = Some (tidb,aidb,acb); {a,b} \<subseteq> E; isRead aca; \<not> isRMW aca; isWrite acb; sameLoc aca acb\<rbrakk>
           \<Longrightarrow> (a,b) \<in> basicDatadep E rho sb"
| wrdependence: "\<lbrakk> (a,b) \<in> trancl sb; rho a = Some (tida,aida,aca);
              rho b = Some (tidb,aidb,acb); {a,b} \<subseteq> E; isWrite aca; isRead acb; \<not> isRMW acb; sameLoc aca acb\<rbrakk>
           \<Longrightarrow> (a,b) \<in> basicDatadep E rho sb"

definition datadep where
"datadep E rho sb = (addDataDep E rho sb) \<union> basicDatadep E rho sb"

(* memory ordering dependency in a single thread *)
inductive_set singleorderdep :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: " (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" where
  readAcqRule: "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1, (ARead vol val x or axl));
                      or = Acquire;  {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| readSeqRule1: "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1, (ARead vol val x or axl ));
                      or = SeqCst;  {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| readSeqRule2: "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1, (ARead vol val x or axl));
                      or = SeqCst;  {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| writeRelRule: "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,AWrite vol v x or axl);
                       or = Release; {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| writeSeqRule1: "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,AWrite vol v x or axl);
                       or = SeqCst; {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| writeSeqRule2: "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1,AWrite vol v x or axl);
                       or = SeqCst; {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| rmwAcqRule: "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1, RMW vol v x or axl);
                   or = Acquire; {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| rmwRelRule: "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,RMW vol v x or axl);
                    or = Release; {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| rmwAllRule1: "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,RMW vol v x or axl);
                       or = AcqRel \<or> or = SeqCst; {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| rmwAllRule2: "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1,RMW vol v x or axl);
                     or = AcqRel \<or> or = SeqCst; {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| acqFence1 : "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1,Fence Acquire); {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| acqFence2 : "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,Fence Acquire); {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| relFence1 : "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,Fence Release); {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| relFence2 : "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1,Fence Release); {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| acqRelFence1 : "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,Fence AcqRel); {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| acqRelFence2 : "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1,Fence AcqRel); {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| seqFence1 : "\<lbrakk> (a,b) \<in> trancl sb; (rho b) = Some (tid1,aid1,Fence SeqCst); {a,b} \<subseteq> E;
                  rho a = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"
| seqFence2 : "\<lbrakk> (a,b) \<in> trancl sb; (rho a) = Some (tid1,aid1,Fence SeqCst); {a,b} \<subseteq> E;
                  rho b = Some (tid2,aid2,ac2); isWrite ac2 \<or> isRead ac2\<rbrakk>
           \<Longrightarrow> (a,b) \<in> singleorderdep E rho sb"


(* define available after relation, it is a combination of all single thread dependency. *)
inductive_set af :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and sb :: "(time_type \<times> time_type) set" where
 callRule : "(a,b) \<in> calldep E rho sb \<Longrightarrow> (a,b) \<in> af E rho sb"
| controlRule : "(a,b) \<in> controldep E rho sb \<Longrightarrow> (a,b) \<in> af E rho sb"
| dataRule : "(a,b) \<in> datadep E rho sb \<Longrightarrow> (a,b) \<in> af E rho sb"
| volatileRule : "(a,b) \<in> volatileDep E rho sb \<Longrightarrow> (a,b) \<in> af E rho sb"
| singleOrderRule : "(a,b) \<in> singleorderdep E rho sb \<Longrightarrow> (a,b) \<in> af E rho sb"

(* a complete set for af, every dependency has an clear edge from one event to the other,
   these edges can act as an indication of which event should happen early than another event.
   if there is no edges between two events, it means that either one can happen early, so 
   it essentially means that there are two edges connecting this two. 
   this process tries to add all two edges on no connected events. *)
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

(* get a set of initial state, where an execution can start with such time *)
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

fun selectTimeByTid where
"selectTimeByTid tid E rho = {t . t \<in> E \<and> (\<exists> tid' aid ac . rho t = Some (tid',aid,ac) \<and> tid = tid')}"

(* assume that rho satisfy the rho assumption *)
definition satE :: "'tid set \<Rightarrow>
          time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
            ('tid \<Rightarrow> (time_type \<times> time_type) set option) \<Rightarrow> bool" where
"satE Tid E rho pos = (\<forall> tid \<in> Tid . (\<forall> po . (pos tid) = Some po \<and> sbAllAssumptions po rho \<longrightarrow>
                   isAllowedSingleExecution (selectTimeByTid tid E rho) rho (the (pos tid))))"

definition localTimes where
"localTimes ts f tid = {x . x \<in> ts \<and> (\<exists> h . f x = Some (tid, h))}"

(* defining seqcst fence in the middle of two points *)
definition seqFenceInMid where
"seqFenceInMid T rho a b = (\<exists> t .
                        t \<in> T \<and> a < t \<and> t < b \<and> isSeqFence (rho t))"

definition seqReadInMid where
"seqReadInMid T rho a b x = (\<exists> t .
                        t \<in> T \<and> a < t \<and> t < b \<and> isPureReadInTuple (rho t)
                        \<and> isSeqAtomicInTuple (rho t) \<and> getLocInTuple (rho t) = Some x)"

definition isSeqRead where
"isSeqRead rho a = (isPureReadInTuple (rho a) \<and> isSeqAtomicInTuple (rho a))"

(* defining a write with the same location in the middle of two points *)
definition writeInMid where
"writeInMid T rho a b loc = (\<exists> t .
                        t \<in> T \<and> a < t \<and> t < b \<and> isTheLocInTuple (rho t) loc \<and> isWriteInTuple (rho t))"

(* defining a write with the same location in the middle of two points *)
definition sameThreadWriteInMid where
"sameThreadWriteInMid T rho a b loc = (\<exists> t .
                        t \<in> T \<and> a < t \<and> t < b \<and> isTheLocInTuple (rho t) loc \<and> isWriteInTuple (rho t)
                          \<and> sameThread rho t b)"

(* starting defining dependency crossing different threads 
   we first define cw relation. cw relation is basically rf + seq fence relation.
   In the model, the seq fence sychronizes all memory values for all locations.
   So, a read from a write crossing a seq fence can be viewed as a read from a seq-fence, and 
       a seq-fence from a write *)
inductive_set sr :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> loc_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
  fromSeqFence : "\<lbrakk> a < b; isWriteInTuple (rho a);  isSeqFence (rho b);
                     getLocInTuple (rho a) = Some x; \<not> seqFenceInMid E rho a b;
                   \<not> writeInMid E rho a b x; \<not> seqReadInMid E rho a b x\<rbrakk> \<Longrightarrow> (a,x,b) \<in> sr E rho rf"
| seqFenceInduct : "\<lbrakk> (a,x,b') \<in> sr E rho rf; b' < b; b \<in> E; isSeqFence (rho b);
                       isWriteInTuple (rho a); getLocInTuple (rho a) = Some x;
                       \<not> seqFenceInMid E rho b' b; \<not> writeInMid E rho b' b x; \<not> seqReadInMid E rho b' b x\<rbrakk>
                          \<Longrightarrow> (a,x,b) \<in> sr E rho rf"
| seqFenceEmpty : "\<lbrakk> isSeqFence (rho b);
                      \<not> seqFenceInMid E rho 0 b;
                   \<not> writeInMid E rho 0 b x; \<not> seqReadInMid E rho 0 b x\<rbrakk>
                          \<Longrightarrow> (0,x,b) \<in> sr E rho rf"
| seqReadEmpty : "\<lbrakk>  isSeqRead rho b;
                     getLocInTuple (rho b) = Some x; \<not> seqFenceInMid E rho 0 b;
                   \<not> writeInMid E rho 0 b x; \<not> seqReadInMid E rho 0 b x\<rbrakk>
                          \<Longrightarrow> (0,x,b) \<in> sr E rho rf"
| fromSeqRead : "\<lbrakk> a < b; isWriteInTuple (rho a);  isSeqRead rho b; sameLocInTuple rho a b;
                     getLocInTuple (rho a) = Some x; \<not> seqFenceInMid E rho a b;
                   \<not> writeInMid E rho a b x; \<not> seqReadInMid E rho a b x\<rbrakk> \<Longrightarrow> (a,x,b) \<in> sr E rho rf"
| seqReadInduct : "\<lbrakk> (a,x,b') \<in> sr E rho rf; b' < b; b \<in> E; isSeqRead rho b;
                       isWriteInTuple (rho a); getLocInTuple (rho a) = Some x; sameLocInTuple rho a b;
                       \<not> seqFenceInMid E rho b' b; \<not> writeInMid E rho b' b x; \<not> seqReadInMid E rho b' b x\<rbrakk>
                          \<Longrightarrow> (a,x,b) \<in> sr E rho rf"


inductive_set cw :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> loc_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
 inrf : "\<lbrakk> (a,b) \<in> rf ; getLocInTuple (rho a) = Some x\<rbrakk> \<Longrightarrow> (a,x,b) \<in> cw E rho rf"
| insr : "\<lbrakk> (\<forall> t . (t ,b) \<notin> rf) ; (a,x,b') \<in> sr E rho rf; b' < b; b \<in> E;
               isReadInTuple (rho b); \<not> sameThreadWriteInMid E rho b' b x\<rbrakk> \<Longrightarrow> (a,x,b) \<in> cw E rho rf"
| inSingle : "\<lbrakk>(\<forall> t . (t ,b) \<notin> rf) ; a  < b; b \<in> E; a \<in> E;
                isWriteInTuple (rho a); sameThread rho a b;
               isReadInTuple (rho b); \<not> seqFenceInMid E rho a b; \<not> seqReadInMid E rho a b x;
               \<not> sameThreadWriteInMid E rho a b x\<rbrakk>
                          \<Longrightarrow> (a,x,b) \<in> cw E rho rf"
| inempty : "\<lbrakk>(\<forall> t . (t ,b) \<notin> rf) ; b \<in> E;
               isReadInTuple (rho b); \<not> seqFenceInMid E rho 0 b; \<not> seqReadInMid E rho 0 b x;
               \<not> sameThreadWriteInMid E rho 0 b x\<rbrakk>
                          \<Longrightarrow> (0,x,b) \<in> cw E rho rf"


(*define cocw relation meaning that a write-read relation that cannot appear in an execution of a rf *)

(* if there is a sequence fence or sequence read-write in the middle with the same location *)
inductive_set seqCocw :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
 seqCocw1 : "\<lbrakk>(a,b) \<in> rf ; rho t = Some (tid,aid, Fence SeqCst); getLocInTuple (rho a) = Some x;
                (a,x,t) \<notin> cw E rho rf; t > a ; t < b\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw E rho rf"
| seqCocw2 : "\<lbrakk>(a,b) \<in> rf ; rho t = Some (tid,aid, ac); getLocInTuple (rho a) = Some x;
                isSeqAtomic ac; (a,x,t) \<notin> cw E rho rf; t > a ; t < b\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw E rho rf"
| seqCocw3 : "\<lbrakk>(a,b) \<in> rf ; rho t = Some (tid,aid, ac); getLocInTuple (rho a) = Some x;
                isSeqAtomic ac; isWrite ac; t > a ; t < b\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> seqCocw E rho rf"

(* in this model, since we have single thread non-determinsm of event moving,
   the cross thread model can be defined very simply. reads in a thread receiving 
     writes from another thread are in a FIFO order, the crossCocw is to rule out un-FIFO order read-writes.*)
inductive_set crossCocw :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow>
              (time_type \<times> time_type) set
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
    and rf :: "(time_type \<times> time_type) set" where
 crossCocw1 : "\<lbrakk>(a,x,b) \<in> cw E rho rf \<and>
                 (\<exists> t t' . t \<in> E \<and> t' \<in> E \<and> t' < a \<and> b < t \<and> sameThread rho b t
                     \<and> (t',x,t) \<in> cw E rho rf)\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> crossCocw E rho rf"
| crossCocw2 : "\<lbrakk>(a,x,b) \<in> cw E rho rf \<and>
                 (\<exists> t t' . t \<in> E \<and> t' \<in> E \<and> a < t' \<and> t < b \<and> sameThread rho b t
                     \<and> (t',x,t) \<in> cw E rho rf)\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> crossCocw E rho rf"

definition cocw where
"cocw E rho rf = seqCocw E rho rf \<union> crossCocw E rho rf"

(* defining memory loc creation property. Every mem-op must happen after its loc creates. *)
inductive_set createPro :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)" where
 createBeforeUse : "\<lbrakk>a \<in> E; b \<in> E; a < b;
                       sameLocInTuple rho a b;  isCreate (rho a); \<not> isCreate (rho b)\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> createPro E rho"

inductive_set freePro :: "time_type set \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
          \<Rightarrow> (time_type \<times> time_type) set"
  for E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                   (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)" where
 notUseAfterFree : "\<lbrakk>a \<in> E; b \<in> E; a < b;
                       sameLocInTuple rho a b;  isFree (rho b); \<not> isFree (rho a)\<rbrakk> 
                    \<Longrightarrow> (a,b) \<in> freePro E rho"

definition satCreationAndFree where
"satCreationAndFree T rho = ((\<forall> a b . a \<in> T \<and> b \<in> T \<and> sameLocInTuple rho a b \<and> isCreate (rho a) 
                           \<longrightarrow> (a,b) \<in> createPro T rho)
                          \<and> (\<forall> a b . a \<in> T \<and> b \<in> T \<and> sameLocInTuple rho a b \<and> isFree (rho b) 
                           \<longrightarrow> (a,b) \<in> freePro T rho))"

definition sat where
"sat Tid T rho po rf = (rhoAssumption rho \<and> rfAllAssumption rf rho
                    \<longrightarrow> (satCreationAndFree T rho \<and> satE Tid T rho po \<and> (\<forall> (a,b) \<in> rf . (a,b) \<notin> cocw T rho rf)))"

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

definition lockProp where
"lockProp t l rho T = ((\<forall> t1 t2 . t1 \<in> T \<and> t2 \<in> T \<and> t < t1 \<and> t < t2 \<and> sameThread rho t t1 
                            \<longrightarrow> \<not> hasAction (rho t1) (UnLock l) \<and> \<not> hasAction (rho t2) (Lock l))
                         \<or> (\<exists> t' \<in> T . t < t' \<and> sameThread rho t t' \<and> hasAction (rho t') (UnLock l)
                             \<and> \<not> termInMid T rho t t' (Lock l) \<and> \<not> termInSameTid T rho t t' (UnLock l)))"

definition locksProp where
"locksProp T rho = (\<forall> t \<in> T . (\<forall> l \<in> locks . hasAction (rho t) (Lock l) \<longrightarrow> lockProp t l rho T))"

(* define a valid execution that needs to satisfy,
   an execution is (Tid, T, rho, sb, rf), and the validExecution predicate defines when an execution is valid.*)

definition validExecution where
"validExecution Tid T rho sb rf = 
  (wellformedTime T rf rho \<and> wellformedTid Tid rho \<and> wellformedSB Tid T sb \<and>
  (((\<forall> t \<in> Tid . (\<forall> (a,b) \<in> the (sb t) . a \<in> T \<and> b \<in> T))
                \<and> (\<forall> (a,b) \<in> rf . a \<in> T \<and> b \<in> T) \<and> (\<forall> a \<in> T . rho a \<noteq> None)) 
    \<longrightarrow> (locksProp T rho \<and> sat Tid T rho sb rf)))"

(* define race condition *)
fun existOtherOp :: "time_type \<Rightarrow> loc_type
               \<Rightarrow> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action \<Rightarrow> bool" where
"existOtherOp key loc (ARead vol v x y axl) = (if loc = x then True else False)"
| "existOtherOp key loc (AWrite vol v x y axl) = (if loc = x then True else False)"
| "existOtherOp key loc (RMW vol v x y axl) = (if loc = x then True else False)"
| "existOtherOp key loc (NRead vol v x t na n axl) = (if key = t then False else
                                             (if loc = x then True else False))"
| "existOtherOp key loc (NWrite vol v x t na n axl) = (if key = t then False else
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
"raceDef T rho = (\<exists> t1 t2 tid aid1 aid2 v v' x t n axl vol . t1 \<in> T \<and> t2 \<in> T \<and> rho t1 = Some (tid,aid1, NRead vol v x t 1 n axl)
                       \<and> rho t2 = Some (tid, aid2, NRead vol v' x t n n axl) 
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
moSeqAtomic : "\<lbrakk> t \<in> T; rho t = Some (tid,aid,ac); isSeqAtomic ac; acLoc ac = Some x; x \<in> Locs\<rbrakk>
                \<Longrightarrow> (tid,t,x) \<in> seqPos T rho Locs"
| moSeqFence : "\<lbrakk> t \<in> T; rho t = Some (tid,aid,Fence SeqCst); x \<in> Locs\<rbrakk>
                \<Longrightarrow> (tid,t,x) \<in> seqPos T rho Locs"

definition hasPrevMem where
"hasPrevMem T t sb = (\<exists> t' \<in> T . (t',t) \<in> trancl sb)"

definition hasReadFrom where
"hasReadFrom T t rf = (\<exists> t' \<in> T . (t',t) \<in> rf)"

definition samLocInMid where
"samLocInMid T rho a b tid x =
   (\<exists> t aid ac . a < t \<and> t < b \<and>  t \<in> T \<and> rho t = Some (tid,aid,ac) \<and> acLoc ac = Some x)"

definition seqPosInMid where
"seqPosInMid T Tids rho Locs a b x =
            (\<exists> t tid . t \<in> T \<and> tid \<in> Tids \<and> a < t \<and> t < b \<and> (tid,t,x) \<in> seqPos T rho Locs)"

fun sameMemContentAux where
"sameMemContentAux (AWrite vol1 x y z axl1) (AWrite vol2 u v w axl2) = (if x = u \<and> y = v then True else False)"
| "sameMemContentAux (RMW vol1 x y z axl1) (RMW vol2 u v w axl2) = (if x = u \<and> y = v then True else False)"
| "sameMemContentAux (NWrite vol1 x y z n1 n2 axl1) (NWrite vol2 u v w n3 n4 axl2) = (if x = u \<and> y = v then True else False)"
| "sameMemContentAux x y = False"

definition sameMemContent :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option) \<Rightarrow> time_type option
         \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option) \<Rightarrow> time_type option \<Rightarrow> bool " where
"sameMemContent rho1 a rho2 b = (a = None \<and> b = None \<or>
             (\<forall> a' b' . a = Some a' \<and> b = Some b' \<longrightarrow> 
                (\<forall> tid1 aid1 tid2 aid2 ac1 ac2 . rho1 a' = Some (tid1,aid1,ac1) \<and> rho2 b' = Some (tid2,aid2,ac2)
                            \<and> sameMemContentAux ac1 ac2)))"

inductive_set observeMem :: "'tid set \<Rightarrow> time_type set
              \<Rightarrow> (time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option)
               \<Rightarrow> ('tid \<Rightarrow> (time_type \<times> time_type) set option)
               \<Rightarrow> (time_type \<times> time_type) set
               \<Rightarrow> loc_type set \<Rightarrow>
                           ('tid \<times> time_type \<times> loc_type \<times> time_type option) set"
for Tids :: "'tid set"
    and E :: "time_type set"
    and rho :: "(time_type \<Rightarrow> ('tid \<times> aid_type \<times> (aid_type, 'val, loc_type,
                 'lock, 'name, 'callID) action) option)"
    and sbs :: "('tid \<Rightarrow> (time_type \<times> time_type) set option)"
    and rf :: "(time_type \<times> time_type) set"
     and Locs :: "loc_type set" where
 moBase1 : "\<lbrakk> tid \<in> Tids; t \<in> E; sbs tid = Some sb; \<not> hasPrevMem E t sb; rho t = Some (tid,aid,ac);
                    isFenceLike ac; x \<in> Locs\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,None) \<in> observeMem Tids E rho sbs rf Locs"
| moReadBase1 : "\<lbrakk> tid \<in> Tids; t \<in> E; sbs tid = Some sb; \<not> hasPrevMem E t sb;
                  rho t = Some (tid,aid,ac); isPureRead ac; acLoc ac = Some x; \<not> hasReadFrom E t rf \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,None) \<in> observeMem Tids E rho sbs rf Locs"
| moReadBase2 : "\<lbrakk> tid \<in> Tids; t \<in> E; sbs tid = Some sb; \<not> hasPrevMem E t sb; y \<in> Locs;
                  rho t = Some (tid,aid,ac); \<not> isFenceLike ac; acLoc ac = Some x; x \<noteq> y \<rbrakk> 
                  \<Longrightarrow> (tid,t,y,None) \<in> observeMem Tids E rho sbs rf Locs"
| moWriteOther1 : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,ac); y \<in> Locs;
                    isAtomicWrite ac; acLoc ac = Some x; x \<noteq> y;
                   (tid, t'', y, a) \<in> observeMem Tids E rho sbs rf Locs; t'' < t;
                     \<not> samLocInMid E rho t'' t tid y;\<not> seqPosInMid E Tids rho Locs t'' t y\<rbrakk> 
                  \<Longrightarrow> (tid,t,y,a) \<in> observeMem Tids E rho sbs rf Locs"
| moWriteOther2 : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,ac); y \<in> Locs;
                    isAtomicWrite ac; acLoc ac = Some x; x \<noteq> y; (tid',t'',y) \<in> seqPos E rho Locs;
                   (tid', t'', y, a) \<in> observeMem Tids E rho sbs rf Locs; t'' < t;
                     \<not> samLocInMid E rho t'' t tid y;\<not> seqPosInMid E Tids rho Locs t'' t y\<rbrakk> 
                  \<Longrightarrow> (tid,t,y,a) \<in> observeMem Tids E rho sbs rf Locs"
| moAtomicWrite : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,ac);
                    isAtomicWrite ac; acLoc ac = Some x \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,Some t) \<in> observeMem Tids E rho sbs rf Locs"
| moNWriteBase : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' cur num axl); num \<noteq> cur;
                 sbs tid = Some sb; \<not> hasPrevMem E t sb\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,None) \<in> observeMem Tids E rho sbs rf Locs"
| moNWriteNoUpdate : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' cur num axl); num \<noteq> cur;
                         (tid, t'', x, a) \<in> observeMem Tids E rho sbs rf Locs; t'' < t;
                         \<not> samLocInMid E rho t'' t tid x; \<not> seqPosInMid E Tids rho Locs t'' t x \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs rf Locs"
| moNWriteNoUpdateSeq : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' cur num axl); num \<noteq> cur;
                         (tid', t'', x, a) \<in> observeMem Tids E rho sbs rf Locs; t'' < t;
                        (tid',t'',x) \<in> seqPos E rho Locs;
                         \<not> samLocInMid E rho t'' t tid x;\<not> seqPosInMid E Tids rho Locs t'' t x \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs rf Locs"
| moNWriteUpdate : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,NWrite vol v x t' num num axl) \<rbrakk> 
                  \<Longrightarrow> (tid,t,x,Some t) \<in> observeMem Tids E rho sbs rf Locs"
| moFenceLike1 : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,ac); 
                    isFenceLike ac; x \<in> Locs; ac \<noteq> Fence SeqCst;
                  (tid, t'', x, a) \<in> observeMem Tids E rho sbs rf Locs; t'' < t;
                   \<not> samLocInMid E rho t'' t tid x;\<not> seqPosInMid E Tids rho Locs t'' t x\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs rf Locs"
| moFenceLike2 : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,ac); 
                    isFenceLike ac; x \<in> Locs; ac \<noteq> Fence SeqCst;
                  (tid', t'', x, a) \<in> observeMem Tids E rho sbs rf Locs; t'' < t;
                    (tid',t'',x) \<in> seqPos E rho Locs;
                   \<not> samLocInMid E rho t'' t tid x;\<not> seqPosInMid E Tids rho Locs t'' t x\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,a) \<in> observeMem Tids E rho sbs rf Locs"
| moSeqFence : "\<lbrakk> tid \<in> Tids; t \<in> E; rho t = Some (tid,aid,Fence SeqCst); x \<in> Locs;
                  (t'', x, t) \<in> cw E rho rf\<rbrakk> 
                  \<Longrightarrow> (tid,t,x,Some t'') \<in> observeMem Tids E rho sbs rf Locs"

(* first posibility: two executions are equivalence
    if their memories are the same for a set locs infinitely often.
 Tid T rho sb rf*)
definition inifOften where
"inifOften Tid T Locs rho1 sb1 rf1 rho2 sb2 rf2 =
     (\<forall> t \<in> T . (\<exists> t' \<in> T . t' > t \<and>
          (\<forall> tid x . tid \<in> Tid \<and> x \<in> Locs \<longrightarrow>
            (\<exists> a b .
               (tid,t',x,a) \<in> observeMem Tid T rho1 sb1 rf1 Locs
              \<and> (tid,t',x,b) \<in> observeMem Tid T rho2 sb2 rf2 Locs
              \<and> sameMemContent rho1 a rho2 b))))"

definition firstEquiv where
"firstEquiv Tid T Locs rho1 sb1 rf1 rho2 sb2 rf2 =
   (validExecution Tid T rho1 sb1 rf1 \<and> validExecution Tid T rho2 sb2 rf2
      \<and> inifOften Tid T Locs rho1 sb1 rf1 rho2 sb2 rf2)"

(* second posibility: two executions are equivalence
    if their memories are the same for a set locs eventually always.
 Tid T rho sb rf*)
definition evalAlways where
"evalAlways Tid T Locs rho1 sb1 rf1 rho2 sb2 rf2 =
     (\<exists> t \<in> T . (\<forall> t' \<in> T . t' > t \<and>
          (\<forall> tid x . tid \<in> Tid \<and> x \<in> Locs \<longrightarrow>
            (\<exists> a b .
               (tid,t',x,a) \<in> observeMem Tid T rho1 sb1 rf1 Locs
              \<and> (tid,t',x,b) \<in> observeMem Tid T rho2 sb2 rf2 Locs
              \<and> sameMemContent rho1 a rho2 b))))"

definition secondEquiv where
"secondEquiv Tid T Locs rho1 sb1 rf1 rho2 sb2 rf2 =
   (validExecution Tid T rho1 sb1 rf1 \<and> validExecution Tid T rho2 sb2 rf2
      \<and> evalAlways Tid T Locs rho1 sb1 rf1 rho2 sb2 rf2)"

end

end