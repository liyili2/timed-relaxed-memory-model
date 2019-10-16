theory SC11
imports Main
begin

(*
TODO: need to modify the definition to include RC11 model and RA11 model.

RC11: a. make the SC fence stronger having a total order on all writes.
      b. WW-merge mistake, too week a sc read/write instead of the acq write.
         our timed-relaxed memory model will make it stronger to prevent SB and WW-merge
      c. the way to prevent out-of-thin-air reads is problematic.
         the requirement for sb \<union> rf to be acyclic is too strong.

RA11: RA11 is just adding modification order on each location on top of
      the current acquire/release atomics.

*)

type_synonym action_id = nat
type_synonym thread_id = nat
type_synonym location = nat
type_synonym avalue = nat
type_synonym program = nat

(* 1 - Relational definitions *)

definition irrefl where
"irrefl S ord = (\<forall> x \<in> S . \<not> ((x,x) \<in> ord))"

definition trans where
"trans S ord = (\<forall> x \<in> S . (\<forall> y \<in> S . (\<forall> z \<in> S. (x,y) \<in> ord \<and> (y,z) \<in> ord \<longrightarrow> (x,z) \<in> ord)))"

definition cross where
"cross S T = {(s,t) . s \<in> S \<and> t \<in> T}"

inductive tc' where
a: "r (x,y) \<Longrightarrow> tc' r (x,y)"
| b: "\<lbrakk> tc' r (x,z); tc' r (z,y)\<rbrakk> \<Longrightarrow> tc' r (x,y)"

definition tc where
"tc r = {(x,y) . (x,y) \<in> r \<and> tc' (\<lambda> (x,y) . (x,y) \<in> r) (x,y) }"

definition restrict_relation_set where
"restrict_relation_set rel s = rel \<inter> (cross s s)"

definition strict_preorder where
"strict_preorder s ord =(irrefl s (ord) \<and> trans s (ord))"

definition relation_over where
"relation_over s rel = (\<forall> (a,b) \<in> rel . a \<in> s \<and> b \<in> s)"

definition inj_on where
"inj_on f A = (\<forall> x \<in> A . (\<forall> y \<in> A . f x = f y \<longrightarrow> x = y))"

definition total_order_over where
"total_order_over s ord = (relation_over s ord \<and> (\<forall> x \<in> s . (\<forall> y \<in> s . (x,y) \<in> ord \<or> (y,x) \<in> ord \<or> x = y)))"

definition strict_total_order_over where
"strict_total_order_over s ord = (strict_preorder s ord \<and> total_order_over s ord)"

definition adjacent_less_than where
"adjacent_less_than ord s x y = ((x,y) \<in> ord \<and> \<not> (\<exists> z \<in> s . (x,z) \<in> ord \<and> (z,y) \<in> ord))"

definition adjacent_less_than_such_that where
"adjacent_less_than_such_that pred ord s x y =
     (pred x \<and> (x,y) \<in> ord \<and> \<not> (\<exists> z \<in> s . pred z \<and> (x,z) \<in> ord \<and> (z,y) \<in> ord))"

(* 2 - Action and location types *)

datatype memory_order =
    Mo_seq_cst
  | Mo_relaxed
  | Mo_release
  | Mo_acquire
  | Mo_consume
  | Mo_acq_rel

datatype lock_outcome =
    Success
  | Blocked

datatype action =
    Lock action_id  thread_id  location  lock_outcome
  | Unlock action_id  thread_id  location
  | Atomic_load  action_id thread_id memory_order location avalue
  | Atomic_store action_id thread_id memory_order location avalue
  | Atomic_rmw action_id thread_id memory_order location avalue avalue
  | Load action_id thread_id location avalue
  | Store action_id thread_id location avalue
  | Fence action_id thread_id memory_order
  | Blocked_rmw action_id thread_id location

primrec action_id_of where
"action_id_of (Lock aid x y z) = aid"
| "action_id_of (Unlock aid x y) = aid"
| "action_id_of (Atomic_load aid x y u v) = aid"
| "action_id_of (Atomic_store aid x y u v) = aid"
| "action_id_of (Atomic_rmw aid x y z u v) = aid"
| "action_id_of (Load aid x y z) = aid"
| "action_id_of (Store aid x y z) = aid"
| "action_id_of (Fence aid x y) = aid"
| "action_id_of (Blocked_rmw aid x y) = aid"

primrec thread_id_of where
"thread_id_of (Lock x tid y z) = tid"
| "thread_id_of (Unlock x tid y) = tid"
| "thread_id_of (Atomic_load x tid y u v) = tid"
| "thread_id_of (Atomic_store x tid y u v) = tid"
| "thread_id_of (Atomic_rmw x tid y z u v) = tid"
| "thread_id_of (Load x tid y z) = tid"
| "thread_id_of (Store x tid y z) = tid"
| "thread_id_of (Fence x tid y) = tid"
| "thread_id_of (Blocked_rmw x tid y) = tid"

fun memory_order_of where
"memory_order_of (Atomic_load x y ord u v) = Some ord"
| "memory_order_of (Atomic_store x y ord u v) = Some ord"
| "memory_order_of (Atomic_rmw x y ord z u v) = Some ord"
| "memory_order_of (Fence x y ord) = Some ord"
| "memory_order_of x = None"

primrec location_of where
"location_of (Lock x tid l z) = Some l"
| "location_of (Unlock x tid l) = Some l"
| "location_of (Atomic_load x tid y l v) = Some l"
| "location_of (Atomic_store x tid y l v) = Some l"
| "location_of (Atomic_rmw x tid y l u v) = Some l"
| "location_of (Load x tid l z) = Some l"
| "location_of (Store x tid l z) = Some l"
| "location_of (Fence x tid y) = None"
| "location_of (Blocked_rmw x tid l) = Some l"

fun value_read_by where
"value_read_by (Atomic_load x tid y l v) = Some v"
| "value_read_by (Atomic_rmw x tid y l u v) = Some v"
| "value_read_by (Load x tid l v) = Some v"
| "value_read_by x = None"

fun value_written_by where
 "value_written_by (Atomic_store x tid y l v) = Some v"
| "value_written_by (Atomic_rmw x tid y l u v) = Some v"
| "value_written_by (Store x tid l v) = Some v"
| "value_written_by x = None"

fun is_lock where
 "is_lock (Lock x tid l z) = True"
| "is_lock a = False"

fun is_successful_lock where
 "is_successful_lock (Lock x tid l Success) = True"
| "is_successful_lock a = False"

fun is_blocked_lock where
 "is_blocked_lock (Lock x tid l Blocked) = True"
| "is_blocked_lock a = False"

fun is_unlock where
 "is_unlock (Unlock x tid l) = True"
| "is_unlock a = False"

fun is_atomic_load where
 "is_atomic_load (Atomic_load x tid y l v) = True"
| "is_atomic_load a = False"

fun is_atomic_store where
 "is_atomic_store (Atomic_store x tid y l v) = True"
| "is_atomic_store a = False"

fun is_atomic_rmw where
 "is_atomic_rmw (Atomic_rmw x tid y l v u) = True"
| "is_atomic_rmw a = False"

fun is_blocked_rmw where
 "is_blocked_rmw (Blocked_rmw x tid y) = True"
| "is_blocked_rmw a = False"

fun is_load where
 "is_load (Load x tid y z) = True"
| "is_load a = False"

fun is_store where
 "is_store (Store x tid y z) = True"
| "is_store a = False"

fun is_fence where
 "is_fence (Fence x y z) = True"
| "is_fence a = False"

fun is_atomic_action where
 "is_atomic_action a = (is_atomic_load a \<or> is_atomic_store a \<or> is_atomic_rmw a)"

fun is_read where
 "is_read a = (is_load a \<or> is_atomic_load a \<or> is_atomic_rmw a)"

fun is_write where
 "is_write a = (is_store a \<or> is_atomic_store a \<or> is_atomic_rmw a)"

(* It is important to note that seq_cst atomics are both acquires and releases *)

fun is_acquire where
"is_acquire a = (case memory_order_of a of 
        Some Mo_acquire \<Rightarrow> is_read a \<or> is_fence a
        | Some Mo_acq_rel \<Rightarrow> is_read a \<or> is_fence a
        | Some Mo_seq_cst \<Rightarrow> is_read a \<or> is_fence a
        | Some Mo_consume \<Rightarrow> is_fence a
        | None \<Rightarrow> is_lock a
        | _ \<Rightarrow> False)"

fun is_consume where
"is_consume a = (is_read a \<and> (memory_order_of a = Some Mo_consume))"

fun is_release where
"is_release a = (case memory_order_of a of 
        Some Mo_acquire \<Rightarrow> is_write a \<or> is_fence a
        | Some Mo_acq_rel \<Rightarrow> is_write a \<or> is_fence a
        | Some Mo_seq_cst \<Rightarrow> is_write a \<or> is_fence a
        | None \<Rightarrow> is_unlock a
        | _ \<Rightarrow> False)"

fun is_seq_cst where
"is_seq_cst a = (memory_order_of a = Some Mo_seq_cst)"


(*   - 2.2 - Location kinds *)

datatype location_kind =
    Mutex
  | Non_atomic
  | Atomic

definition actions_respect_location_kinds where
"actions_respect_location_kinds S lk = 
   (\<forall> a \<in> S . case location_of a of Some l \<Rightarrow> 
                  (case lk l of 
                     Mutex \<Rightarrow> is_lock a \<or> is_unlock a
                   | Non_atomic \<Rightarrow> is_load a \<or> is_store a
                   | Atomic \<Rightarrow> is_store a \<or> is_atomic_action a \<or>  is_blocked_rmw a)
            | None \<Rightarrow> True)"

fun is_at_location_kind where
"is_at_location_kind lk a lk0 = 
   (case location_of a of Some l \<Rightarrow> (lk l = lk0)
             | None \<Rightarrow> False)"

fun is_at_mutex_location where
"is_at_mutex_location lk a = is_at_location_kind lk a Mutex"

fun is_at_non_atomic_location where
"is_at_non_atomic_location lk a = is_at_location_kind lk a Non_atomic"

fun is_at_atomic_location where
"is_at_atomic_location lk a = is_at_location_kind lk a Atomic"

(* 3 - The preferred model *)
record opsem_execution_part =
  actions :: "action set"
  threads :: "thread_id set"
  lk      :: "location \<Rightarrow> location_kind"
  sb      :: "(action * action) set"
  asw     :: "(action * action) set"
  dd      :: "(action * action) set"
  cd      :: "(action * action) set"

record witness_execution_part =
  rf     :: "(action * action) set"
  mo     :: "(action * action) set"
  sc     :: "(action * action) set"

(*   - 3.2 - Well formed action *)

fun same_thread where
"same_thread a b = (thread_id_of a = thread_id_of b)"

fun threadwise_relation_over where
"threadwise_relation_over s rel = relation_over s rel"

fun same_location where 
"same_location a b = (location_of a = location_of b)"

fun locations_of where
"locations_of as = {l . (\<exists> a . Some l = location_of a \<and> a \<in> as)}"

fun well_formed_action where
"well_formed_action a = 
   (case a of Atomic_load x y mem_ord u v \<Rightarrow>
       mem_ord = Mo_relaxed \<or> mem_ord = Mo_acquire \<or> mem_ord = Mo_seq_cst \<or> mem_ord = Mo_consume
      | Atomic_store x y mem_ord u v \<Rightarrow> mem_ord = Mo_relaxed \<or> mem_ord = Mo_release \<or> mem_ord = Mo_seq_cst 
      | Atomic_rmw x y mem_ord z u v \<Rightarrow> mem_ord = Mo_relaxed \<or> mem_ord = Mo_release \<or> mem_ord = Mo_acquire
                                \<or> mem_ord = Mo_acq_rel \<or> mem_ord = Mo_seq_cst \<or> mem_ord = Mo_consume
      | _ \<Rightarrow> True)"

(*  - 3.3 - Well formed threads *)
fun well_formed_threads where
"well_formed_threads as threads' lk' sb' asw' dd' cd' = 
   (inj_on action_id_of as \<and>
      (\<forall> a \<in> as . well_formed_action a) \<and>
    threadwise_relation_over as sb' \<and>
    threadwise_relation_over as dd' \<and>
    threadwise_relation_over as cd' \<and>
    strict_preorder as sb' \<and>
    strict_preorder as dd' \<and>
    strict_preorder as cd' \<and>
    (\<forall> a \<in> as . thread_id_of a \<in> threads') \<and>
    actions_respect_location_kinds as lk' \<and>
    dd' \<subseteq> sb' \<and>
    relation_over as asw' \<and>
    (\<forall> a \<in> as . is_blocked_rmw a \<or> is_blocked_lock a \<longrightarrow> \<not> (\<exists> b \<in> as . (a,b) \<in> sb')))"

(*   - 3.4 - Consistent locks *)
fun consistent_locks where
"consistent_locks as lo hb = 
   (strict_total_order_over {a . a \<in> as \<and> (is_lock a \<or> is_unlock a)} lo \<and>
       restrict_relation_set hb {a . a \<in> as \<and> (is_lock a \<or> is_unlock a)} \<subseteq> lo \<and>
   (\<forall> (a,c) \<in> lo. 
      is_successful_lock a \<and> is_successful_lock c \<and> same_location a c
     \<longrightarrow>
      (\<exists> b \<in> as . same_location a b \<and> is_unlock b \<and> (a,b) \<in> lo \<and> (b,c) \<in> lo)))"

(*  - 3.5 - Well formed reads from mapping *)
fun well_formed_reads_from_mapping where
"well_formed_reads_from_mapping as lk' rf' = 
  (relation_over as rf' \<and>
  (\<forall> a1 \<in> as . (\<forall> a2 \<in> as . (\<forall> b \<in> as . 
          (a1,b) \<in> rf' \<and> (a2,b) \<in> rf' \<longrightarrow> (a1 = a2)))) \<and>
   (\<forall> a \<in> as . (\<forall> b \<in> as . (a,b) \<in> rf' \<longrightarrow> 
          same_location a b \<and> (value_read_by b = value_written_by a) \<and>
        \<not> (a = b) \<and> \<not> is_fence a \<and> \<not> is_fence b \<and>
    \<not> (is_at_mutex_location lk' a) \<and> 
       (is_at_non_atomic_location lk' a \<longrightarrow> is_store a \<and> is_load b) \<and>
       (is_at_atomic_location lk' a \<longrightarrow>
          (is_atomic_store a \<or> is_atomic_rmw a \<or> is_store a) \<and> 
           (is_atomic_load b \<or> is_atomic_rmw b \<or> is_load b)))))"

(*   - 3.6 - Happens before *)
fun rs_element where
"rs_element rs_head a =
    (same_thread a rs_head \<or> is_atomic_rmw a)"

fun release_sequence where
"release_sequence as lk' mo' a_rel b =
   (is_at_atomic_location lk' b \<and>
    is_release a_rel \<and>
    ((b = a_rel) \<or>
      (rs_element a_rel b \<and> (a_rel,b) \<in> mo' \<and>
        (\<forall> c \<in> as . ((a_rel,c) \<in> mo' \<and> (c,b) \<in> mo') \<longrightarrow> rs_element a_rel c))))"


fun release_sequence_set where
"release_sequence_set as lk' mo' =
 {(a,b) . a \<in> as \<and> b \<in> as \<and> release_sequence as lk' mo' a b}"

fun hypothetical_release_sequence where
"hypothetical_release_sequence as lk' mo' a b =
    (is_at_atomic_location lk' b \<and>
    ((b = a) \<or>
      ( rs_element a b \<and> (a,b) \<in> mo' \<and> 
        (\<forall> c \<in> as . ((a,c) \<in> mo' \<and> (c,b) \<in> mo') \<longrightarrow> rs_element a c))))"

fun hypothetical_release_sequence_set where
"hypothetical_release_sequence_set as lk' mo' =
  {(a,b) . a \<in> as \<and> b \<in> as \<and> hypothetical_release_sequence as lk' mo' a b}"

fun synchronizes_with where
"synchronizes_with as sb' asw' rf' lo rs hrs a b =
  ((a,b) \<in> asw' \<or>
    ( same_location a b \<and> a \<in> as \<and> b \<in> as \<and>
     ( (is_unlock a \<and> is_successful_lock b \<and> (a,b) \<in> lo) \<or>
       ( is_release a \<and> is_acquire b \<and> \<not> (same_thread a b) \<and>
          (\<exists> c \<in> as . (a,c) \<in> rs \<and> (c,b) \<in> rf' ) ) \<or>
        (\<not> (same_thread a b) \<and>
          is_fence a \<and> is_release a \<and> is_fence b \<and> is_acquire b \<and>
          (\<exists> x \<in> as . (\<exists> y \<in> as . same_location x y \<and>
              is_atomic_action x \<and> is_atomic_action y \<and> is_write x \<and>
              (a,x) \<in> sb' \<and> (y,b) \<in> sb' \<and>
              (\<exists> z \<in> as . (x,z) \<in> hrs \<and> (z,y) \<in> rf')))) \<or> 
        (\<not> (same_thread a b) \<and>
          is_fence a \<and> is_release a \<and> is_atomic_action b \<and> is_acquire b \<and>
          (\<exists> x \<in> as . same_location x b \<and>
            is_atomic_action x \<and> is_write x \<and> (a,x) \<in> sb' \<and>
            (\<exists> z \<in> as . (x,z) \<in> hrs \<and> (z,b) \<in> rf' ) ) ) \<or>
        (\<not> (same_thread a b) \<and>
          is_atomic_action a \<and> is_release a \<and>
          is_fence b \<and> is_acquire b \<and>
          (\<exists> x \<in> as . same_location a x \<and> is_atomic_action x \<and>
            (x,b) \<in> sb' \<and>
            (\<exists> z \<in> as . (a,z) \<in> rs \<and> (z,x) \<in> rf' ) ) ))))"

fun synchronizes_with_set where
"synchronizes_with_set as sb' asw' rf' lo rs hrs =
 {(a,b) . a \<in> as \<and> b \<in> as \<and> synchronizes_with as sb' asw' rf' lo rs hrs a b}"

fun carries_a_dependency_to_set where
"carries_a_dependency_to_set as sb' dd' rf' = tc ( (rf' \<inter> sb') \<union> dd')"

fun dependency_ordered_before where
"dependency_ordered_before as rf' rs cad a d =
    (a \<in> as \<and> d \<in> as \<and>
     (\<exists> b \<in> as . is_release a \<and> is_consume b \<and>
       (\<exists> e \<in> as . (a,e) \<in> rs \<and> (e,b) \<in> rf') \<and>
       ( (b,d) \<in> cad \<or> (b = d) )))"

fun dependency_ordered_before_set where
"dependency_ordered_before_set as rf' rs cad =
         {(a,b) . a \<in> as \<and> b \<in> as \<and> dependency_ordered_before as rf' rs cad a b}"

fun compose where
"compose R1 R2 = { (w,z) . \<exists> t . (w,t) \<in> R1 \<and> (t,z) \<in> R2}"

fun inter_thread_happens_before where
"inter_thread_happens_before sb' sw dob =
    tc ((sw \<union> dob \<union> (compose sw sb')) \<union> (compose sb' (sw \<union> dob \<union> (compose sw sb'))))"


fun consistent_inter_thread_happens_before where
"consistent_inter_thread_happens_before as ithb = irrefl as ithb"

fun happens_before where
"happens_before as sb' ithb = sb' \<union> ithb"

(*   - 3.7 - Consistent SC and modification orders *)

fun all_sc_actions where
"all_sc_actions as =
 { a . a \<in> as \<and> (is_seq_cst a \<or> is_lock a \<or> is_unlock a )}"

fun consistent_sc_order where
"consistent_sc_order as mo' sc' hb = 
   (strict_total_order_over (all_sc_actions as) sc' \<and>
       (restrict_relation_set hb (all_sc_actions as)) \<subseteq> sc' \<and>
       (restrict_relation_set mo' (all_sc_actions as)) \<subseteq> sc')"

fun consistent_modification_order where
"consistent_modification_order as lk' sb' mo' hb =
  ((\<forall> a \<in> as . (\<forall> b \<in> as . (a,b) \<in> mo' \<longrightarrow>
          (same_location a b \<and> is_write a \<and> is_write b))) \<and>
   (\<forall> l \<in> locations_of as .
        (case lk' l of Atomic \<Rightarrow> 
          (strict_total_order_over {a . a \<in> {a . a \<in> as \<and> location_of a = Some l} \<and> is_write a}
                      (restrict_relation_set mo' {a . a \<in> as \<and> location_of a = Some l})
           \<and> restrict_relation_set hb {a . a \<in> {a . a \<in> as \<and> location_of a = Some l} \<and> is_write a} \<subseteq> mo')  )))"


(*   - 3.8 - Visible side effects *)
fun visible_side_effect where
"visible_side_effect as hb a b =
   ((a,b) \<in> hb \<and>
    is_write a \<and> is_read b \<and> same_location a b \<and>
     \<not> (\<exists> c \<in> as . \<not> (c = a) \<and> \<not> (c = b) \<and>
          is_write c \<and> same_location c b \<and>
          (a,c) \<in> hb \<and> (c,b) \<in> hb))"


fun visible_side_effect_set where
"visible_side_effect_set as hb =
    { (a,b) . (a,b) \<in> hb \<and> visible_side_effect as hb a b}"

(*   - 3.9 - Undefined behaviour *)
fun indeterminate_reads where
"indeterminate_reads as rf' =
    {b . b \<in> as \<and> is_read b \<and> \<not> (\<exists> a \<in> as . (a,b) \<in> rf')}"

fun unsequenced_races where
"unsequenced_races as sb' =
{(a,b) . a \<in> as \<and> b \<in> as \<and> \<not> (a = b) \<and> same_location a b \<and> (is_write a \<or> is_write b) \<and>
          same_thread a b \<and> \<not> ((a,b) \<in> sb' \<or> (b,a) \<in> sb')}"

fun data_races where
"data_races as hb =
{(a,b) . a \<in> as \<and> b \<in> as \<and> \<not> a = b \<and> same_location a b \<and> (is_write a \<or> is_write b) \<and>
       \<not> same_thread a b \<and> \<not> (is_atomic_action a \<and> is_atomic_action b) \<and>
        \<not> ((a,b) \<in> hb \<or> (b,a) \<in> hb) }"

fun data_races' where
"data_races' Xo Xw lo =
 (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
   (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
    (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo rs hrs of sw \<Rightarrow>
     (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
      (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow>
       (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
        (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow>
          data_races (actions Xo) hb)))))))"

fun good_mutex_use where
"good_mutex_use as lk' sb' lo a =
  (case {a' . a' \<in> as \<and> ((is_successful_lock a' \<or> is_unlock a') \<and> (location_of a' = location_of a))} of 
  mutexes_at_l \<Rightarrow> (case restrict_relation_set lo mutexes_at_l of lock_order \<Rightarrow>
  ( is_unlock a  \<longrightarrow> (\<exists> al \<in> as .
              is_successful_lock al \<and> (location_of al = location_of a) \<and> (al,a) \<in> sb' \<and>
              adjacent_less_than lock_order as al a ) ) \<and>
   ( is_lock a \<longrightarrow>
      \<not> (\<exists> al \<in> as .
          is_successful_lock al \<and> (location_of a = location_of al) \<and> same_thread a al \<and>
          adjacent_less_than lock_order as al a ))))"


fun bad_mutexes where
"bad_mutexes Xo lo =
  { a . a \<in> (actions Xo) \<and> \<not> (good_mutex_use (actions Xo) (lk Xo) (sb Xo) lo a)}"

fun undefined_behaviour where
"undefined_behaviour Xo Xw =
  (\<not> (data_races' Xo Xw (sc Xw) = {}) \<or>
  \<not> (unsequenced_races (actions Xo) (sb Xo) = {}) \<or>
  \<not> (indeterminate_reads (actions Xo) (rf Xw) = {}) \<or>
  \<not> (bad_mutexes Xo (sc Xw) = {}))"

(*   - 3.10 - Consistent reads from mapping *)
fun consistent_non_atomic_read_values where
"consistent_non_atomic_read_values as lk' rf' vse =
  (\<forall> b \<in> as . (is_read b \<and> is_at_non_atomic_location lk' b)
   \<longrightarrow> (if (\<exists> a_vse \<in> as . (a_vse,b) \<in> vse)
        then (\<exists> a_vse \<in> as . (a_vse,b) \<in> vse \<and> (a_vse,b) \<in> rf')
        else \<not> (\<exists> a \<in> as . (a,b) \<in> rf')))"

fun coherent_memory_use where
"coherent_memory_use as lk' rf' mo' hb = 
  ((\<forall> (x,a) \<in> rf' .(\<forall> (y,b) \<in> rf' .
      ((a,b) \<in> hb \<and> same_location a b \<and> is_at_atomic_location lk' b) \<longrightarrow>
      ((x = y) \<or> (x,y) \<in> mo'))) \<and>
    (\<forall> (a,b) \<in> hb . (\<forall> c \<in> as .
      ((c,b) \<in> rf' \<and> is_write a \<and> same_location a b \<and> is_at_atomic_location lk' b) \<longrightarrow>
      ((c = a) \<or> (a,c) \<in> mo'))) \<and> 
  (\<forall> (a,b) \<in> hb . (\<forall> c \<in> as .
      ((c,a) \<in> rf' \<and> is_write b \<and> same_location a b \<and> is_at_atomic_location lk' a) \<longrightarrow>
      ((c,b) \<in> mo'))))"

fun rmw_atomicity where
"rmw_atomicity as rf' mo' = 
   (\<forall> (a,b) \<in> rf' .
    is_atomic_rmw b \<longrightarrow> adjacent_less_than mo' as a b)"

fun sc_reads_restricted where
"sc_reads_restricted as rf' sc' mo' hb =
  (\<forall> (a,b) \<in> rf' .
    is_seq_cst b \<longrightarrow>
    (adjacent_less_than_such_that (\<lambda> c . is_write c \<and> same_location b c) sc' as a b) \<or>
    ( \<not> (is_seq_cst a) \<and>
      (\<forall> x \<in> as .
        (adjacent_less_than_such_that (\<lambda> c . is_write c \<and> same_location b c) sc' as x b)
                     \<longrightarrow> \<not> ((a,x) \<in> hb))))"



    (* fence restriction N3291 29.3p4 *)
    (* fence restriction N3291 29.3p5 *)
    (* fence restriction N3291 29.3p6 *)
    (* SC fences impose mo N3291 29.3p7 *)
(* SC fences impose mo N3291 29.3p7, w collapsed first write*)
(* SC fences impose mo N3291 29.3p7, w collapsed second write*)

fun sc_fences_heeded where
"sc_fences_heeded as sb' rf' sc' mo' = 
  ((\<forall> a \<in> as . (\<forall> (x,b) \<in> sb' . (\<forall> y \<in> as .
      ( is_write a \<and> is_fence x \<and>
        adjacent_less_than sc' as a x \<and>
        is_atomic_action b \<and> same_location a b \<and>
        (y,b) \<in> rf') \<longrightarrow>
      (y = a) \<or> (a,y) \<in> mo') )) \<and>
   (\<forall> (a,x) \<in> sb' . (\<forall> (y,b) \<in> rf' .
      ((is_atomic_action a \<and> is_write a \<and>
        is_fence x \<and> is_atomic_action b \<and> (x,b) \<in> sc' \<and>
        same_location a b) \<longrightarrow>
      ((y = a) \<or> (a,y) \<in> mo')))) \<and>
     (\<forall> (a,x) \<in> sb' . (\<forall> (y,b) \<in> sb' . (\<forall> z \<in> as .
      (is_atomic_action a \<and> is_write a \<and>
        is_fence x \<and> is_fence y \<and> (x,y) \<in> sc' \<and>
        is_atomic_action b \<and> same_location a b \<and>
        (z,b) \<in> rf') \<longrightarrow>
             ((z = a) \<or> (a,z) \<in> mo')))) \<and>
  (\<forall> (a,x) \<in> sb' . (\<forall> (y,b) \<in> sb' .
      ( is_atomic_action a \<and> is_write a \<and>
        is_atomic_action b \<and> is_write b \<and>
        is_fence x \<and> is_fence y \<and> (x,y) \<in> sc' \<and>
        same_location a b \<longrightarrow>
      (a,b) \<in> mo'))) \<and>
    (\<forall> a \<in> as . (\<forall> (y,b) \<in> sb' .
      ( is_atomic_action a \<and> is_write a \<and>
        is_fence y \<and> (a,y) \<in> sc' \<and>
        is_atomic_action b \<and> is_write b \<and>
        same_location a b \<longrightarrow>
             (a,b) \<in> mo'))) \<and>
   (\<forall> (a,x) \<in> sb' . (\<forall> b \<in> as .
      (is_atomic_action a \<and> is_write a \<and>
        is_fence x \<and> is_atomic_action b \<and> is_write b \<and> (x,b) \<in> sc' \<and>
        same_location a b \<longrightarrow>
         (a,b) \<in> mo'))) )"

fun no_vsse_consistent_atomic_read_values where
"no_vsse_consistent_atomic_read_values as lk' rf' hb vse = 
   (\<forall> b \<in> as .
    (is_read b \<and> is_at_atomic_location lk' b) \<longrightarrow>
      ( if (\<exists> a_vse \<in> as . (a_vse,b) \<in> vse)
        then (\<exists> a \<in> as . (a,b) \<in> rf' \<and> \<not> ((b,a) \<in> hb))
        else \<not> (\<exists> a \<in> as . (a,b) \<in> rf')))"

fun no_vsse_consistent_reads_from_mapping where
"no_vsse_consistent_reads_from_mapping as lk' sb' rf' sc' mo' hb vse =
   (consistent_non_atomic_read_values as lk' rf' vse \<and>
    no_vsse_consistent_atomic_read_values as lk' rf' hb vse \<and>
    coherent_memory_use as lk' rf' mo' hb \<and>
    rmw_atomicity as rf' mo' \<and>
    sc_reads_restricted as rf' sc' mo' hb \<and>
    sc_fences_heeded as sb' rf' sc' mo')"

(* 3.11 - Consistent execution *)
(* This simplification has ben verified equivalent to the model
   in section 3 using the HOL theorem prover. It removes the complicated
   notion of VSSE's, whose force is covered by the coherence requirements.
   For those looking to work with C or C++ concurrency, this is the preferred model. *)

fun no_vsse_consistent_execution where
"no_vsse_consistent_execution Xo Xw = 
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
   (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
     (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
     (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) (sc Xw) rs hrs of sw \<Rightarrow>
     (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
     (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow>
     (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
     (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow> 
      (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
    consistent_locks (actions Xo) (sc Xw) hb \<and>
       consistent_inter_thread_happens_before (actions Xo) ithb \<and>
        consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
         consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
          well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
             no_vsse_consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse)))))))))"

(*  - 3.12 - Preferred model top level judgement *)
definition no_vsse_cmm where
"no_vsse_cmm opsem p = 
    (case { (Xopsem,Xwitness) . opsem p Xopsem \<and> no_vsse_consistent_execution Xopsem Xwitness}
            of pre_executions \<Rightarrow> 
         if (\<exists> (Xo,Xw) \<in> pre_executions .  undefined_behaviour Xo Xw)
             then {(Xo,Xw) . True} else pre_executions)"


(* 4 - Standard C/C++ model *)
(* The following definitions make up the memory model described by the
   2011 standard. It was constructed in discussion with the
   standardisation comittee. *)

fun visible_sequence_of_side_effects_tail where
"visible_sequence_of_side_effects_tail as mo' hb vsse_head b = 
   { c . c \<in> as \<and> (vsse_head,c) \<in> mo' \<and> \<not> (b,c) \<in> hb \<and>
           (\<forall> a \<in> as . (vsse_head,a) \<in> mo' \<and> (a,c) \<in> mo' \<longrightarrow> \<not> (b,a) \<in> hb)}"

(* visible sequences of side effects have been proven redundant. See the simpler model in section 3. *)
fun visible_sequence_of_side_effects where
"visible_sequence_of_side_effects as lk' mo' hb vsse_head b =
     (b , if is_at_atomic_location lk' b then
             {vsse_head} \<union>
             visible_sequence_of_side_effects_tail as mo' hb vsse_head b
           else {})"

fun visible_sequences_of_side_effects_set where
"visible_sequences_of_side_effects_set as lk' mo' hb vse =
   { (b,bs) . b \<in> as \<and> is_at_atomic_location lk' b \<and> is_read b \<and>
        (\<exists> vsse_head . (b,bs) = visible_sequence_of_side_effects as lk' mo' hb vsse_head b
        \<and> vsse_head \<in> as \<and> (vsse_head,b) \<in> vse)}"

fun consistent_atomic_read_values where
"consistent_atomic_read_values as lk' rf' vsses =
   (\<forall> b \<in> as . (is_read b \<and> is_at_atomic_location lk' b) \<longrightarrow> 
           ( if (\<exists> (b',v) \<in> vsses . b = b')
        then (\<exists> (b',v) \<in> vsses . b = b' \<and>
               (\<exists> c \<in> v . (c,b) \<in> rf'))
        else \<not> (\<exists> a \<in> as . (a,b) \<in> rf')))"

fun consistent_reads_from_mapping where 
"consistent_reads_from_mapping as lk' sb' rf' sc' mo' hb vse vsses =
   (consistent_non_atomic_read_values as lk' rf' vse \<and>
    consistent_atomic_read_values as lk' rf' vsses \<and>
    coherent_memory_use as lk' rf' mo' hb \<and>
    rmw_atomicity as rf' mo' \<and>
    sc_reads_restricted as rf' sc' mo' hb \<and>
    sc_fences_heeded as sb' rf' sc' mo')"

fun consistent_execution where
"consistent_execution Xo Xw =
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
     (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) (sc Xw) rs hrs of sw \<Rightarrow>
        (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
         (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow> 
          (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
           (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow> 
            (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
             (case visible_sequences_of_side_effects_set (actions Xo) (lk Xo) (mo Xw) hb vse of vsses \<Rightarrow>
              consistent_locks (actions Xo) (sc Xw) hb \<and>
    consistent_inter_thread_happens_before (actions Xo) ithb \<and>
    consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
    consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
    well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
    consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse vsses))))))))))"

(*   - 4.1  - Standard model top level judgement *)
definition cmm where
"cmm opsem p = (case { (Xopsem,Xwitness) . opsem p Xopsem \<and> consistent_execution Xopsem Xwitness}
       of pre_executions \<Rightarrow> if (\<exists> (Xo,Xw) \<in> pre_executions . undefined_behaviour Xo Xw)
                             then {(Xo,Xw). True} else pre_executions)"


(* 5 - Model with seperate lock order *)
(* A version of the no VSSE model with a seperate lock order. *)
fun no_vsse_seperate_lo_consistent_execution where
"no_vsse_seperate_lo_consistent_execution Xo Xw lo =
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
     (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo rs hrs of sw \<Rightarrow>
        (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
         (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow> 
          (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
           (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow> 
            (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
             (case visible_sequences_of_side_effects_set (actions Xo) (lk Xo) (mo Xw) hb vse of vsses \<Rightarrow>
    consistent_locks (actions Xo) lo hb \<and>
    consistent_inter_thread_happens_before (actions Xo) ithb \<and>
    consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
    consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
    well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
    no_vsse_consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse))))))))))"

fun no_vsse_seperate_lo_undefined_behaviour where
"no_vsse_seperate_lo_undefined_behaviour Xo Xw lo =
  (\<not> (data_races' Xo Xw lo = {}) \<or>
  \<not> (unsequenced_races (actions Xo) (sb Xo) = {}) \<or>
  \<not> (indeterminate_reads (actions Xo) (rf Xw) = {}) \<or>
  \<not> (bad_mutexes Xo lo = {}))"

(*  - 5.1  - Seperate lock order top level judgement *)
definition no_vsse_seperate_lo_cmm where
"no_vsse_seperate_lo_cmm opsem p = 
   (case { (Xopsem,(Xwitness,lo)).
      opsem p Xopsem \<and> no_vsse_seperate_lo_consistent_execution Xopsem Xwitness lo}
       of pre_executions \<Rightarrow>
       if (\<exists> (Xo,(Xw,lo)) \<in> pre_executions . no_vsse_seperate_lo_undefined_behaviour Xo Xw lo)
        then { (Xo,(Xw,lo)) . True } else pre_executions)"

(* 6 - Model with per-location lock orders *)
(* This model uses per location lock orders rather than one shared one. *)
fun multi_lo_consistent_locks where
"multi_lo_consistent_locks as lk' lo hb =
  (case {a . a \<in> as \<and> (is_lock a \<or> is_unlock a)} of mutex_actions \<Rightarrow>
    (case restrict_relation_set hb mutex_actions of lo_happens_before \<Rightarrow>
      lo_happens_before \<subseteq> lo \<and>
    (\<forall> (a,c) \<in> lo . is_successful_lock a \<and> is_successful_lock c \<and> same_location a c
      \<longrightarrow>  (\<exists> b \<in> as . same_location a b \<and> is_unlock b \<and> (a,b) \<in> lo \<and> (b,c) \<in> lo)) \<and>
   (\<forall> l \<in> locations_of as . 
        (case {a . a \<in> as \<and>location_of a = Some l} of actions_at_l \<Rightarrow>
           (case lk' l of Mutex \<Rightarrow> strict_total_order_over actions_at_l (restrict_relation_set lo actions_at_l)
                | _ \<Rightarrow> Set.is_empty (restrict_relation_set lo actions_at_l))))))"

fun no_vsse_multi_lo_consistent_execution where
"no_vsse_multi_lo_consistent_execution Xo Xw lo =
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
     (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo rs hrs of sw \<Rightarrow>
        (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
         (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow> 
          (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
           (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow> 
            (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
    multi_lo_consistent_locks (actions Xo) (lk Xo) lo hb \<and>
    consistent_inter_thread_happens_before (actions Xo) ithb \<and>
    consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
    consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
    well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
    no_vsse_consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse)))))))))"

(*   - 6.1  - per-location lock order top level judgement *)
definition no_vsse_multi_lo_cmm where
"no_vsse_multi_lo_cmm opsem p = 
   (case { (Xopsem,(Xwitness,lo)).
      opsem p Xopsem \<and> no_vsse_multi_lo_consistent_execution Xopsem Xwitness lo}
       of pre_executions \<Rightarrow>
       if (\<exists> (Xo,(Xw,lo)) \<in> pre_executions . no_vsse_seperate_lo_undefined_behaviour Xo Xw lo)
        then { (Xo,(Xw,lo)) . True } else pre_executions)"

(* 7 - Model with single step mutex synchronisation *)
(* This model creates synchronizes-with edges from each unlock to the
   next lock at the same location, rather than all subsequent ones. *)
fun lo_single_synchronizes_with where
"lo_single_synchronizes_with as sb' asw' rf' lo rs hrs a b = 
  ((a,b) \<in> asw' \<or>
    (same_location a b \<and> a \<in> as \<and> b \<in> as \<and>
     ((is_unlock a \<and> is_successful_lock b \<and> (a,b) \<in> lo \<and>
                \<not> (\<exists> c \<in> as . (a,c) \<in> lo \<and> (c,b) \<in> lo)) \<or>
     (is_release a \<and> is_acquire b \<and> \<not> (same_thread a b) \<and>
          (\<exists> c \<in> as . (a,c) \<in> rs \<and> (c,b) \<in>  rf')) \<or>
     ( \<not> (same_thread a b) \<and>
          is_fence a \<and> is_release a \<and> is_fence b \<and> is_acquire b \<and>
          (\<exists> x \<in> as . (\<exists> y \<in> as . same_location x y \<and>
              is_atomic_action x \<and> is_atomic_action y \<and> is_write x \<and>
              (a,x) \<in> sb' \<and> (y,b) \<in> sb' \<and>
              (\<exists> z \<in> as . (x,z) \<in> hrs \<and> (z,y) \<in> rf')))) \<or>
    ( \<not> (same_thread a b) \<and>
          is_fence a \<and> is_release a \<and> is_atomic_action b \<and> is_acquire b \<and>
          (\<exists> x \<in> as . same_location x b \<and>
            is_atomic_action x \<and> is_write x \<and> (a,x) \<in> sb' \<and>
            (\<exists> z \<in> as . (x,z) \<in> hrs \<and> (z,b) \<in> rf'))) \<or>
    ( \<not> (same_thread a b) \<and>
          is_atomic_action a \<and> is_release a \<and>
          is_fence b \<and> is_acquire b \<and>
          ( \<exists> x \<in> as . same_location a x \<and> is_atomic_action x \<and>
            (x,b) \<in> sb' \<and>
            ( \<exists> z \<in> as . (a,z) \<in> rs \<and> (z,x) \<in> rf'))))))"

fun lo_single_synchronizes_with_set where
"lo_single_synchronizes_with_set as sb' asw' rf' lo rs hrs =
    {(a,b) . a \<in> as \<and> b \<in> as \<and>
       lo_single_synchronizes_with as sb' asw' rf' lo rs hrs a b}"

fun no_vsse_multi_lo_single_sw_consistent_execution where
"no_vsse_multi_lo_single_sw_consistent_execution Xo Xw lo =
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
     (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo rs hrs of sw \<Rightarrow>
        (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
         (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow> 
          (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
           (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow> 
            (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
    multi_lo_consistent_locks (actions Xo) (lk Xo) lo hb \<and>
    consistent_inter_thread_happens_before (actions Xo) ithb \<and>
    consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
    consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
    well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
    no_vsse_consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse)))))))))"

fun los_single_sw_data_races' where
"los_single_sw_data_races' Xo Xw lo = 
    (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case lo_single_synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo rs hrs of sw \<Rightarrow>
        (case carries_a_dependency_to_set (actions Xo) (sb Xo) (dd Xo) (rf Xw) of cad \<Rightarrow>
         (case dependency_ordered_before_set (actions Xo) (rf Xw) rs cad of dob \<Rightarrow> 
          (case inter_thread_happens_before (sb Xo) sw dob of ithb \<Rightarrow>
           (case happens_before (actions Xo) (sb Xo) ithb of hb \<Rightarrow> 
      data_races (actions Xo) hb)))))))"

fun no_vsse_multi_lo_single_sw_undefined_behaviour where
"no_vsse_multi_lo_single_sw_undefined_behaviour Xo Xw lo = 
   (\<not> (los_single_sw_data_races' Xo Xw lo = {}) \<or>
  \<not>  (unsequenced_races (actions Xo) (sb Xo) = {}) \<or>
  \<not>  (indeterminate_reads (actions Xo) (rf Xw) = {}) \<or>
  \<not>  (bad_mutexes Xo lo = {}))"

(*   - 7.1  - single step mutex synchronisation top level judgement *)
definition no_vsse_multi_lo_single_sw_cmm where
"no_vsse_multi_lo_single_sw_cmm opsem p = 
   (case { (Xopsem,(Xwitness,lo)).
      opsem p Xopsem \<and> no_vsse_multi_lo_single_sw_consistent_execution Xopsem Xwitness lo}
       of pre_executions \<Rightarrow>
       if (\<exists> (Xo,(Xw,lo)) \<in> pre_executions . no_vsse_multi_lo_single_sw_undefined_behaviour Xo Xw lo)
        then { (Xo,(Xw,lo)) . True } else pre_executions)"

(* 8 - Model simplified for programs without consumes *)
(* This model is simplified for use with programs that don't use
   consume memory orders. Happens-before is transitive. *)

fun no_vsse_consume_happens_before where
"no_vsse_consume_happens_before sb' sw = tc (sb' \<union> sw)"

fun no_vsse_consume_consistent_happens_before where
"no_vsse_consume_consistent_happens_before as hb = irrefl as hb"

fun no_vsse_consume_consistent_execution where
"no_vsse_consume_consistent_execution Xo Xw = 
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
     (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) (sc Xw) rs hrs of sw \<Rightarrow>
           (case no_vsse_consume_happens_before (sb Xo) sw of hb \<Rightarrow> 
            (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
    consistent_locks (actions Xo) (sc Xw) hb \<and>
    no_vsse_consume_consistent_happens_before (actions Xo) hb \<and>
    consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
    consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
    well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
    no_vsse_consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse))))))"

fun no_vsse_consume_data_races' where
"no_vsse_consume_data_races' Xo Xw lo = 
    (case release_sequence_set (actions Xo) (lk Xo) (mo Xw) of rs \<Rightarrow>
      (case hypothetical_release_sequence_set (actions Xo) (lk Xo) (mo Xw) of hrs \<Rightarrow>
       (case synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo rs hrs of sw \<Rightarrow>
          (case no_vsse_consume_happens_before (sb Xo) sw of hb \<Rightarrow>
      data_races (actions Xo) hb))))"

fun no_vsse_consume_undefined_behaviour where
"no_vsse_consume_undefined_behaviour Xo Xw = 
  (\<not> (no_vsse_consume_data_races' Xo Xw (sc Xw) = {}) \<or>
  \<not> (unsequenced_races   (actions Xo) (sb Xo)  = {}) \<or>
  \<not> (indeterminate_reads (actions Xo) (rf Xw) = {}) \<or>
  \<not> (bad_mutexes Xo (sc Xw) = {}))"

(*   - 8.1  - No consume top level judgement *)
definition no_vsse_consume_cmm where
"no_vsse_consume_cmm opsem p = 
   (case { (Xopsem,Xwitness).
      opsem p Xopsem \<and> no_vsse_consume_consistent_execution Xopsem Xwitness}
       of pre_executions \<Rightarrow>
       if (\<exists> (Xo,Xw) \<in> pre_executions . no_vsse_consume_undefined_behaviour Xo Xw)
        then { (Xo,Xw) . True } else pre_executions)"

(* 9 - Model simplified for programs without consumes or relaxed *)
(* Without relaxed, can release sequences go? Unfortunately not. This model is NOT equvalent. *)
fun no_vsse_consume_relaxed_synchronizes_with where
"no_vsse_consume_relaxed_synchronizes_with as sb' asw' rf' lo a b = 
   ((a,b) \<in> asw' \<or>
    ( same_location a b \<and> a \<in> as \<and> b \<in> as \<and>
      ((is_unlock a \<and> is_lock b \<and> (a,b) \<in> lo) \<or>
        ( is_release a \<and> is_acquire b \<and> \<not> (same_thread a b) \<and> (a,b) \<in> rf' ) ) ))"

fun no_vsse_consume_relaxed_synchronizes_with_set where
"no_vsse_consume_relaxed_synchronizes_with_set as sb' asw' rf' lo =
  {(a,b) . a \<in> as \<and> b \<in> as \<and> no_vsse_consume_relaxed_synchronizes_with as sb' asw' rf' lo a b}"

fun no_vsse_consume_relaxed_consistent_execution where
"no_vsse_consume_relaxed_consistent_execution Xo Xw = 
   (well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo) \<and>
       (case no_vsse_consume_relaxed_synchronizes_with_set
                  (actions Xo) (sb Xo) (asw Xo) (rf Xw) (sc Xw) of sw \<Rightarrow>
           (case no_vsse_consume_happens_before (sb Xo) sw of hb \<Rightarrow> 
            (case visible_side_effect_set (actions Xo) hb of vse \<Rightarrow>
    consistent_locks (actions Xo) (sc Xw) hb \<and>
    no_vsse_consume_consistent_happens_before (actions Xo) hb \<and>
    consistent_sc_order (actions Xo) (mo Xw) (sc Xw) hb \<and>
    consistent_modification_order (actions Xo) (lk Xo) (sb Xo) (mo Xw) hb \<and>
    well_formed_reads_from_mapping (actions Xo) (lk Xo) (rf Xw) \<and>
    no_vsse_consistent_reads_from_mapping (actions Xo) (lk Xo) (sb Xo) (rf Xw) (sc Xw) (mo Xw) hb vse))))"

fun no_vsse_consume_relaxed_data_races' where
"no_vsse_consume_relaxed_data_races' Xo Xw lo = 
       (case no_vsse_consume_relaxed_synchronizes_with_set
                   (actions Xo) (sb Xo) (asw Xo) (rf Xw) lo of sw \<Rightarrow>
          (case no_vsse_consume_happens_before (sb Xo) sw of hb \<Rightarrow>
      data_races (actions Xo) hb))"

fun no_vsse_consume_relaxed_undefined_behaviour where
"no_vsse_consume_relaxed_undefined_behaviour Xo Xw = 
  (\<not> (no_vsse_consume_relaxed_data_races' Xo Xw (sc Xw) = {}) \<or>
  \<not> (unsequenced_races   (actions Xo) (sb Xo)  = {}) \<or>
  \<not> (indeterminate_reads (actions Xo) (rf Xw) = {}) \<or>
  \<not> (bad_mutexes Xo (sc Xw) = {}))"

(*   - 9.1  - No consume or relaxed top level judgement *)
definition no_vsse_consume_relaxed_cmm where
"no_vsse_consume_relaxed_cmm opsem p = 
   (case { (Xopsem,Xwitness).
      opsem p Xopsem \<and> no_vsse_consume_relaxed_consistent_execution Xopsem Xwitness}
       of pre_executions \<Rightarrow>
       if (\<exists> (Xo,Xw) \<in> pre_executions . no_vsse_consume_relaxed_undefined_behaviour Xo Xw)
        then { (Xo,Xw) . True } else pre_executions)"

(* 10 - Model simplified for programs without consumes, relaxed, acquires or releases *)
fun consistent_total_order where
"consistent_total_order as sb' asw' tot = 
   (strict_total_order_over as tot \<and> (sb' \<subseteq> tot) \<and> (asw' \<subseteq> tot))"

fun tot_consistent_reads_from_mapping where
"tot_consistent_reads_from_mapping as lk' rf' tot = 
  (\<forall> b \<in> as .
    (is_read b) \<longrightarrow>
     (case { a . a \<in> as \<and> (same_location a b) \<and> is_write a} of writes_at_same_location \<Rightarrow>
       if (\<exists> a \<in> as .adjacent_less_than 
              (restrict_relation_set tot (writes_at_same_location \<union> {b})) as a b)
       then (\<exists> a \<in> as .
          ((a,b) \<in> rf') \<and>
          adjacent_less_than (restrict_relation_set tot (writes_at_same_location \<union> {b})) as a b)
       else \<not> (\<exists> a \<in> as . (a,b) \<in> rf')))"

fun tot_consistent_execution where
"tot_consistent_execution Xo rf' tot = 
   (case restrict_relation_set tot { a . a \<in> actions Xo \<and> (is_lock a \<or> is_unlock a)} of lo \<Rightarrow> 
      well_formed_threads (actions Xo) (threads Xo) (lk Xo) (sb Xo) (asw Xo) (dd Xo) (cd Xo)
     \<and>  consistent_total_order (actions Xo) (sb Xo) (asw Xo) tot
     \<and> consistent_locks (actions Xo) lo tot
     \<and> tot_consistent_reads_from_mapping (actions Xo) (lk Xo) rf' tot
     \<and> well_formed_reads_from_mapping (actions Xo) (lk Xo) rf')"

fun tot_hb_data_races where
"tot_hb_data_races Xo rf' tot =
   (case tot \<inter> {(a,b) . a \<in> (actions Xo) \<and> b \<in> (actions Xo) \<and> is_seq_cst a \<and>is_seq_cst b} of sc' \<Rightarrow>
    (case tot \<inter> {(a,b) . a \<in> (actions Xo) \<and> b \<in> (actions Xo) \<and>
                    (same_location a b) \<and> is_write a \<and> is_write b} of mo' \<Rightarrow>
     (case no_vsse_consume_relaxed_synchronizes_with_set (actions Xo) (sb Xo) (asw Xo) rf' tot of sw' \<Rightarrow>
     (case no_vsse_consume_happens_before (sb Xo) sw' of hb \<Rightarrow>
        data_races (actions Xo) hb))))"

fun tot_data_races where
"tot_data_races as tot = 
  { (a,b) . a \<in> as \<and> b \<in> as \<and>
       \<not> (a = b) \<and> same_location a b \<and> (is_write a \<or> is_write b) \<and>
        \<not> (same_thread a b) \<and>
        \<not> (is_atomic_action a \<and> is_atomic_action b) \<and>
        (adjacent_less_than tot as a b \<or> adjacent_less_than tot as b a) }"

fun tot_undefined_behaviour where
"tot_undefined_behaviour Xo rf' tot = 
  (\<not> (tot_hb_data_races Xo rf' tot = {}) \<or>
  \<not> (unsequenced_races   (actions Xo) (sb Xo)  = {}) \<or>
  \<not> (indeterminate_reads (actions Xo) rf' = {}) \<or>
  \<not> (bad_mutexes Xo tot = {}))"

(*   - 10.1  - No consume, relaxed, acquire or release top level judgement *)
definition tot_cmm where
"tot_cmm opsem p = 
   (case { (Xopsem,(rf,tot)).
      opsem p Xopsem \<and> tot_consistent_execution Xopsem rf tot}
       of pre_executions \<Rightarrow>
       if (\<exists> (Xo,(rf,tot)) \<in> pre_executions . tot_undefined_behaviour Xo rf tot)
        then { (Xo,(rf,tot)) . True } else pre_executions)"



end