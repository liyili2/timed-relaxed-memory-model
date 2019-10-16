(* memory_model.thy *)
(* William Mansky *)
(* Memory model locales for PTRANS. *)

theory memory_model
imports "$AFP/List-Infinite/ListInfinite" AxiomaticModel
begin

(*
print_locale "ord"

instantiation option :: (ord) ord
begin
fun less_eq_option where
   "(None \<le> None) = True"
 | "(None \<le> (Some _ )) = True"
 | "((Some _) \<le> None) = False"
 | "((Some x) \<le> (Some y)) = (x \<le> y)"

fun less_option where
   "(None < None) = False"
 | "(None < (Some _)) = True"
 | "((Some _) < None) = False"
 | "((Some x) < (Some y)) = (x < y)"

instance proof qed
end

lemma map_add_dom_upd [simp]: "dom m' = {k} \<Longrightarrow> (m ++ m')(k \<mapsto> v) = m(k \<mapsto> v)"
by (auto intro!: ext simp add: map_add_def split: option.splits)

lemma dud_set [simp]: "{(l, v). False} = {}"
by simp

(* Extra utility function: enumerate the elements of a set in arbitrary order. 
   Useful for memory models. Could conceivably be replaced by Eps over finite_distinct_list. *)
thm finite_distinct_list
function list_of_set where
"list_of_set S = (if infinite S \<or> S = {} then [] else let a = SOME a. a \<in> S in a # list_of_set (S - {a}))"
by pat_completeness auto
termination 
apply (relation "measure (\<lambda>S. card S)", auto)
apply (frule card_Diff_singleton, rule someI, simp)
apply (case_tac "card S", simp_all)
done
lemma list_of_set_empty [simp]: "list_of_set {} = []"
by simp
lemma list_of_set_inf [simp]: "infinite S \<Longrightarrow> list_of_set S = []"
by simp
lemma list_of_set_card [simp]: "(list_of_set S \<noteq> []) = (card S \<noteq> 0)"
by (auto simp add: Let_def)
declare list_of_set.simps [simp del]

lemma set_some [simp]: "S \<noteq> {} \<Longrightarrow> insert (SOME a. a \<in> S) S = S"
by (metis insert_absorb not_ex_in_conv someI)

lemma set_some2 [simp]: "S \<noteq> {} \<Longrightarrow> (SOME a. a \<in> S) \<in> S"
by (metis not_ex_in_conv someI)

lemma list_of_set_set [simp]: "finite S \<Longrightarrow> set (list_of_set S) = S"
apply (induct "card S" arbitrary: S, simp_all)
apply (rule trans, simp add: list_of_set.simps, simp add: Let_def)
done

corollary list_of_set_nth: "\<lbrakk>list_of_set S ! i = x; i < length (list_of_set S)\<rbrakk> \<Longrightarrow> x \<in> S"
apply (subgoal_tac "finite S", subgoal_tac "x \<in> set (list_of_set S)", simp, 
 simp add: set_conv_nth, force)
apply (auto simp add: list_of_set.simps split: if_splits)
done

lemma list_of_set_distinct [simp]: "distinct (list_of_set S)"
apply (induct "card S" arbitrary: S, clarsimp simp add: list_of_set.simps)
apply (rule_tac P=distinct in list_of_set.simps [THEN sym [THEN subst]], clarsimp simp add: Let_def)
done  

datatype ('thread, 'loc, 'val) access = Read 'thread 'loc 'val | Write 'thread 'loc 'val 
  | ARW 'thread 'loc 'val 'val | Alloc 'thread 'loc | Free 'thread 'loc
primrec get_thread where
"get_thread (Read t _ _) = t" |
"get_thread (Write t _ _) = t" |
"get_thread (ARW t _ _ _) = t" |
"get_thread (Alloc t _) = t" |
"get_thread (Free t _) = t"
primrec get_loc where
"get_loc (Read _ l _) = l" |
"get_loc (Write _ l _) = l" |
"get_loc (ARW _ l _ _) = l" |
"get_loc (Alloc _ l) = l" |
"get_loc (Free _ l) = l"
primrec set_thread where
"set_thread t' (Read t l v) = Read t' l v" |
"set_thread t' (Write t l v) = Write t' l v" |
"set_thread t' (ARW t l v v') = ARW t' l v v'" |
"set_thread t' (Alloc t l) = Alloc t' l" |
"set_thread t' (Free t l) = Free t' l"
lemma set_get_thread [simp]: "set_thread (get_thread a) a = a"
by (case_tac a, auto)
lemma get_set_thread [simp]: "get_thread (set_thread t a) = t"
by (case_tac a, auto)
lemma set_thread_frees [simp]: "set_thread t' ` Free t ` S = Free t' ` S"
by (auto simp add: image_def)

abbreviation "get_ptrs ops \<equiv> get_loc ` ops"


type_synonym ('block, 'os) pointer = "'block * 'os"
type_synonym ('add, 'size) block_structure = "'add * 'size"

datatype ('add,'val,'size,'os) raw_block =
    RawBlk "('add, 'size) block_structure" "('os \<rightharpoonup> 'val)"

type_synonym ('add, 'val, 'size) allocation = "(('add, 'size) block_structure) set"

type_synonym ('add,'val,'size,'os) block_allocation = "('add,'val,'size,'os) raw_block set"

fun get_addr_s where
  "get_addr_s ((addr,_)::(('add,'size) block_structure)) = addr"

fun get_size_s where
  "get_size_s ((_,s)::(('add,'size) block_structure)) = s"

fun get_addr where "get_addr ( RawBlk (addr,_) _) = addr"

fun get_size where "get_size (RawBlk(_,s) _) = s"

fun block_to_struct where "block_to_struct (RawBlk blk _) = blk"

declare[[show_types = true]]
declare[[show_sorts = true]]
  
(* locale for reasoning about blocks and the mapping of block offsets to memory locations *)
(* FUNCTIONS *)
(* block_s_start: partial function giving the first memory location of a 
    block_structure (if it exists) 
   block_exists: see assumptions for block existence conditions 
   block_start_os: gives the offset of a block that can be passed into block_s_ptr
    such that the same memory location is returned as for block_s_start 
   block_s_ptr: partial function mapping offsets into a block to memory locations 
   size_to_offset: conversion between abstract types *)
(* ASSUMPTIONS *)
(* block_firstlast_offset: if a block exists, the start offset must be \<le> the offset
    returned by calling size_to_offset on the block size (corresponds to the last memory
    location of the block.
   pointer_inbounds_exists: For any offset into a block that is between the start 
    and end offsets (inclusive), there must be a valid mapping to a memory location for
    that offset.
   block_s_same_add_same_loc: Two blocks with the same starting address must also have
    the same starting memory location.
   block_s_ptr_monotonic: block_s_ptr is a monotonic function
   block_s_ptr_one_to_one: block_s_ptr is a one to one function
   block_s_start_offset: Assumes that block_start_os is a total function. There will
    exist an offset such that block_s_ptr and block_s_start will be equal (even if
    it is because they both return None) *)
locale block_structure =
  fixes block_s_start::"('add, 'size::ord) block_structure \<rightharpoonup> ('loc::ord)"
    and block_exists::"('add, 'size::ord) block_structure \<Rightarrow> bool"
    and block_start_os :: "('add, 'size::ord) block_structure \<Rightarrow> ('os::{ord,plus})"
    and block_s_ptr::"('add, 'size) block_structure * 'os \<rightharpoonup> ('loc::ord)"
    and size_to_offset::"'size \<Rightarrow> 'os"
    and struct_to_rb::"('add,'size) block_structure \<Rightarrow> ('add,'val,'size,'os) raw_block"
  assumes block_exists_defin: "block_exists blk = (\<exists>x. block_s_start(blk) = (Some x))"
      and block_firstlast_offset:
          "block_exists (addr,size1) \<Longrightarrow>
           (block_start_os (addr,size1)) \<le> (size_to_offset size1)"
      and pointer_inbounds_exists:
          "\<lbrakk>block_exists (addr,size1); os \<ge> block_start_os(addr,size1); 
            os \<le> size_to_offset(size1)\<rbrakk> \<Longrightarrow>
           \<exists> l. (block_s_ptr ((addr,size1),os) = (Some l))"
      and block_s_same_add_same_loc:
        "\<lbrakk>block_exists (add, size1); block_exists (add, size2)\<rbrakk> \<Longrightarrow>
        block_s_start (add,size1) = block_s_start(add, size2)"
      and block_s_ptr_monotonic: "\<lbrakk>os1 < os2; block_s_ptr(blk,os1) = Some x;
                                   block_s_ptr(blk,os2) = Some y\<rbrakk> \<Longrightarrow> x < y"
      and block_s_ptr_one_to_one: "\<lbrakk>block_s_ptr(blk,os1) = Some x;
                                   block_s_ptr(blk,os2) = Some y;
                                   (x = y)\<rbrakk> \<Longrightarrow> (os1 = os2)"
      and block_s_start_offset: "\<exists>os_1. block_s_ptr(blk,os_1) = block_s_start(blk)"
      and block_s_start_defin: "(block_s_start blk = block_s_ptr(blk,(block_start_os blk)))"
context block_structure
begin

fun good_block_s_ptr where
  "good_block_s_ptr ((start,len), os) = ((block_exists (start,len)) \<and> 
  ((block_start_os (start,len)) \<le> os) \<and> (os \<le> (size_to_offset len)))"

fun good_rb_s_pair where
  "good_rb_s_pair blk1 blk2 =
  ((\<exists> os_1. (\<exists> os_2. ((good_block_s_ptr(blk1,os_1)) \<and>
                      (good_block_s_ptr(blk2,os_2)) \<and>
                      ((good_block_s_ptr(blk1,os_1)) = (good_block_s_ptr(blk2,os_2)))))) \<longrightarrow>
   (blk1 = blk2))"
  
fun good_allocation where
  "good_allocation (alloc::('add,'val,'size) allocation) = 
  (\<forall> rb1 \<in> alloc. (\<forall> rb2 \<in> alloc. (good_rb_s_pair rb1 rb2)))"
  
fun good_block_allocation where
  "good_block_allocation (alloc::('add,'val,'size,'os) block_allocation) =
  good_allocation (block_to_struct ` alloc)"

lemma good_rb_s_pair_refl [simp]: "good_rb_s_pair a a"
apply auto
done
lemma good_rb_s_pair_symm [simp]: "good_rb_s_pair a b = good_rb_s_pair b a"
apply auto
done
lemma good_rb_s_pair_trans [simp]: "((good_allocation alloc) \<and> 
  (a \<in> alloc) \<and> (b \<in> alloc) \<and> (c \<in> alloc) \<and> 
  (good_rb_s_pair a b) \<and> (good_rb_s_pair b c) \<longrightarrow> good_rb_s_pair a c)"
apply auto
done
end

type_synonym ('block,'size, 'os) access_region = "('block * 'size * 'os)"

type_synonym ('add,'val,'size,'os) block_access_region =
    "(('add,'val,'size,'os) raw_block,'size,'os) access_region"
    
type_synonym ('add,'val,'size,'os) block_s_access_region =
    "(('add,'size) block_structure,'size,'os) access_region"

fun region_get_block where
  "region_get_block ((b,s,os)::('block,'size, 'os) access_region) = b"
   
context block_structure
begin

 (* Define the set of ptr or os that are "in" a region *)
fun os_in_region where
  "os_in_region ((b,s,os1)::('add,'val,'size,'os) block_access_region) (os2::'os) = 
    ((((block_start_os (block_to_struct b))+os1) \<le> os2) \<and> 
    (((block_start_os (block_to_struct b))+os1+(size_to_offset s)) \<ge> os2))"

fun region_eq where
  "region_eq ((b1, s1, os1)::('add,'val,'size,'os) block_access_region)
  ((b2, s2, os2)::('add,'val,'size,'os) block_access_region) = 
  ((block_s_ptr((block_to_struct b1),os1) = block_s_ptr((block_to_struct b2),os2))
  \<and> (block_s_ptr((block_to_struct b1),(os1+(size_to_offset s1))) = 
  block_s_ptr((block_to_struct b2),(os2+(size_to_offset s2)))))"

lemma region_eq_all_ptr:
  "region_eq (b1,s1,os1) (b2, s2, os2) \<Longrightarrow> (\<forall> (os_a::'os). \<exists> (os_b::'os).
    (((os_in_region (b1,s1,os1) os_a) \<and> (os_in_region (b2,s2,os2) os_b))
    \<and> (block_s_ptr((block_to_struct b1),os_a)) = block_s_ptr((block_to_struct b2),os_b)))"
  oops
   
fun region_overlap where
  "region_overlap ((b1, s1, os1)::('add,'val,'size,'os) block_access_region)
  ((b2, s2, os2)::(('add,'val,'size,'os) block_access_region)) = (\<exists> (os_a::'os). 
  (\<exists> (os_b::'os). ((os_a \<ge> os1) \<and> (os_b \<ge> os2) \<and> (os_a \<le> (os1+(size_to_offset s1))) \<and>
  (os_b \<le> (os2+(size_to_offset s2))) \<and> (block_s_ptr((block_to_struct b1),os_a)) = 
  block_s_ptr((block_to_struct b2),os_b))))"

fun region_inbounds where
  "region_inbounds ((b, s, os)::('add,'val,'size,'os) block_access_region)
  = (((os + (size_to_offset s)) \<le> (size_to_offset (get_size b))) \<and> 
  (block_start_os((block_to_struct b)) \<le> os))"
  
(* tells us if a region describes an entire block *)
fun region_block_eq where
  "region_block_eq ((b, s, os)::('add,'val,'size,'os) block_access_region)
  = ((block_start_os((block_to_struct b)) = os) \<and> ((get_size_s(block_to_struct b)) = s))"
end

declare[[show_types = true]] 
declare[[show_sorts = true]]
*)

context axiomaticModel begin

term observeMem

end

locale memory_model = axiomaticModel
  where actions =  "actions :: (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action set"
    and locations = "locations :: loc_type set"
    and actionIDs = "actionIDs :: aid_type set"
    and times = "times :: time_type set"
    and threads = "threads :: 'tid set"
    and locks = "locks :: 'lock set"
    and names = "names :: 'name set"
    and callIDs = "callIDs :: 'callID set" 
  for actions locations actionIDs times threads locks names callIDs + 
  fixes free_set::"(('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
             \<Rightarrow> time_type \<Rightarrow> loc_type set"
and can_read::"(('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
            \<Rightarrow>'tid \<Rightarrow> time_type \<Rightarrow> loc_type \<Rightarrow> 'val set"
and update_mem::"(('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)
                       \<Rightarrow> time_type \<Rightarrow> ('tid \<times> aid_type \<times>
                             (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) set
                        \<Rightarrow> (('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option) \<Rightarrow> bool"
and start_mem:: "(('tid \<times> time_type \<times> loc_type)
            \<Rightarrow> (aid_type \<times> (aid_type, 'val, loc_type, 'lock, 'name, 'callID) action) option)"
assumes alloc_not_free: "\<lbrakk>update_mem mem time ops mem'; (tid,aid,Create l) \<in> ops\<rbrakk> \<Longrightarrow> 
 l \<notin> free_set mem' time"
    and stays_not_free: "\<lbrakk>update_mem mem time ops mem'; l \<notin> free_set mem time\<rbrakk> \<Longrightarrow>
 l \<notin> free_set mem' time"


 (*
datatype ('thread, 'add, 'size,'os) block_access =
    bRead 'thread "('add,'size,'os) block_s_access_region" 'val
  | bWrite 'thread "('add,'size,'os) block_s_access_region" 'val
  | bARW 'thread "('add,'size,'os) block_s_access_region" 'val 'val
  | bAlloc 'thread "('add,'size) block_structure"
  | bFree 'thread "('add,'size) block_structure"
  
datatype ('thread, 'block, 'region,'val) block_access =
    bRead 'thread 'region 'val
  | bWrite 'thread 'region 'val
  | bARW 'thread 'region 'val 'val
  | bAlloc 'thread 'block
  | bFree 'thread 'block
*)

(*
locale block_structur =
  fixes good_block ::"'block \<Rightarrow> bool"
    and good_region :: "'region \<Rightarrow> bool"
    and block_overlap::"'block \<Rightarrow> 'block \<Rightarrow> bool"
    and region_overlap::"'region \<Rightarrow> 'region \<Rightarrow> bool"
    and subblock::"'block \<Rightarrow> 'block \<Rightarrow> bool"
    and subregion :: "'region \<Rightarrow> 'region \<Rightarrow> bool"
    and region_get_block ::"'region \<Rightarrow> 'block"
    and block_as_region ::"'block \<Rightarrow> 'region"
    and value_fits_region :: "'val \<Rightarrow> 'region \<Rightarrow> bool"
    and region_fits_block ::"'region \<Rightarrow> 'block \<Rightarrow> bool"
    (* define does_not_modify later *)
    and does_not_modify :: "('thread, 'block, 'region,'val) block_access 
        \<Rightarrow> 'region \<Rightarrow>  bool" 
   (* and get_access_region:: "('thread, 'block, 'region,'val) block_access \<Rightarrow> 'region"*)
  assumes value_fits_bigger_region :
    "\<lbrakk> subregion r1 r2; value_fits_region v r1 \<rbrakk> \<Longrightarrow> value_fits_region v r2"
  and subblock_good: "\<lbrakk>good_block b ; subblock b' b\<rbrakk> \<Longrightarrow> good_block b'"
  and region_overlap_symm: "region_overlap r r' \<Longrightarrow> region_overlap r' r"
(*  and dummy: "\<exists> b. block_as_region b = block_as_region b" *)

fun (in block_structur) get_access_region::"('thread, 'block, 'region,'val) block_access \<Rightarrow> 'region" where
  "get_access_region (bRead _ r _) = r" |
  "get_access_region (bWrite _ r _) = r" |
  "get_access_region (bARW _ r _ _) = r" |
  "get_access_region (bAlloc _ b) = (block_as_region b)" |
  "get_access_region (bFree _ b) = (block_as_region b)"
thm block_structur.get_access_region.simps
thm block_structur_def

locale basic_can_do = block_structur
  where     good_block = "good_block :: 'block \<Rightarrow> bool"
    and     good_region = "good_region :: 'region \<Rightarrow> bool"
  for       good_block 
    and     good_region +
  fixes     can_do::"('thread, 'block, 'region,'val) block_access list \<Rightarrow> 
            ('thread, 'block, 'region,'val) block_access \<Rightarrow> bool"
  assumes   base_allows_alloc: "good_block b \<Longrightarrow> (can_do [] (bAlloc t b))"     
    and     free_allows_alloc: "\<lbrakk>good_block b; can_do m (bFree t b); subblock b' b\<rbrakk>
            \<Longrightarrow> (can_do ((bFree t b)#m) (bAlloc t' b'))"
    and     alloc_allows_free: "\<lbrakk>good_block b; can_do m (bAlloc t b)\<rbrakk> \<Longrightarrow> 
            (can_do ((bAlloc t b)#m) (bFree t b))"
   (* and     alloc_allows_write: "\<lbrakk>good_block b; can_do m (bAlloc t b); 
            region_fits_block r b\<rbrakk> \<Longrightarrow> 
            (can_do ((bAlloc t b)#m) (bWrite t' r v))"*)
    and     alloc_allows_write_same_thread: "\<lbrakk>good_block b; can_do m (bAlloc t b); 
            region_fits_block r b\<rbrakk> \<Longrightarrow> 
            (can_do ((bAlloc t b)#m) (bWrite t r v))"
    and     write_any_value_same_thread: "\<lbrakk>value_fits_region v' r; 
            (can_do m (bWrite t r v))\<rbrakk> \<Longrightarrow> (can_do m (bWrite t r v'))"
    and     not_mod_write_drop: "\<lbrakk>can_do m opr; does_not_modify opr r; 
            can_do (opr#m) (bWrite t r v)\<rbrakk> 
            \<Longrightarrow> can_do m (bWrite t r v)"
    and     not_mod_write_add: "\<lbrakk>can_do m opr; does_not_modify opr r;
            can_do m (bWrite t r v)\<rbrakk> \<Longrightarrow> can_do (opr#m) (bWrite t r v)"
    and     write_not_read_drop: "\<lbrakk>can_do m (bWrite t r v); 
            \<forall>r' v' .(region_overlap r r') \<longrightarrow> (opr \<noteq> (bRead t' r' v'));
            can_do ((bWrite t r v)#m) opr\<rbrakk> \<Longrightarrow> can_do m opr"
    and     write_not_read_add: "\<lbrakk>can_do m (bWrite t r v); 
            \<forall>r' v' .(region_overlap r r') \<longrightarrow> (opr \<noteq> (bRead t' r' v'));
            can_do m opr\<rbrakk> \<Longrightarrow> can_do ((bWrite t r v)#m) opr"
    and     read_only_written: "\<lbrakk>can_do m (bWrite t r v); 
            can_do ((bWrite t r v)#m) (bRead t' r v')\<rbrakk> \<Longrightarrow> v = v'"
    and     read_written: "can_do m (bWrite t r v) \<Longrightarrow>
            can_do ((bWrite t r v)#m) (bRead t' r v)"
    and     read_noop_drop: "\<lbrakk>can_do m (bRead t r v); can_do ((bRead t r v)#m) opr\<rbrakk>
            \<Longrightarrow> can_do m opr"
    and     read_noop_add: "\<lbrakk>can_do m (bRead t r v); can_do m opr\<rbrakk>
            \<Longrightarrow> can_do ((bRead t r v)#m) opr"
    and     reg_drop: "\<lbrakk>\<not>(region_overlap (get_access_region opr) (get_access_region opr'));
            can_do m opr; can_do (opr#m) opr'\<rbrakk> \<Longrightarrow> can_do m opr'"
    and     reg_add: "\<lbrakk>\<not>(region_overlap (get_access_region opr) (get_access_region opr'));
            can_do m opr; can_do m opr'\<rbrakk> \<Longrightarrow> can_do (opr#m) opr'"
    (*and     reg_comm: "\<lbrakk>\<not>(region_overlap (get_access_region opr) (get_access_region opr'));
            can_do (opr#m) opr'\<rbrakk> \<Longrightarrow> can_do (opr'#m) opr"*)
    and     prefix_closed: "\<lbrakk>can_do (opr#m) opr'\<rbrakk> \<Longrightarrow> can_do m opr"

lemma (in basic_can_do) reg_comm: "\<lbrakk>\<not>(region_overlap (get_access_region opr) (get_access_region opr'));
            can_do (opr#m) opr'\<rbrakk> \<Longrightarrow> can_do (opr'#m) opr"
apply (rule reg_add)
apply (erule contrapos_nn)
apply (erule_tac r = "(get_access_region opr')" and r' = "(get_access_region opr)"
       in region_overlap_symm)
prefer 2
apply (erule prefix_closed)
apply (erule reg_drop)
apply (erule prefix_closed)
apply auto
done

            
  (* Commented out to the end
context block_structure
begin
primrec block_get_thread where
"block_get_thread (bRead t _ _) = t" |
"block_get_thread (bWrite t _ _) = t" |
"block_get_thread (bARW t _ _ _) = t" |
"block_get_thread (bAlloc t _) = t" |
"block_get_thread (bFree t _) = t"
fun block_get_region where
"block_get_region (bRead _ r  _) = r" |
"block_get_region (bWrite _ r _) = r" |
"block_get_region (bARW _ r  _ _) = r"|
"block_get_region (bAlloc _ b) = ((struct_to_rb b),(get_size_s b),(block_start_os(b)))" |
"block_get_region (bFree _ b) = ((struct_to_rb b),(get_size_s b),(block_start_os(b)))"
primrec block_get_block where
"block_get_block (bRead _ r _) = (region_get_block r)" |
"block_get_block (bWrite _ r _) = (region_get_block r)" |
"block_get_block (bARW _ r _ _) = (region_get_block r)" |
"block_get_block (bAlloc _ b) = (struct_to_rb b)" |
"block_get_block (bFree _ b) = (struct_to_rb b)"
primrec block_set_thread where
"block_set_thread t' (bRead t r v) = bRead t' r v" |
"block_set_thread t' (bWrite t r v) = bWrite t' r v" |
"block_set_thread t' (bARW t r v v') = bARW t' r v v'" |
"block_set_thread t' (bAlloc t l) = bAlloc t' l" |
"block_set_thread t' (bFree t l) = bFree t' l" 
end

 locale block_seq_can_do = fixes can_do::"('thread,'add,'val,'size,'os) 
  block_access list \<Rightarrow> ('thread,'add,'val,'size,'os) block_access \<Rightarrow> bool"
assumes base_allows_alloc: "(can_do [] (bAlloc t b))"
    and free_allows_alloc: "\<lbrakk>can_do m (bFree t b); b=b'\<rbrakk>
          \<Longrightarrow> (\<not>(can_do ((bFree t b)#m) (bFree t' b')))"
    and alloc_allows_write: "\<lbrakk>can_do m (bAlloc t b); 
          region_inbounds ((struct_to_block b),s,os)\<rbrakk> \<Longrightarrow> 
          (can_do ((bAlloc t b)#m) 
          (bWrite t' ((struct_to_block b),s,os) v))"
    and alloc_allows_alloc: "\<lbrakk>can_do m (bAlloc t b); b=b'\<rbrakk> \<Longrightarrow> 
          (\<not>(can_do ((bAlloc t b)#m) (bAlloc t' b')))"
    and alloc_allows_free: "\<lbrakk>can_do m (bAlloc t b); b=b'\<rbrakk> \<Longrightarrow> 
          (can_do ((bAlloc t b)#m) (bFree t' b'))"
    and write_any_value: "(can_do m (bWrite t r v)) = (can_do m (bWrite t' r v'))"(*
    and not_mod_write: "\<lbrakk>can_do m (bRead t' r' v'); can_do m (bWrite t' r' v'); 
      can_do m (bAlloc t' b); can_do m (bFree t' b); region_block_eq(b,s,os);
      \<not>(region_overlap r r'); \<not>(region_overlap r (b,s,os))\<rbrakk> \<Longrightarrow> 
      ((can_do ((bRead t' r' v')#m) (bWrite t r v)) = 
        (can_do (m) (bWrite t r v))) \<and> 
      ((can_do ((bWrite t' r' v')#m) (bWrite t r v)) = 
        (can_do (m) (bWrite t r v))) \<and> 
      ((can_do ((bAlloc t' b)#m) (bWrite t r v)) = 
        (can_do (m) (bWrite t r v))) \<and> 
      ((can_do ((bFree t' b)#m) (bWrite t r v)) = 
        (can_do (m) (bWrite t r v)))" 
    and write_not_read: "\<lbrakk>can_do m (bWrite t r v);  opr \<noteq> (bRead t' r v')\<rbrakk> \<Longrightarrow> 
      (can_do ((bWrite t r v)#m) opr) = (can_do m opr)"
    and read_written: "\<lbrakk>can_do m (bWrite t r v)\<rbrakk> \<Longrightarrow> ((can_do ((bWrite t r v)#m) 
      (bRead t' r v')) = (v = v'))"
    and read_noop: "\<lbrakk>can_do m (bRead t r v)\<rbrakk> \<Longrightarrow> (can_do ((bRead t r v)#m) opr = 
      can_do m opr)"*)(*
    and loc_drop: "\<lbrakk>\<not>region_overlap((block_get_region opr) (block_get_region opr'));
      (can_do m opr)\<rbrakk> \<Longrightarrow> (can_do (opr#m) opr') = (can_do m opr')"  
    and loc_comm: "\<lbrakk>\<not>region_overlap((block_get_region opr) (block_get_region opr'))\<rbrakk> 
      \<Longrightarrow> (can_do (opr#m) opr') = (can_do (opr'#m) opr)"*)
      
locale block_seq_can_do_extend = block_seq_can_do +
  assumes base_disallows_free:"(\<not>(can_do [] (bFree t b)))"
  and     free_dissallows_free:"\<lbrakk>can_do m (bFree t b); b=b'\<rbrakk>
          \<Longrightarrow> (\<not>(can_do ((bFree t b)#m) (bFree t' b')))"
 
 
locale seq_can_do = fixes can_do::"('thread, 'loc, 'val) access list \<Rightarrow>
  ('thread, 'loc, 'val) access \<Rightarrow> bool"
assumes base_allows: "(\<not>(can_do [] (Read t l v))) \<and> (can_do [] (Alloc t l))
  \<and>(\<not>(can_do [] (Free t l)))"
    and free_allows: "\<lbrakk>can_do m (Free t l)\<rbrakk> \<Longrightarrow> (\<not>(can_do ((Free t l)#m) (Read t' l v)))
      \<and> (can_do ((Free t l)#m) (Alloc t' l)) \<and> (\<not>(can_do ((Free t l)#m) (Free t' l)))"
    and alloc_allows: "\<lbrakk>can_do m (Alloc t l)\<rbrakk> \<Longrightarrow> (can_do ((Alloc t l)#m) (Write t l v))
      \<and> (\<not>(can_do ((Alloc t l)#m) (Alloc t' l))) \<and> (can_do ((Alloc t l)#m) (Free t l))"
    and write_any_value: "(can_do m (Write t l v)) = (can_do m (Write t l v'))"
    and not_mod_write: "\<lbrakk>can_do m (Read t l v); can_do m (Write t l' v); 
      can_do m (Alloc t l'); can_do m (Free t l'); l \<noteq> l'\<rbrakk> \<Longrightarrow> ((can_do ((Read t l v)#m) 
      (Write t' l v)) = (can_do (m) (Write t' l v))) \<and> ((can_do ((Write t l' v)#m) 
      (Write t' l v)) = (can_do (m) (Write t' l v))) \<and> ((can_do ((Alloc t l')#m) 
      (Write t' l v)) = (can_do (m) (Write t' l v))) \<and> ((can_do ((Free t l')#m) 
      (Write t' l v)) = (can_do (m) (Write t' l v)))" 
    and write_not_read: "\<lbrakk>can_do m (Write t l v);  opr \<noteq> (Read t' l v')\<rbrakk> \<Longrightarrow> 
      (can_do ((Write t l v)#m) opr) = (can_do m opr)"
    and read_written: "\<lbrakk>can_do m (Write t l v)\<rbrakk> \<Longrightarrow> ((can_do ((Write t l v)#m) 
      (Read t' l v')) = (v = v'))"
    and read_noop: "\<lbrakk>can_do m (Read t l v)\<rbrakk> \<Longrightarrow> (can_do ((Read t l v)#m) a = can_do m a)"
    and loc_drop: "\<lbrakk>get_loc (opr) \<noteq> get_loc(opr'); (can_do m opr)\<rbrakk> \<Longrightarrow> (can_do (opr#m) opr')
      = (can_do m opr')" 
    and loc_comm: "\<lbrakk>get_loc (opr) \<noteq> get_loc(opr')\<rbrakk> \<Longrightarrow> (can_do (opr#m) opr') = 
      (can_do (opr'#m) opr)"
      
    
(* how can we define a memory as only being a "good" allocation? *)
 locale block_memory_model = fixes free_set::"'memory \<Rightarrow> 'a word set"
and can_read::"'memory \<Rightarrow> 'thread \<Rightarrow> 'loc \<Rightarrow> 'block set"
and update_mem::"'memory \<Rightarrow> ('thread, 'loc, 'val) block_access set \<Rightarrow> 'memory \<Rightarrow> bool"
and allocation::"'loc allocation"
and start_mem::'memory
(*and memory_max_word:: "'loc::len word" *) (*largest address *) (* note: we may want to condense these into one *)
and memory_max_int:: int
and memory_min:: int (* smallest address *)           
(*assumes good_allocations: "\<lbrakk>update_mem mem ops mem'; good_allocation *)
(*assumes good_allocation_word: "good_allocation memory_max_word allocation"*)
assumes good_allocation_int: "good_allocation (word_of_int memory_max_int) allocation"



(* TSO memory model *)
locale TSO = fixes undef::'val begin
(* This isn't really a TSO-specific locale, but I might have other assumptions later.
   More to the point, it's convenient to have a separate locale for each memory model, even if
   they don't actually rely on separate assumptions. *)

abbreviation "free_set mem \<equiv> UNIV - dom (fst mem)"
definition "can_read mem t l \<equiv> case List.find (\<lambda>(l', v). l' = l) ((snd mem) t) of 
 Some (l, v) \<Rightarrow> {v} | None \<Rightarrow> {v. fst mem l = Some v}"
definition "can_read2 mem t l \<equiv> case mem of (mem_map, bufs) \<Rightarrow> (case List.find (\<lambda>(l', v). l' = l) (bufs t) of 
 Some (l, v) \<Rightarrow> {v} | None \<Rightarrow> {v. mem_map l = Some v})"
(* Switch to the inductive approach... sometime. *)
inductive update_mem where 
no_atomic [intro]: "\<lbrakk>\<And>t l v v'. ARW t l v v' \<notin> ops; \<And>t. \<exists>up. bufs' t = up @ bufs t \<and> 
 set up = {(l, v) | l v. Write t l v \<in> ops} \<and> distinct up\<rbrakk> \<Longrightarrow> 
 update_mem (mem, bufs) ops (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None), bufs')" |
update [intro]: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); bufs' t = buf @ [(l, v)]\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs) ops (mem'(l \<mapsto> v), bufs'(t := buf))" |
atomic [intro!]: "bufs t = [] \<Longrightarrow> update_mem (mem, bufs) {ARW t l v v'} (mem(l \<mapsto> v'), bufs)"
abbreviation "start_mem \<equiv> (empty, \<lambda>t. [])"

lemma alloc_not_free: "\<lbrakk>update_mem mem ops mem'; Alloc t l \<in> ops; \<forall>t. Free t l \<notin> ops\<rbrakk> \<Longrightarrow> 
 l \<notin> free_set mem'"
by (induct rule: update_mem.induct, auto split: if_splits)

lemma stays_not_free: "\<lbrakk>update_mem mem ops mem'; l \<notin> free_set mem; \<forall>t. Free t l \<notin> ops\<rbrakk> \<Longrightarrow>
 l \<notin> free_set mem'"
by (induct rule: update_mem.induct, auto split: if_splits)

end

sublocale TSO \<subseteq> memory_model free_set can_read update_mem start_mem
by (unfold_locales, metis alloc_not_free, metis stays_not_free)

context TSO begin

lemma update_none [intro!, simp]: "update_mem C {} C"
by (cases C, cut_tac ops="{}" and mem=a and bufs=b in no_atomic, auto simp add: restrict_map_def)

lemma can_read_thread: "\<lbrakk>v \<in> can_read (mem, b) t l; b t = b' t\<rbrakk> \<Longrightarrow> 
 v \<in> can_read (mem, b') t l"
by (auto simp add: can_read_def split: option.splits)

lemma first_entry: "\<lbrakk>update_mem (mem, bufs) {Write t l v} (mem', bufs'); 
 bufs' t = a # rest\<rbrakk> \<Longrightarrow> a = (l, v)"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). \<forall>a rest. ops = {Write t l v} \<and> 
 bufs' t = a # rest \<longrightarrow> a = (l, v)" in update_mem.induct, simp_all, clarsimp)
apply (subgoal_tac "\<exists>up. bufs'a t = up @ bufs t \<and> set up = {ab. t = t \<and> (case ab of (la, va) \<Rightarrow> 
 la = l \<and> va = v)} \<and> distinct up", clarify, simp+)
apply (case_tac up, simp, simp)
apply (thin_tac "bufs'a t = ((aa, b) # resta)", force)
apply auto
apply (cases a, auto)
done

lemma update_map: "update_mem (mem, bufs) {} (mem', bufs') \<Longrightarrow>
 \<exists>map. \<forall>mem2. update_mem (mem2, bufs) {} (mem2 ++ map, bufs')"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). ops = {} \<longrightarrow> 
 (\<exists>map. \<forall>mem2. update_mem (mem2, bufs) {} (mem2 ++ map, bufs'))" in update_mem.induct, auto)
apply (subgoal_tac "bufs' = bufs", rule_tac x=empty in exI, simp, rule ext)
apply (subgoal_tac "\<exists>up. bufs' x = (up @ bufs x) \<and> set up = {(l, v). False} \<and> distinct up", clarify, auto)
apply (rule_tac x="map(l \<mapsto> v)" in exI, auto)
done

lemma update_trans_rev: "\<lbrakk>update_mem (mem', bufs') {} (mem'', bufs'');
 update_mem (mem, bufs) ops (mem', bufs')\<rbrakk> \<Longrightarrow> update_mem (mem, bufs) ops (mem'', bufs'')"
apply (drule_tac P="\<lambda>(mem', bufs') ops' (mem'', bufs''). ops' = {} \<and> update_mem (mem, bufs) ops (mem', bufs') \<longrightarrow>
 update_mem (mem, bufs) ops (mem'', bufs'')" in update_mem.induct, auto simp add: restrict_map_def)
apply (subgoal_tac "bufs'a = bufsa", simp, rule ext)
apply (subgoal_tac "\<exists>up. bufs'a x = up @ bufsa x \<and> set up = {(l, v). False} \<and> distinct up", 
 clarify, auto)
done

lemma update_trans [trans]: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs');
 update_mem (mem', bufs') {} (mem'', bufs'')\<rbrakk> \<Longrightarrow> update_mem (mem, bufs) ops (mem'', bufs'')"
by (erule update_trans_rev, simp)

lemma update_canonical: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); 
 \<And>t l v v'. ARW t l v v' \<notin> ops\<rbrakk> \<Longrightarrow>
 \<exists>writes bufs''. (\<forall>t. bufs'' t = writes t @ bufs t \<and> set (writes t) = {(l, v) | l v. Write t l v \<in> ops} \<and> distinct (writes t)) \<and> 
 update_mem (mem, bufs) ops (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None), bufs'') \<and>
 update_mem (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None), bufs'') {} (mem', bufs')"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). (\<forall>t l v v'. ARW t l v v' \<notin> ops) \<longrightarrow>
 (\<exists>writes bufs''. (\<forall>t. bufs'' t = writes t @ bufs t \<and>
 set (writes t) = {(l, v) | l v. Write t l v \<in> ops} \<and> distinct (writes t)) \<and> update_mem (mem, bufs) ops 
 (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None), bufs'') \<and>
 update_mem (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None), bufs'') {} (mem', bufs'))" in update_mem.induct, auto)
apply (rule_tac x="\<lambda>t. SOME up. bufs' t = up @ bufs t \<and> set up = {(l, v). Write t l v \<in> opsa} \<and> 
 distinct up" in exI)
apply (rule_tac x=bufs' in exI)
apply (rule conjI, clarsimp)
apply (rule someI_ex, auto)
done

corollary update_write: "\<lbrakk>update_mem (mem, bufs) {Write t l v} (mem', bufs')\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs(t := (l, v) # bufs t)) {} (mem', bufs')"
apply (drule update_canonical, auto)
apply (subgoal_tac "bufs'' = bufs(t := (l, v) # bufs t)", simp add: restrict_map_def, rule ext, 
 clarsimp)
apply (erule_tac x=x in allE, rule conjI, clarsimp)
apply (case_tac "writes t", simp+, case_tac list, simp+)
apply clarsimp
done

lemma update_later: "\<lbrakk>update_mem (mem, bufs) {} (mem', bufs')\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs) {Write t l v} (mem', bufs'(t := (l, v) # bufs' t))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). ops = {} \<longrightarrow> 
 update_mem (mem, bufs) {Write t l v} (mem', bufs'(t := (l, v) # bufs' t))" in update_mem.induct, auto)
apply (cut_tac ops="{Write t l v}" in no_atomic, auto)
apply (drule_tac ops="{Write t l v}" in update, auto)
apply (drule_tac ops="{Write t l v}" and t=ta in update, auto)
by (metis (hide_lams, no_types) fun_upd_twist)

lemma update_later2: "\<lbrakk>update_mem (mem, bufs) {} (mem', bufs'(t := buf)); bufs' t = (l, v) # buf\<rbrakk> \<Longrightarrow> 
 update_mem (mem, bufs) {Write t l v} (mem', bufs')"
by (smt fun_upd_idem_iff fun_upd_upd list.inject update_later)

lemma update_past: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); t \<notin> get_thread ` ops\<rbrakk> \<Longrightarrow> 
 update_mem (mem, bufs(t := b @ bufs t)) ops (mem', bufs'(t := b @ bufs' t))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). t \<notin> get_thread ` ops \<longrightarrow> 
 update_mem (mem, bufs(t := b @ bufs t)) ops (mem', bufs'(t := b @ bufs' t))" 
 in update_mem.induct, auto)
apply (rule no_atomic, auto)
apply (rule_tac x="[]" in exI, simp)
apply (subgoal_tac "\<forall>a b. Write t a b \<notin> opsa", subgoal_tac "\<exists>up. bufs' t = up @ bufs t 
 \<and> set up = {(l, v). Write t l v \<in> opsa} \<and> distinct up", clarify, simp, metis, auto)
apply (metis get_thread.simps(2) imageI)
apply (drule_tac bufs="bufs(t := b @ bufs t)" in update, auto)
apply (drule_tac bufs="bufs(t := b @ bufs t)" and t=ta in update, auto)
apply (simp add: fun_upd_twist)
done

lemma update_past2: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); 
 \<And>l v. Write t l v \<notin> ops; \<And>l v v'. ARW t l v v' \<notin> ops\<rbrakk> \<Longrightarrow> 
 update_mem (mem, bufs(t := b @ bufs t)) ops (mem', bufs'(t := b @ bufs' t))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). (\<forall>l v. Write t l v \<notin> ops) \<and> 
 (\<forall>l v v'. ARW t l v v' \<notin> ops) \<longrightarrow> update_mem (mem, bufs(t := b @ bufs t)) ops (mem', bufs'(t := b @ bufs' t))" 
 in update_mem.induct, auto)
apply (rule no_atomic, auto)
apply (subgoal_tac "\<exists>up. bufs' t = up @ bufs t \<and> set up = {(l, v). Write t l v \<in> opsa} \<and> 
 distinct up", simp)
apply (metis (full_types))
apply (drule_tac bufs="bufs(t := b @ bufs t)" in update, auto)
apply (drule_tac bufs="bufs(t := b @ bufs t)" and t=ta in update, auto simp add: fun_upd_twist)
done

lemma process_buffer: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); bufs' t = a @ b\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs) ops (mem' ++ map_of b, bufs'(t := a))"
apply (induct b arbitrary: mem' bufs' rule: rev_induct, auto simp add: map_upd_triv)
apply (drule_tac t=t in update, auto)
apply force
done

end

(* assorted useful list lemmas*)
lemma map_upt_zip_Suc [simp]: "l' = map (\<lambda>(x, n). (x, Suc n)) l \<Longrightarrow> map (\<lambda>((l, v), n). (l, v) # map (Pair l) (f n)) l' =
 map (\<lambda>((l, v), n). (l, v) # map (Pair l) (f (Suc n))) l"
by auto

declare map_Suc_upt [simp]

lemma zip_Suc [simp]: "zip l [Suc i..<Suc j] = map (\<lambda>(x, n). (x, Suc n)) (zip l [i..<j])"
by (simp only: zip_map2 [THEN sym], simp)

(* The redundant store produces buffers with redundant elements.
   add_red is a general characterization of such buffers. *)
definition "add_red l f = 
 concat (map (\<lambda>((l, v), n). (l, v) # map (\<lambda>v. (l, v)) (f n)) (zip l [0..<length l]))"

lemma add_red_nil [simp]: "add_red [] f = []"
by (simp add: add_red_def)

lemma add_red_cons [simp]: "add_red (x # l) f = x # map (\<lambda>v. (fst x, v)) (f 0) @ add_red l (\<lambda>n. f (Suc n))"
apply (auto simp add: add_red_def)
apply (case_tac "map (\<lambda>((l, v), n). (l, v) # map (Pair l) (f n)) (zip (x # l) ([0..<length l] @ [length l]))", auto)
apply (case_tac "[0..<length l] @ [length l]", auto)
apply (case_tac "[0..<length l] @ [length l]", auto)
apply (case_tac "[0..<length l] @ [length l]", auto)
apply (cut_tac i=0 and j="Suc (length l)" and x=ba and xs=list in upt_eq_Cons_conv, auto)
apply (rule_tac f=concat in arg_cong)
apply (rule map_upt_zip_Suc)
by (metis upt_Suc_append zip_Suc)

lemma add_red_app [simp]: "add_red (l @ l') f = add_red l f @ add_red l' (\<lambda>n. f (n + length l))"
by (induct l arbitrary: f, auto)

lemma add_red_id [simp]: "(\<And>n. n < length l \<Longrightarrow> f n = []) \<Longrightarrow> add_red l f = l"
by (induct l arbitrary: f, auto)

lemma find_append: "(\<And>x. x \<in> set l \<Longrightarrow> \<not>P x) \<Longrightarrow> List.find P (l @ l') = List.find P l'"
by (induct l, auto)

lemma find_append2 [simp]: "List.find P l = None \<Longrightarrow> List.find P (l @ l') = List.find P l'"
by (induct l, auto)

lemma find_append3 [simp]: "List.find P l = Some x \<Longrightarrow> List.find P (l @ l') = Some x"
by (induct l, auto)

lemma add_red_find [simp]: "List.find (\<lambda>(l, v). l = x) (add_red buf f) = 
 List.find (\<lambda>(l, v). l = x) buf"
apply (induct buf arbitrary: f, auto)
apply (rule trans, rule find_append, auto)
done

context TSO begin

lemma update_red: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); \<And>t. red t = add_red (bufs t) (f t)\<rbrakk> \<Longrightarrow>
 \<exists>red' f'. update_mem (mem, red) ops (mem', red') \<and> (\<forall>t. red' t = add_red (bufs' t) (f' t))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). (\<forall>t. red t = add_red (bufs t) (f t)) \<longrightarrow> 
 (\<exists>red' f'. update_mem (mem, red) ops (mem', red') \<and> (\<forall>t. red' t = add_red (bufs' t) (f' t)))" 
 in update_mem.induct, auto)
apply (rule_tac x="\<lambda>t. (SOME up. bufs' t = up @ bufsa t \<and> set up = {(l, v). Write t l v \<in> ops} \<and> 
 distinct up) @ red t" in exI, auto)
apply (rule no_atomic, simp_all)
apply (cut_tac P="\<lambda>up. bufs' t = up @ bufsa t \<and> set up = {(l, v). Write t l v \<in> ops} \<and> 
 distinct up" in someI_ex, simp+)
apply (rule_tac x="\<lambda>t n. if n < length (SOME up. bufs' t = up @ bufsa t \<and> 
 set up = {(l, v). Write t l v \<in> ops} \<and> distinct up) then [] else f t (n - length (SOME up. 
 bufs' t = up @ bufsa t \<and> set up = {(l, v). Write t l v \<in> ops} \<and> distinct up))" in exI, clarsimp)
apply (subgoal_tac "\<exists>up. bufs' t = up @ bufsa t \<and> set up = {(l, v). Write t l v \<in> ops} \<and> distinct up", 
 clarify, clarsimp)
apply (cut_tac P="\<lambda>upa. up = upa \<and> set upa = {(l, v). Write t l v \<in> ops} \<and> distinct upa" in someI, 
 force, clarsimp)
apply metis
apply (drule_tac bufs=red and t=t and a="add_red buf (f' t)" in process_buffer, simp, clarsimp)
apply (subgoal_tac "dom (map_of (map (Pair l) (f' t (length buf)))) = {l} \<or> f' t (length buf) = []", 
 erule disjE, simp+)
apply (rule_tac x="red'(t := add_red buf (f' t))" in exI, clarsimp)
apply (rule_tac x=f' in exI, simp)
apply (rule_tac x="red'(t := add_red buf (f' t))" in exI, clarsimp)
apply (rule_tac x=f' in exI, simp)
apply (auto simp add: dom_map_of_conv_image_fst intro!: set_eqI)
apply (case_tac "f' t (length buf)", simp+)
apply (rule_tac x=red in exI, auto)+
done

lemma update_red1: "update_mem (mem, bufs) ops (mem', bufs') \<Longrightarrow>
 \<exists>f'. update_mem (mem, bufs(t := add_red (bufs t) f)) ops (mem', bufs'(t := add_red (bufs' t) f'))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). \<exists>f'. update_mem (mem, bufs(t := add_red (bufs t) f)) 
 ops (mem', bufs'(t := add_red (bufs' t) f'))" in update_mem.induct, auto)
apply (rule_tac x="\<lambda>n. if n < length (SOME x. bufs' t = x @ bufs t \<and> set x = {(l, v). Write t l v \<in> ops} \<and> distinct x) 
 then [] else f (n - length (SOME x. bufs' t = x @ bufs t \<and> set x = {(l, v). Write t l v \<in> ops} \<and> distinct x))" 
 in exI, rule no_atomic, auto)
apply (cut_tac P="\<lambda>up. bufs' t = up @ bufs t \<and> set up = {(l, v). Write t l v \<in> ops} \<and> 
 distinct up" in someI_ex, force, clarsimp)
apply (rule_tac x="SOME x. bufs' t = x @ bufs t \<and> set x = {(l, v). Write t l v \<in> ops} \<and> distinct x"
 in exI, clarsimp)
apply (rule_tac s="add_red ((SOME x. bufs' t = x @ bufs t \<and> set x = {(l, v). Write t l v \<in> ops} \<and> distinct x) @ bufs t)
        (\<lambda>n. if n < length (SOME x. bufs' t = x @ bufs t \<and> set x = {(l, v). Write t l v \<in> ops} \<and> distinct x) then []
             else f (n - length (SOME x. bufs' t = x @ bufs t \<and> set x = {(l, v). Write t l v \<in> ops} \<and> distinct x)))" 
 in trans, simp, simp (no_asm))
apply (drule_tac bufs="bufs(t := add_red (bufs t) f)" and t=t and a="add_red buf f'" in process_buffer,
 simp, clarsimp)
apply (subgoal_tac "dom (map_of (map (Pair l) (f' (length buf)))) = {l} \<or> f' (length buf) = []", 
 auto simp add: dom_map_of_conv_image_fst intro!: set_eqI)
apply (metis (full_types) append_Nil fst_conv imageI in_set_conv_decomp list.exhaust)
apply (drule_tac bufs="bufs(t := add_red (bufs t) f)" in update, simp, force, 
 force simp add: fun_upd_twist)
apply force
done

lemma can_read_red: "b' t = add_red (b t) f \<Longrightarrow> can_read (mem, b') t = can_read (mem, b) t"
by (clarsimp intro!: ext simp add: can_read_def split: option.splits)

lemma can_read_red_loc: "\<lbrakk>b' t = (l', v) # add_red (b t) f; l' \<noteq> l\<rbrakk> \<Longrightarrow> 
 can_read (mem, b') t l = can_read (mem, b) t l"
by (clarsimp intro!: ext simp add: can_read_def split: option.splits)

end

(* Sequential consistency memory model *)
locale SC = fixes undef::'val begin

abbreviation "free_set mem \<equiv> UNIV - dom mem"
abbreviation "can_read mem t l \<equiv> {v. mem l = Some v}"
inductive update_mem where 
no_atomic [intro]: "\<lbrakk>\<And>t l v v'. ARW t l v v' \<notin> ops; \<And>l. (\<forall>t v. Write t l v \<notin> ops) \<Longrightarrow> writes l = None; 
 \<And>t l v. Write t l v \<in> ops \<Longrightarrow> \<exists>t v. Write t l v \<in> ops \<and> writes l = Some v; finite ops\<rbrakk> \<Longrightarrow> 
 update_mem mem ops (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None) ++ writes)" |
atomic [intro!]: "update_mem mem {ARW t l v v'} (mem(l \<mapsto> v'))"
abbreviation "start_mem \<equiv> empty"

lemma update_threads: "\<lbrakk>update_mem mem ops mem'; \<forall>a'\<in>ops'. \<exists>a\<in>ops. \<exists>t. a' = set_thread (t::'t) 
  (a::('t, 'l, 'val) access)\<rbrakk> \<Longrightarrow> update_mem mem ops' mem'"
apply (drule_tac P="\<lambda>mem ops mem'. \<forall>ops'. (\<forall>a'\<in>ops'. \<exists>a\<in>ops. \<exists>t. a' = set_thread t a) \<longrightarrow>
  update_mem mem ops' mem'" in update_mem.induct, auto)
apply (subgoal_tac "{l. \<exists>t. Free t l \<in> opsa} = {l. \<exists>t. Free t l \<in> ops'a} \<and> (\<lambda>l. if \<exists>t. Alloc t l \<in> 
  opsa then Some undef else None) = (\<lambda>l. if \<exists>t. Alloc t l \<in> ops'a then Some undef else None)", simp)
apply (rule no_atomic, clarsimp)
apply (thin_tac "\<forall>a'\<in>ops'. \<exists>a\<in>ops. \<exists>t. a' = set_thread t a")
apply (erule_tac x="ARW t l v v'" in ballE, simp_all, clarsimp)
apply (case_tac a, simp_all)
apply (subgoal_tac "\<forall>t v. Write t l v \<notin> opsa", simp, clarsimp)
oops

lemma update_threads: "update_mem mem ops mem' \<Longrightarrow> update_mem mem (set_thread t ` ops) mem'"
apply (drule_tac P="\<lambda>mem ops mem'. update_mem mem (set_thread t ` ops) mem'" in update_mem.induct, auto)
apply (subgoal_tac "{l. \<exists>t. Free t l \<in> ops} = {l. \<exists>ta. Free ta l \<in> set_thread t ` ops} \<and> (\<lambda>l. if 
  \<exists>t. Alloc t l \<in> ops then Some undef else None) = (\<lambda>l. if \<exists>ta. Alloc ta l \<in> set_thread t ` ops 
  then Some undef else None)", simp)
apply (rule no_atomic, clarsimp)
apply (case_tac x, simp_all)
apply (subgoal_tac "\<forall>t v. Write t l v \<notin> ops", simp, clarsimp)
apply (erule_tac x=t in allE, erule_tac x=v in allE, force simp add: image_def)
apply (subgoal_tac "\<exists>t v. Write t l v \<in> ops \<and> writes l = Some v", clarsimp simp add: image_def)
apply (rule_tac x=t in exI, rule_tac x="Write tb l va" in bexI, simp+)
apply (clarsimp simp add: image_def)
apply (case_tac x, simp_all)
apply (auto simp add: image_def)
apply (rule_tac x=t in exI, rule bexI, simp_all)
apply (case_tac xa, simp_all, metis)
apply (rule ext, auto)
apply (rule_tac x=t in exI, rule bexI, simp_all)
apply (case_tac x, simp_all)
done

lemma stays_not_free: "\<lbrakk>update_mem mem ops mem'; l \<notin> free_set mem; \<forall>t. Free t l \<notin> ops\<rbrakk> \<Longrightarrow>
 l \<notin> free_set mem'"
by (induct rule: update_mem.induct, auto split: if_splits)

lemma alloc_not_free: "\<lbrakk>update_mem mem ops mem'; Alloc t l \<in> ops; Free t l \<notin> ops\<rbrakk> \<Longrightarrow> 
 l \<notin> free_set mem'"
by (induct rule: update_mem.induct, auto split: if_splits)

end

sublocale SC \<subseteq> memory_model free_set can_read update_mem start_mem
by (unfold_locales, metis alloc_not_free, metis stays_not_free)

context SC begin

lemma update_none [intro!, simp]: "update_mem C {} C"
by (cut_tac no_atomic, auto simp add: restrict_map_def)

lemma update_none_only [simp, dest!]: "update_mem mem {} mem' \<Longrightarrow> mem' = mem"
by (erule update_mem.cases, auto simp add: restrict_map_def map_add_def)

lemma update_one_write [intro!, simp]: "mem' = mem(l \<mapsto> v) \<Longrightarrow>
 update_mem mem {Write t l v} mem'"
by (cut_tac ops="{Write t l v}" and writes="[l \<mapsto> v]" in no_atomic, auto simp add: restrict_map_def)

lemma update_one_writeD [dest!, simp]: "update_mem mem {Write t l v} mem' \<Longrightarrow> mem' = mem(l \<mapsto> v)"
by (erule update_mem.cases, auto intro!: ext simp add: map_add_def split: option.splits)

lemma update_one_read [intro, simp]: "update_mem mem {Read t l v} mem"
by (cut_tac ops="{Read t l v}" in no_atomic, auto simp add: restrict_map_def)

lemma update_one_readD [dest!, simp]: "update_mem mem {Read t l v} mem' \<Longrightarrow> mem' = mem"
by (erule update_mem.cases, auto intro!: ext simp add: restrict_map_def map_add_def)

lemma update_one_alloc [intro!, simp]: "mem' = mem(l \<mapsto> undef) \<Longrightarrow>
 update_mem mem {Alloc t l} mem'"
apply (cut_tac ops="{Alloc t l}" and mem=mem in no_atomic, auto simp add: restrict_map_def)
apply (subgoal_tac "mem ++ (\<lambda>la. if la = l then Some undef else None) = mem(l \<mapsto> undef)", simp,
 auto intro!: ext simp add: map_add_def)
done

lemma update_one_allocD [dest!]: "update_mem mem {Alloc t l} mem' \<Longrightarrow> mem' = mem(l \<mapsto> undef)"
by (erule update_mem.cases, auto simp add: restrict_map_def map_add_def)

lemma update_frees [intro!, simp]: "\<lbrakk>mem' = mem |` (UNIV - S); finite S\<rbrakk> \<Longrightarrow> 
 update_mem mem (Free t ` S) mem'"
apply (cut_tac ops="Free t ` S" and mem=mem in no_atomic, auto)
apply (rule subst, rule_tac f="update_mem mem (Free t ` S)" in arg_cong, simp_all)
apply (auto intro!: ext simp add: map_add_def restrict_map_def, force)
done

lemma update_freesD [dest!, simp]: "update_mem mem (Free t ` S) mem' \<Longrightarrow>
 mem' = mem |` (UNIV - S)"
apply (erule update_mem.cases, auto intro!: ext simp add: map_add_def restrict_map_def 
 split: option.splits)
apply (metis image_eqI)
apply (metis access.distinct(13) image_iff option.distinct(1))
apply (metis image_eqI)
by (metis access.distinct(13) image_iff option.distinct(1))

lemma update_ARW [intro!]: "mem' = mem(l \<mapsto> v') \<Longrightarrow> update_mem mem {ARW t l v v'} mem'"
by clarsimp

lemma update_ARWD [dest!]: "update_mem mem {ARW t l v v'} mem' \<Longrightarrow> mem' = mem(l \<mapsto> v')"
by (erule update_mem.cases, auto)

lemma update_past: "\<lbrakk>update_mem mem ops mem'; \<And>t v. Write t l v \<notin> ops; 
 \<And>t v v'. ARW t l v v' \<notin> ops; \<And>t. Free t l \<notin> ops; \<And>t. Alloc t l \<notin> ops\<rbrakk> \<Longrightarrow>
 update_mem (mem(l := v)) ops (mem'(l := v))"
apply (induct rule: update_mem.induct, auto)
apply (cut_tac ops=ops and mem="mem(l := v)" and writes=writes in no_atomic, auto)
apply (rule_tac f1="update_mem (mem(l := v))" in arg_cong2 [THEN subst], 
 auto intro!: ext simp add: map_add_def restrict_map_def split: option.splits)
by (metis atomic fun_upd_twist)

end

locale undef = fixes undef::'val
sublocale undef \<subseteq> TSO: TSO .
sublocale undef \<subseteq> SC: SC .

context undef begin

(* SC can be modeled by TSO. *)
(*

lemma process_all_buffers [rule_format]: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); 
 \<forall>t. bufs' t = ma t @ mb t; finite {t. mb t \<noteq> []}\<rbrakk> \<Longrightarrow>
 \<exists>m'. update_mem (mem, bufs) ops (mem' ++ m', (\<lambda>t. ma t)) \<and>
 (\<forall>l v. ((m' l = Some v) \<longrightarrow> (\<exists>t. map_of (mb t) l = Some v)) \<and>
 (m' l = None \<longrightarrow> (\<forall>t. map_of (mb t) l = None)))"
apply (drule_tac P="\<lambda>S. \<forall>mem' bufs' ma mb. (update_mem (mem, bufs) ops (mem', bufs') \<and>
 (\<forall>t. bufs' t = ma t @ mb t)) \<and> S = {t. mb t \<noteq> []} \<longrightarrow> 
 (\<exists>m'. update_mem (mem, bufs) ops (mem' ++ m', (\<lambda>t. ma t)) \<and>
 (\<forall>l v. ((m' l = Some v) \<longrightarrow> (\<exists>t. map_of (mb t) l = Some v)) \<and>
 (m' l = None \<longrightarrow> (\<forall>t. map_of (mb t) l = None))))" in finite_induct, auto)
apply (rule_tac x=empty in exI, simp)
apply (subgoal_tac "bufs'a = maa", simp)
apply (auto intro!: ext split: option.split)
apply (cut_tac a=x and B=F in insertI1, clarsimp)
apply (thin_tac "\<forall>t. bufs' t = ma t @ mb t")
apply (drule_tac bufs'=bufs'a and t=x and a="ma x" in process_buffer, auto)
apply (erule_tac x="mem'a ++ map_of (mb x)" in allE, erule_tac x="bufs'a(x := ma x)" in allE, 
 erule_tac x=ma in allE, erule_tac x="mb(x := [])" in allE, clarsimp, erule impE, force, clarsimp)
apply (rule_tac x="map_of (mb x) ++ m'" in exI, auto split: if_splits, metis, metis)
apply (erule_tac x=mem' in allE, erule_tac x=bufs' in allE, simp)
done

lemma SC_lt_update [simp, intro]: "update_mem_SC mem ops mem' \<Longrightarrow> 
 update_mem (mem, \<lambda>t. []) ops (mem', \<lambda>t. [])"
apply (erule update_mem_SC.cases, auto split: if_splits)
apply (cut_tac ops=ops and mem=mem and bufs="\<lambda>t. []" and
 bufs'="\<lambda>t. list_of_set {(l, v) | l v. Write t l v \<in> ops \<and> writes l = Some v} @ 
 list_of_set {(l, v) | l v. Write t l v \<in> ops \<and> writes l \<noteq> Some v}" in no_atomic, simp_all)
apply (subgoal_tac "finite {(l, v). Write t l v \<in> ops}", auto)
apply (rule finite_vimageI, auto simp add: inj_on_def)
apply (drule_tac ma="\<lambda>t. list_of_set {(l, v) | l v. Write t l v \<in> ops \<and> writes l = Some v}" and 
 mb="\<lambda>t. list_of_set {(l, v) | l v. Write t l v \<in> ops \<and> writes l \<noteq> Some v}" in process_all_buffers)
apply (simp split: if_splits)
apply clarsimp
apply (rule_tac B="{t. \<exists>a \<in> ops. get_thread a = t}" in finite_subset, clarsimp)
apply (clarsimp simp add: card_gt_0_iff, rule_tac x="Write x a b" in bexI, simp+)
apply clarsimp
apply (drule_tac ma="\<lambda>t. []" and 
 mb="\<lambda>t. list_of_set {(l, v) | l v. Write t l v \<in> ops \<and> writes l = Some v}" in process_all_buffers)
apply (simp split: if_splits)
apply clarsimp
apply (rule_tac B="{t. \<exists>a \<in> ops. get_thread a = t}" in finite_subset, clarsimp)
apply (clarsimp simp add: card_gt_0_iff, rule_tac x="Write x a b" in bexI, simp+)
apply clarsimp
apply (rule_tac x1="(mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None) ++ m' ++ m'a, \<lambda>t. case case if t \<in> dom threads
                       then Some (list_of_set {(l, v) |l v. Write t l v \<in> ops \<and> writes l = Some v} @
                                  list_of_set {(l, v) |l v. Write t l v \<in> ops \<and> writes l \<noteq> Some v})
                       else None of
                  None \<Rightarrow> None | Some x \<Rightarrow> Some (list_of_set {(l, v) |l v. Write t l v \<in> ops \<and> writes l = Some v}) of
             None \<Rightarrow> None | Some x \<Rightarrow> Some [])" in cong [THEN subst], simp, auto)
apply (subgoal_tac "m' ++ m'a = writes")
apply (metis map_add_assoc)
apply (rule ext, (erule_tac x=x in allE)+, clarsimp simp add: map_add_def split: option.split)
apply (case_tac "writes x", simp_all)
apply (subgoal_tac "\<forall>t v. Write t x v \<notin> ops", rule ccontr, clarsimp, erule disjE, 
 clarsimp split: if_splits)
apply (drule map_of_is_SomeD)
apply (subgoal_tac "finite {(l, v). Write t l v \<in> ops}", simp+)
apply (rule finite_vimageI, simp, simp add: inj_on_def)
apply (clarsimp split: if_splits)
apply (drule map_of_is_SomeD)
apply (subgoal_tac "finite {(l, v). Write t l v \<in> ops}", simp+)
apply (rule finite_vimageI, simp, simp add: inj_on_def)
apply (metis not_Some_eq)
apply (subgoal_tac "\<exists>t. Write t x a \<in> ops", clarsimp)
apply (rule conjI, clarsimp)
apply (erule_tac x=t in allE)
apply (clarsimp simp add: map_of_eq_None_iff)
apply (subgoal_tac "finite {(l, v). Write t l v \<in> ops}", simp+)
apply (erule notE, rule_tac x="(x, a)" in image_eqI, simp+)
apply (rule finite_vimageI, simp, simp add: inj_on_def)
apply clarsimp
apply (drule map_of_is_SomeD)
apply (subgoal_tac "finite {(l, v). Write ta l v \<in> ops}", simp+)
apply (rule finite_vimageI, simp, simp add: inj_on_def)
by (metis (hide_lams, full_types) not_Some_eq option.inject)

lemma make_bufs_can_read [simp]: "can_read (mem, \<lambda>t. []) t = can_read_SC mem t"
by (rule ext, simp add: can_read_def)
(* Because can_read and update_mem are the only interfaces to the memory provided by memory_model,
   this implies that SC refines TSO for any language.  Is there a way to make this explicit? *)
*)
end

locale PSO = fixes undef::'val begin

(* PSO memory model *)
abbreviation "free_set mem \<equiv> UNIV - dom (fst mem)"
definition "can_read mem t l \<equiv> case snd mem t l of v # buf \<Rightarrow> {v}
 | [] \<Rightarrow> {v. fst mem l = Some v}"
inductive update_mem where 
no_atomic [intro]: "\<lbrakk>\<And>t l v v'. ARW t l v v' \<notin> ops; \<And>t l. \<exists>up. bufs' t l = up @ bufs t l \<and> 
 set up = {v. Write t l v \<in> ops} \<and> distinct up\<rbrakk> \<Longrightarrow> 
 update_mem (mem, bufs) ops (mem |` (UNIV - {l. \<exists>t. Free t l \<in> ops}) ++ 
 (\<lambda>l. if \<exists>t. Alloc t l \<in> ops then Some undef else None), bufs')" |
update [intro]: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); bufs' t l = buf @ [v]\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs) ops (mem'(l \<mapsto> v), bufs'(t := (bufs' t)(l := buf)))" |
atomic [intro!]: "bufs t l = [] \<Longrightarrow>
 update_mem (mem, bufs) {ARW t l v v'} (mem(l \<mapsto> v'), bufs)"
abbreviation "start_mem \<equiv> (empty, \<lambda>t l. [])"

lemma alloc_not_free: "\<lbrakk>update_mem mem ops mem'; Alloc t l \<in> ops; \<forall>t. Free t l \<notin> ops\<rbrakk> \<Longrightarrow> 
 l \<notin> free_set mem'"
by (induct rule: update_mem.induct, auto split: if_splits)

lemma stays_not_free: "\<lbrakk>update_mem mem ops mem'; l \<notin> free_set mem; \<forall>t. Free t l \<notin> ops\<rbrakk> \<Longrightarrow>
 l \<notin> free_set mem'"
by (induct rule: update_mem.induct, auto split: if_splits)

end

sublocale PSO \<subseteq> memory_model free_set can_read update_mem start_mem
by (unfold_locales, metis alloc_not_free, metis stays_not_free)

context PSO begin

lemma update_none [intro!, simp]: "update_mem C {} C"
by (cases C, cut_tac ops="{}" and mem=a and bufs=b in no_atomic, auto simp add: restrict_map_def)

lemma process_buffer: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); bufs' t l = a @ v # b\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs) ops (mem'(l \<mapsto> v), bufs'(t := (bufs' t)(l := a)))"
apply (induct b arbitrary: mem' bufs' v rule: rev_induct, auto simp add: map_upd_triv)
apply (drule_tac t=t and l=l in update, simp, force)
done

lemma update_later: "\<lbrakk>update_mem (mem, bufs) {} (mem', bufs')\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs) {Write t l v} (mem', bufs'(t := (bufs' t)(l := v # bufs' t l)))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). ops = {} \<longrightarrow> 
 update_mem (mem, bufs) {Write t l v} (mem', bufs'(t := (bufs' t)(l := v # bufs' t l)))" 
 in update_mem.induct, auto)
apply (cut_tac ops="{Write t l v}" in no_atomic, auto)
apply (drule_tac ops="{Write t l v}" in update, auto)
apply (drule_tac ops="{Write t l v}" and t=ta in update, auto simp add: fun_upd_twist)
apply (drule_tac ops="{Write t l v}" and l=la in update, auto simp add: fun_upd_twist)
apply (drule_tac ops="{Write t l v}" and t=ta in update, auto simp add: fun_upd_twist)
done

lemma update_later2: "\<lbrakk>update_mem (mem, bufs) {} (mem', bufs'(t := (bufs' t)(l := buf))); 
 bufs' t l = v # buf\<rbrakk> \<Longrightarrow> update_mem (mem, bufs) {Write t l v} (mem', bufs')"
by (smt fun_upd_idem_iff fun_upd_upd list.inject update_later)

lemma update_past2: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); 
 \<And>v. Write t l v \<notin> ops; \<And>l v v'. ARW t l v v' \<notin> ops\<rbrakk> \<Longrightarrow> 
 update_mem (mem, bufs(t := (bufs t)(l := b @ bufs t l))) ops 
                (mem', bufs'(t := (bufs' t)(l := b @ bufs' t l)))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). (\<forall>v. Write t l v \<notin> ops) \<and> 
 (\<forall>l v v'. ARW t l v v' \<notin> ops) \<longrightarrow> update_mem (mem, bufs(t := (bufs t)(l := b @ bufs t l))) ops 
                (mem', bufs'(t := (bufs' t)(l := b @ bufs' t l)))" in update_mem.induct, auto)
apply (rule no_atomic, auto)
apply (subgoal_tac "\<exists>up. bufs' t l = up @ bufs t l \<and> set up = {v. Write t l v \<in> opsa} \<and> 
 distinct up", simp)
apply (metis (full_types))
apply (drule_tac bufs="bufs(t := (bufs t)(l := b @ bufs t l))" in update, auto)
apply (drule_tac bufs="bufs(t := (bufs t)(l := b @ bufs t l))" and t=ta in update, 
 auto simp add: fun_upd_twist)
apply (drule_tac bufs="bufs(t := (bufs t)(l := b @ bufs t l))" in update, 
 auto simp add: fun_upd_twist)
apply (drule_tac bufs="bufs(t := (bufs t)(l := b @ bufs t l))" and t=ta in update, 
 auto simp add: fun_upd_twist)
done

lemma update_write: "\<lbrakk>update_mem (mem, bufs) {Write t l v} (mem', bufs')\<rbrakk> \<Longrightarrow>
 update_mem (mem, bufs(t := (bufs t)(l := v # bufs t l))) {} (mem', bufs')"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). ops = {Write t l v} \<longrightarrow>
 update_mem (mem, bufs(t := (bufs t)(l := v # bufs t l))) {} (mem', bufs')" 
 in update_mem.induct, auto)
apply (cut_tac ops="{}" and bufs="bufs(t := (bufs t)(l := v # bufs t l))" and
 bufs'=bufs' in no_atomic, simp_all)
apply (subgoal_tac "\<exists>up. bufs' ta la = up @ bufs ta la \<and> set up = {va. va = v \<and> ta = t \<and> la = l} \<and> 
 distinct up", clarify, auto)
apply (case_tac up, auto, case_tac list, auto)
done

lemma update_trans_rev: "\<lbrakk>update_mem (mem', bufs') {} (mem'', bufs'');
 update_mem (mem, bufs) ops (mem', bufs')\<rbrakk> \<Longrightarrow> update_mem (mem, bufs) ops (mem'', bufs'')"
apply (drule_tac P="\<lambda>(mem', bufs') ops' (mem'', bufs''). ops' = {} \<and> update_mem (mem, bufs) ops (mem', bufs') \<longrightarrow>
 update_mem (mem, bufs) ops (mem'', bufs'')" in update_mem.induct, auto simp add: restrict_map_def)
apply (subgoal_tac "bufs'a = bufsa", auto)
done

end
*)
(* In PSO, redundant elements are added to the buffers for individual locations. *)
definition "add_red2 l f = concat (map (\<lambda>(v, n). v # f n) (zip l [0..<length l]))"

lemma add_red2_nil [simp]: "add_red2 [] f = []"
by (simp add: add_red2_def)

lemma upt_0 [simp]: "j > i \<Longrightarrow> [i..<j] ! 0 = i"
by (induct i, auto)

lemma add_red2_nil2 [simp]: "(add_red2 l f = []) = (l = [])"
apply (auto simp add: add_red2_def)
apply (case_tac l, auto)
apply (erule_tac x="(a, 0)" in ballE, auto simp add: set_conv_nth)
apply (erule_tac x=0 in allE, auto)
by (metis gr_implies_not0 le0 upt_0 upt_Suc zero_less_Suc)

lemma map_upt_zip_Suc2 [simp]: "l' = map (\<lambda>(x, n). (x, Suc n)) l \<Longrightarrow> map (\<lambda>(v, n). v # f n) l' =
 map (\<lambda>(v, n). v # f (Suc n)) l"
by auto

lemma add_red2_cons [simp]: "add_red2 (x # l) f = x # f 0 @ add_red2 l (\<lambda>n. f (Suc n))"
apply (auto simp add: add_red2_def)
apply (case_tac "map (\<lambda>(v, n). v # f n) (zip (x # l) ([0..<length l] @ [length l]))", auto)
apply (case_tac "[0..<length l] @ [length l]", auto)
apply (case_tac "[0..<length l] @ [length l]", auto)
apply (case_tac "[0..<length l] @ [length l]", auto)
apply (cut_tac i=0 and j="Suc (length l)" and x=b and xs=list in upt_eq_Cons_conv, auto)
apply (rule_tac f=concat in arg_cong)
apply (rule map_upt_zip_Suc2)
by (metis upt_Suc_append zip_Suc)

lemma add_red2_app [simp]: "add_red2 (l @ l') f = add_red2 l f @ add_red2 l' (\<lambda>n. f (n + length l))"
by (induct l arbitrary: f, auto)

lemma add_red2_id [simp]: "(\<And>n. n < length l \<Longrightarrow> f n = []) \<Longrightarrow> add_red2 l f = l"
by (induct l arbitrary: f, auto)

context PSO begin

lemma update_red2: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs');
 \<And>t l. red t l = add_red2 (bufs t l) (f t l)\<rbrakk> \<Longrightarrow>
 \<exists>red' f'. update_mem (mem, red) ops (mem', red') \<and> 
 (\<forall>t l. red' t l = add_red2 (bufs' t l) (f' t l))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). (\<forall>t l. red t l = add_red2 (bufs t l) (f t l)) \<longrightarrow> 
 (\<exists>red' f'. update_mem (mem, red) ops (mem', red') \<and> (\<forall>t l. red' t l = add_red2 (bufs' t l) (f' t l)))" 
 in update_mem.induct, auto)
apply (rule_tac x="\<lambda>t l. (SOME up. bufs' t l = up @ (bufsa t l) \<and> set up = {v. Write t l v \<in> ops} \<and> 
 distinct up) @ red t l" in exI, auto)
apply (rule no_atomic, simp_all)
apply (cut_tac P="\<lambda>up. bufs' t l = up @ bufsa t l \<and> set up = {v. Write t l v \<in> ops} \<and> 
 distinct up" in someI_ex, simp+)
apply (rule_tac x="\<lambda>t l n. if n < length (SOME up. bufs' t l = up @ bufsa t l \<and> set up = 
 {v. Write t l v \<in> ops} \<and> distinct up) then [] else f t l (n - length (SOME up. bufs' t l = 
 up @ bufsa t l \<and> set up = {v. Write t l v \<in> ops} \<and> distinct up))" in exI, clarsimp)
apply (subgoal_tac "\<exists>up. bufs' t l = up @ bufsa t l \<and> set up = {v. Write t l v \<in> ops} \<and> distinct up", 
 clarify, clarsimp)
apply (cut_tac P="\<lambda>upa. up = upa \<and> set upa = {v. Write t l v \<in> ops} \<and> distinct upa" in someI, 
 force, clarsimp)
apply metis
apply (drule_tac bufs=red and t=t and l=l and a="add_red2 buf (f' t l)" in process_buffer, force)
apply (rule_tac x="red'(t := (red' t)(l := add_red2 buf (f' t l)))" in exI, clarsimp, metis)
apply (rule_tac x=red in exI, auto)
done

lemma update_red2_one_buf: "\<lbrakk>update_mem (mem, bufs) ops (mem', bufs'); 
 \<And>t'. t' \<noteq> t \<Longrightarrow> red t' = bufs t'; \<And>l. red t l = add_red2 (bufs t l) (f l)\<rbrakk> \<Longrightarrow>
 \<exists>red' f'. update_mem (mem, red) ops (mem', red') \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> red' t' = bufs' t') \<and>
 (\<forall>l. red' t l = add_red2 (bufs' t l) (f' l))"
apply (drule_tac P="\<lambda>(mem, bufs) ops (mem', bufs'). ((\<forall>t'. t' \<noteq> t \<longrightarrow> red t' = bufs t') \<and>
 (\<forall>l. red t l = add_red2 (bufs t l) (f l))) \<longrightarrow> (\<exists>red' f'. update_mem (mem, red) ops (mem', red') \<and> 
 (\<forall>t'. t' \<noteq> t \<longrightarrow> red' t' = bufs' t') \<and> (\<forall>l. red' t l = add_red2 (bufs' t l) (f' l)))" 
 in update_mem.induct, simp_all, clarsimp)
apply (rule_tac x="bufs'(t := \<lambda>l. (SOME up. bufs' t l = up @ (bufsa t l) \<and> set up = {v. Write t l v \<in> ops} \<and> 
 distinct up) @ red t l)" in exI, clarsimp)
apply (rule conjI, rule no_atomic, simp_all)
apply (cut_tac P="\<lambda>up. bufs' t l = up @ bufsa t l \<and> set up = {v. Write t l v \<in> ops} \<and> 
 distinct up" in someI_ex, simp+)
apply (rule_tac x="\<lambda>l n. if n < length (SOME up. bufs' t l = up @ bufsa t l \<and> set up = 
 {v. Write t l v \<in> ops} \<and> distinct up) then [] else f l (n - length (SOME up. bufs' t l = 
 up @ bufsa t l \<and> set up = {v. Write t l v \<in> ops} \<and> distinct up))" in exI, clarsimp)
apply (subgoal_tac "\<exists>up. bufs' t l = up @ bufsa t l \<and> set up = {v. Write t l v \<in> ops} \<and> distinct up", 
 clarify, clarsimp)
apply (cut_tac P="\<lambda>upa. up = upa \<and> set upa = {v. Write t l v \<in> ops} \<and> distinct upa" in someI, 
 force, clarsimp)
apply metis
apply auto
apply (drule_tac bufs=red and t=t and l=l in process_buffer, force)
apply (rule_tac x="red'(t := (red' t)(l := add_red2 buf (f' l)))" in exI, clarsimp, metis)
apply (drule_tac bufs=red and t=ta and l=l in process_buffer, force)
apply (rule_tac x="red'(ta := (red' ta)(l := buf))" in exI, clarsimp, metis)
apply (rule_tac x=red in exI, auto)
apply (case_tac "ta = t", auto)
done

lemma can_read_red [simp]: "b' t l = add_red2 (b t l) f \<Longrightarrow> 
 can_read (mem, b') t l = can_read (mem, b) t l"
by (clarsimp intro!: ext simp add: can_read_def split: list.splits)

lemma can_read_loc: "b' t l = b t l \<Longrightarrow> 
 can_read (mem, b') t l = can_read (mem, b) t l"
by (clarsimp intro!: ext simp add: can_read_def split: list.splits)

lemma two_part_buf [simp]: "bufs t l = buf \<Longrightarrow> bufs(t := (bufs t)(l := buf)) = bufs"
by (clarsimp intro!: ext)

end
*)
end
