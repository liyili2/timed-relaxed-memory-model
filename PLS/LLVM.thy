(* LLVM.thy *)
(* William Mansky *)
(* MiniLLVM for VeriF-OPT. *)

theory LLVM
imports trans_flowgraph trans_semantics
begin

(* Maybe I shouldn't have this
type_synonym 'a pat = "('a, string)literal"
*)

(* Syntax *)
datatype LLVM_type = Int_ty | (* Float_ty | Void_ty | Label_ty | Array_ty nat LLVM_type ("[_ \<times> _]") |*)
(* Structure? | *) Pointer_ty LLVM_type ("_*")  (* Ignoring size for now. *)

datatype 'mvar LLVM_type_pat = PInt_ty | Tymvar 'mvar | PPointer_ty "'mvar LLVM_type_pat"

primrec LLVM_type_lit_fv where
   "LLVM_type_lit_fv PInt_ty = {}"
 | "LLVM_type_lit_fv (Tymvar x) = {x}"
 | "LLVM_type_lit_fv (PPointer_ty ty) = LLVM_type_lit_fv ty"

lemma finite_LLVM_type_lit_fv [simp]: "finite (LLVM_type_lit_fv ty)"
by (induct_tac ty, auto)

datatype ('loc,'int) LLVM_const = CInt 'int | (* Float? | *) CNull (* | CArray "(LLVM_type \<times> LLVM_const) list" *) | 
 CPointer 'loc | CUndef
(* Poison values? *)

type_synonym concrete_LLVM_const = "(int, int)LLVM_const"
type_synonym 'mvar gen_LLVM_const = "((int,'mvar)literal,(int,'mvar)literal) LLVM_const"

primrec LLVM_const_lit_fv where
   "LLVM_const_lit_fv (CInt ip) = base_lit_fv ip"
 | "LLVM_const_lit_fv CNull = {}"
 | "LLVM_const_lit_fv (CPointer lp) = base_lit_fv lp"
 | "LLVM_const_lit_fv CUndef = {}"

lemma finite_LLVM_const_lit_fv [simp]: 
  "finite (LLVM_const_lit_fv c)"
by (case_tac c, auto)

datatype ('var, 'cvar, 'gvar) LLVM_expr =
    Local 'var ("%_")
  | Const "'cvar"
  | Global 'gvar (*string*) (*("@_")*) (* | Constant expressions? *)

type_synonym concrete_LLVM_expr = "(string, concrete_LLVM_const, string) LLVM_expr"
type_synonym 'mvar gen_LLVM_expr = "('mvar, ('mvar gen_LLVM_const, 'mvar)literal, 'mvar) LLVM_expr"
type_synonym 'mvar LLVM_expr_pat = "('mvar gen_LLVM_expr,'mvar) expr_pattern"


(* If we are calculating free variables, then we are dealing with patterns,
   ie things with "literals" --ELG *)

primrec expr_fv :: "'mvar gen_LLVM_expr \<Rightarrow> 'mvar set" where
"expr_fv (Local x) = {x}" |
"expr_fv (Const c) = lit_fv LLVM_const_lit_fv c" |
"expr_fv (Global g) = {g}"

lemma finite_expr_fv [simp]:
fixes e shows "finite (expr_fv e)"
by (case_tac e, auto)

corollary finite_expr_pattern_fv:
fixes ep shows "finite (expr_pattern_fv expr_fv ep)"
by simp

primrec expr_lfv :: "concrete_LLVM_expr \<Rightarrow> string set" where
"expr_lfv (Local x) = {x}" |
"expr_lfv (Const c) = {}" |
"expr_lfv (Global g) = {}"

datatype LLVM_op = add | sub | mul
datatype LLVM_cmp = eq | ne | sgt | sge | slt | sle

abbreviation eplist_fv :: "'mvar LLVM_expr_pat list \<Rightarrow> 'mvar set" where
"eplist_fv \<equiv> \<lambda> epl. foldr
 (\<lambda> ep vs. (expr_pattern_fv expr_fv ep) \<union> vs) epl {}"

abbreviation eplist_lfv :: "concrete_LLVM_expr list \<Rightarrow> string set" where
"eplist_lfv \<equiv> \<lambda> epl. foldr (\<lambda> ep vs. (expr_lfv ep) \<union> vs) epl {}"

lemma finite_eplist_fv [simp]:
fixes epl shows "finite (eplist_fv epl)"
by (induct "epl", auto)

(*
type_synonym 'thread gen_node = "(('thread, string) literal) node_const"

term "(x::('thread gen_node, string) literal)"
*)

type_synonym 'node concrete_philist = "('node \<times> concrete_LLVM_expr) list"
type_synonym 'mvar gen_philist = "(('mvar node_const,'mvar)literal  \<times> ('mvar LLVM_expr_pat))list"

abbreviation philist_fv :: "'mvar gen_philist \<Rightarrow> 'mvar set" where
"philist_fv \<equiv> \<lambda> es. foldr (\<lambda>(n, e) r. lit_fv node_fv n \<union> expr_pattern_fv expr_fv e \<union> r) es {}"

lemma finite_philist_fv [simp]:
fixes phi_list  shows "finite (philist_fv phi_list)"
by (induct "phi_list", auto)

term "expr_lfv"
abbreviation philist_lfv :: "'node concrete_philist \<Rightarrow> string set" where
"philist_lfv \<equiv> \<lambda> es. foldr (\<lambda>(n, e) r. expr_lfv e \<union> r) es {}"

(* TODO: better concrete syntax *)
datatype ('var, 'type, 'expr, 'opr, 'cmp, 'phi_list, 'args) LLVM_instr =
   Assign 'var 'opr 'type 'expr 'expr ("_ = _ _ _, _" 160)
 | Ret 'type 'expr
 | Br_i1 'expr (* conditional branch *)
 | Br_label (* unconditional *)
(* Note that, since control flow is implicit in the function body, label targets are unnecessary. 
   Well, sort of.  If we were linking to outside things, using label names would let us refer outside
   the context.  *)
(* Switch | Indirectbr | Invoke | Resume | *)  
 | Alloca 'var 'type (* the memory is freed when the allocating function returns. *)
 | Load 'var 'type 'expr
 | Store 'type 'expr 'type 'expr (* Fence |*)
 | Cmpxchg 'var 'type 'expr 'type 'expr 'type 'expr (* ordering constraint *)
 | ICmp 'var 'cmp 'type 'expr 'expr ("_ = icmp _ _ _, _" 160) (* | Atomicrmw *)
 | Phi 'var 'type 'phi_list (*"('node \<times> 'expr) list"*) ("_ = phi _ _" 160)  (* Select | *) 
 | Call 'var 'type "'args" ("_ = call _ _" 160)  (* list patterns? *)
(* This might be controversial: eliminate function names entirely, indicate call target by call edge.
   This is inadequate for 1) calls to outside functions and 2) function pointers.  *) 
 | IsPointer 'expr

type_synonym 'node concrete_LLVM_instr =
"(string, LLVM_type, concrete_LLVM_expr, LLVM_op, LLVM_cmp, 'node concrete_philist,
  concrete_LLVM_expr list) LLVM_instr"

type_synonym 'mvar gen_LLVM_instr =
"('mvar, 'mvar LLVM_type_pat,'mvar  LLVM_expr_pat, (LLVM_op, 'mvar)literal, (LLVM_cmp,'mvar)literal,
 ('mvar gen_philist,'mvar)literal, ('mvar LLVM_expr_pat list, 'mvar)literal) LLVM_instr"

type_synonym 'mvar pattern = "('mvar gen_LLVM_instr, 'mvar) literal"

primrec instr_pattern_fv ::"'mvar gen_LLVM_instr \<Rightarrow> 'mvar set" where
"instr_pattern_fv (Assign x bop ty e1 e2) =
  {x} \<union> LLVM_type_lit_fv ty \<union> (base_lit_fv bop) \<union> (expr_pattern_fv expr_fv)  e1 \<union> (expr_pattern_fv expr_fv) e2" |
"instr_pattern_fv (Ret ty e) = LLVM_type_lit_fv ty \<union> (expr_pattern_fv expr_fv) e" |
"instr_pattern_fv (Br_i1 e) = (expr_pattern_fv expr_fv) e" |
"instr_pattern_fv (Br_label) = {}" |
"instr_pattern_fv (Alloca x ty) = {x} \<union> LLVM_type_lit_fv ty" |
"instr_pattern_fv (Load x ty e) = {x} \<union> LLVM_type_lit_fv ty \<union> (expr_pattern_fv expr_fv) e" |
"instr_pattern_fv (Store ty1 e1 ty2 e2) =
  LLVM_type_lit_fv ty1 \<union> (expr_pattern_fv expr_fv) e1 \<union> LLVM_type_lit_fv ty2 \<union> (expr_pattern_fv expr_fv) e2" |
"instr_pattern_fv (Cmpxchg x ty1 e1 ty2 e2 ty3 e3) =
  {x} \<union> LLVM_type_lit_fv ty1 \<union> (expr_pattern_fv expr_fv) e1 \<union> LLVM_type_lit_fv ty2 \<union> (expr_pattern_fv expr_fv) e2
   \<union> LLVM_type_lit_fv ty3 \<union> (expr_pattern_fv expr_fv) e3" |
"instr_pattern_fv (ICmp x cop ty e1 e2) =
  {x} \<union> lit_fv (\<lambda> x. {}) cop \<union> LLVM_type_lit_fv ty \<union> (expr_pattern_fv expr_fv) e1 \<union> (expr_pattern_fv expr_fv) e2" |
"instr_pattern_fv (Phi x ty phl) =
  {x} \<union> LLVM_type_lit_fv ty \<union> lit_fv philist_fv phl" |
"instr_pattern_fv (Call x ty el) = {x} \<union> LLVM_type_lit_fv ty \<union> lit_fv eplist_fv el" |
"instr_pattern_fv (IsPointer e) = (expr_pattern_fv expr_fv) e"

lemma finite_instr_pattern_fv [simp]:
 fixes instr shows "finite (instr_pattern_fv instr)"
by (case_tac instr, auto)

primrec instr_fv where
"instr_fv (Assign x _ _ e1 e2) = {x} \<union> expr_lfv e1 \<union> expr_lfv e2" |
"instr_fv (Ret _ e) = expr_lfv e" |
"instr_fv (Br_i1 e) = expr_lfv e" |
"instr_fv (Br_label) = {}" |
"instr_fv (Alloca x _) = {x}" |
"instr_fv (Load x _ e) = {x} \<union> expr_lfv e" |
"instr_fv (Store _ e1 _ e2) = expr_lfv e1 \<union> expr_lfv e2" |
"instr_fv (Cmpxchg x _ e1 _ e2 _ e3) = {x} \<union> expr_lfv e1 \<union> expr_lfv e2 \<union> expr_lfv e3" |
"instr_fv (ICmp x _ _ e1 e2) = {x} \<union> expr_lfv e1 \<union> expr_lfv e2" |
"instr_fv (Phi x _ es) = {x} \<union> (\<Union>(_, e)\<in>set es. expr_lfv e)" |
"instr_fv (Call x _ es) = {x} \<union> (\<Union>e\<in>set es. expr_lfv e)" |
"instr_fv (IsPointer e) = expr_lfv e"

datatype LLVM_decl = Global_Decl string concrete_LLVM_const

(* We aren't bothering with linking in this pass, surely. *)
(*datatype LLVM_function = Define LLVM_type string "LLVM_instr list"*)
(* Alternatively:*)
datatype LLVM_edge_type = seq | true | false | proc_call | ret

lemma finite_edge_types [simp]: "finite (UNIV::LLVM_edge_type set)"
apply (simp add: finite_conv_nat_seg_image)
apply (rule_tac x=5 in exI, rule_tac x="\<lambda>n. if n = 0 then seq else if n = 1 then true else
 if n = 2 then false else if n = 3 then proc_call else ret" in exI, auto)
apply (case_tac x, auto)
apply force
done
declare finite_edge_types [simp del] (* Why?  ---ELG *)

datatype ('node, 'var, 'type, 'expr, 'opr, 'cmp, 'phi_list, 'args) LLVM_function =
   Define 'type string "('type \<times> string) list" 
                    "('node, LLVM_edge_type, ('var, 'type, 'expr, 'opr, 'cmp, 'phi_list, 'args) LLVM_instr) flowgraph"
                     ("define _ __ { _ }")
(* Basic block structure? *)

datatype ('node, 'var, 'type, 'expr, 'opr, 'cmp,'phi_list, 'args) LLVM_module = 
 Module "LLVM_decl list" "('node, 'var, 'type, 'expr, 'opr, 'cmp, 'phi_list, 'args) LLVM_function list"
(* If we do this, we still have to parse a module into a tICFG.  We might instead skip everything
   after LLVM_instr and just work on t(I)CFGs of LLVM_instrs.  Doing this for now. *)

(* TODO: Improve program model - functions *)

(* Free variables *)

(* tICFG for LLVM module *)
fun LLVM_instr_edges where
"LLVM_instr_edges (Ret _ _) = {no_edges(ret := n) | n. True}" |
"LLVM_instr_edges (Br_i1 _) = {no_edges(true := 1, false := 1)}" |
"LLVM_instr_edges (Call _ _ _) = {no_edges(proc_call := 1, seq := 1)}" |
"LLVM_instr_edges _ = {no_edges(seq := (1::nat))}"

corollary one_seq [simp]: "finite (Edges G) \<Longrightarrow> (edge_types {(u, t). (n, u, t) \<in> Edges G} = no_edges(seq := Suc 0)) = 
 (\<exists>m. (n, m, seq) \<in> Edges G \<and> (\<forall>u t. (n, u, t) \<in> Edges G \<longrightarrow> u = m \<and> t = seq))"
by (drule_tac n=n and ty=seq in out_one, auto simp add: out_edges_def)

lemma out_br [simp]: "finite (Edges G) \<Longrightarrow> (edge_types (out_edges (Edges G) n) = 
 no_edges(true := Suc 0, false := Suc 0)) = 
 (\<exists>m1 m2. out_edges (Edges G) n = {(m1, true), (m2, false)})"
apply (rule iffI, frule_tac x=true in cong, simp, simp (no_asm_use) add: edge_types_def)
apply (frule_tac x=false in cong, simp, simp (no_asm_use) add: edge_types_def)
apply (auto simp add: card_Suc_eq)
done

(* Hypothesis: the additional bookkeeping involved in an ICFG is redundant for our purposes. 
   Calls and returns can be stored in edge labels. *)
(* Note that the tICFG assumes that threads execute mutually distinct code, i.e., don't execute 
   each other's procedures.   We'll run with that assumption for now. *)

(* Semantics *)
(* basic expressions *)
abbreviation "start_env \<equiv> \<lambda>x. CUndef"


primrec eval_expr (*:: "('a \<Rightarrow> 'b LLVM_const) \<Rightarrow> (char list \<Rightarrow> 'b LLVM_const) \<Rightarrow> 'a LLVM_expr \<Rightarrow> 'b LLVM_const" *)
where
"eval_expr env _ (Local i) = env i" | (* i::type of LLVM_expr *)
"eval_expr env _ (Const c) = c" |     (* c::LLVM_const *)
"eval_expr _ gt (Global i) = gt i"    (* i::string *)

term eval_expr

primrec cmp_helper where
"cmp_helper eq v1 v2 = (v1 = v2)" |
"cmp_helper ne v1 v2 = (v1 \<noteq> v2)" |
"cmp_helper sgt v1 v2 = (v1 > v2)" |
"cmp_helper sge v1 v2 = (v1 \<ge> v2)" |
"cmp_helper slt v1 v2 = (v1 < v2)" |
"cmp_helper sle v1 v2 = (v1 \<le> v2)"

fun eval_cmp where
"eval_cmp env gt cmp e1 e2 = (case (eval_expr env gt e1, eval_expr env gt e2) of
   (CInt v1, CInt v2) \<Rightarrow> if cmp_helper cmp v1 v2 then CInt 1 else CInt 0
 | (CPointer v1, CPointer v2) \<Rightarrow> if cmp_helper cmp v1 v2 then CInt 1 else CInt 0
 | _ \<Rightarrow> CUndef)"

fun eval where
"eval env gt opr e1 e2 = (case ((eval_expr env gt e1), (eval_expr env gt e2)) of
 (CInt v1, CInt v2)
    \<Rightarrow> (case opr of add \<Rightarrow> CInt (v1 + v2)
                  | sub \<Rightarrow> CInt (v1 - v2)
                  | mul \<Rightarrow> CInt (v1 * v2)) 
 | _ \<Rightarrow> CUndef)"

(* Copied and adapted the good bits from JinjaThreads' ToString.thy.  Why isn't this in Main? *)
function digit_toString :: "int \<Rightarrow> string"
where
  "digit_toString 0 = ''0''"
| "digit_toString 1 = ''1''"
| "digit_toString 2 = ''2''"
| "digit_toString 3 = ''3''"
| "digit_toString 4 = ''4''"
| "digit_toString 5 = ''5''"
| "digit_toString 6 = ''6''"
| "digit_toString 7 = ''7''"
| "digit_toString 8 = ''8''"
| "digit_toString 9 = ''9''"
| "n \<notin> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} ==> digit_toString n = undefined"
apply(case_tac x)
apply simp_all
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply simp
done
termination by lexicographic_order

function int_toString :: "int \<Rightarrow> string"
where
  "int_toString n = 
  (if n < 0 then ''-'' @ int_toString (- n)
   else if n < 10 then digit_toString n
   else int_toString (n div 10) @ digit_toString (n mod 10))"
by pat_completeness simp
termination by size_change

lemma neg_int_toString [simp]: "n < 0 \<Longrightarrow> int_toString n = ''-'' @ int_toString (- n)"
by simp

lemma digit_int_toString [simp]: "\<lbrakk>n \<ge> 0; n < 10\<rbrakk> \<Longrightarrow> int_toString n = digit_toString n"
by simp

lemma ten_int_toString [simp]: "n \<ge> 10 \<Longrightarrow> int_toString n = int_toString (n div 10) @ 
  digit_toString (n mod 10)"
by simp

lemmas int_toString.simps [simp del]

lemma int_digit: "\<lbrakk>(i::int) \<ge> 0; i < 10\<rbrakk> \<Longrightarrow> i \<in> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}"
by (case_tac i, auto)

lemma one_digit: "i \<in> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} \<Longrightarrow> length (digit_toString i) = 1"
by auto

lemma inj_digit: "\<lbrakk>i \<ge> 0; i < 10; j \<ge> 0; j < 10; digit_toString i = digit_toString j\<rbrakk> \<Longrightarrow> 
 i = j"
by (drule int_digit, simp, drule int_digit, auto)

(*
lemma toString_nonempty [simp]: "int_toString i \<noteq> []"
apply (induct rule: int_toString.induct)
apply (case_tac "n < 0", simp)
apply (case_tac "n < 10", simp)
apply (cut_tac i=n in one_digit [OF int_digit], simp+)
apply (case_tac "digit_toString n", simp, simp)
apply (simp only: ten_int_toString)
by (metis Nil_is_append_conv)
*)

abbreviation "nat_toString n \<equiv> int_toString (int n)"

lemma inj_toString: "\<lbrakk>int_toString x = int_toString y; x \<ge> 0; y \<ge> 0\<rbrakk> \<Longrightarrow> x = y"
oops

(* For now, a bogus calling convention: arguments are named arg0, etc. instead of
   using function definitions and formal parameter names. *)
primrec init_env_aux where
"init_env_aux _ _ [] _ = start_env" |
"init_env_aux env gt (e # rest) n = (init_env_aux env gt rest (Suc n))((''arg'' @ nat_toString n) := eval_expr env gt e)"
abbreviation "init_env env gt args \<equiv> init_env_aux env gt args 0"

term "seq"
locale LLVM_flowgraph = flowgraph
 where Nodes = "Nodes :: 'node set"
   and Start = "Start :: 'node" 
   and Exit ="Exit ::'node" 
   and Edges = "Edges :: ('node \<times> 'node \<times> LLVM_edge_type) set" 
   and L = "L::'node \<Rightarrow> ('var, 'type, 'expr, 'opr, 'cmp, 'phi_list, 'args) LLVM_instr"
   and instr_edges=LLVM_instr_edges
   and Seq="seq::LLVM_edge_type"
 for Nodes and Start and Exit and Edges and L

locale LLVM_tCFG = tCFG
 where CFGs = "CFGs::'thread \<Rightarrow> ('node, LLVM_edge_type, ('var, 'type, 'expr, 'opr, 'cmp, 'phi_list, 'args) LLVM_instr) flowgraph option" 
 and instr_edges=LLVM_instr_edges
 and Seq=seq
 for CFGs
begin

lemma LLVM_graph [simp, intro]: "CFGs t = Some G \<Longrightarrow> 
 LLVM_flowgraph (Nodes G) (Start G) (Exit G) (Edges G) (Label G)"
apply (frule CFGs, simp add: is_flowgraph_def flowgraph_def pointed_graph_def flowgraph_axioms_def)
apply (unfold_locales, auto)
apply force
apply force
done

end

print_locale memory_model
locale LLVM_MM = memory_model
 where free_set = "free_set :: 'memory \<Rightarrow> int set" 
    and can_read = "can_read :: 'memory \<Rightarrow> 'thread \<Rightarrow> int \<Rightarrow> (int, int) LLVM_const set" 
    and start_mem = "start_mem:: 'memory"
    and update_mem="update_mem::'memory \<Rightarrow> 
  ('thread, int, (int, int) LLVM_const) access set \<Rightarrow> 'memory \<Rightarrow> bool"
 for free_set and can_read and start_mem and update_mem

locale LLVM = LLVM_flowgraph (* ASSUMED INT *)
 where Nodes = "Nodes :: 'node set"
   and Start = "Start :: 'node" 
   and Exit ="Exit ::'node" 
   and Edges = "Edges :: ('node \<times> 'node \<times> LLVM_edge_type) set" 
   and L="L::'node \<Rightarrow> 'node concrete_LLVM_instr" + 
 LLVM_MM
 where free_set = "free_set :: 'memory \<Rightarrow> int set" 
    and can_read = "can_read :: 'memory \<Rightarrow> 'thread \<Rightarrow> int \<Rightarrow> (int, int) LLVM_const set" 
    and update_mem="update_mem::'memory \<Rightarrow> ('thread, int, concrete_LLVM_const) access set \<Rightarrow> 
  'memory \<Rightarrow> bool"
    and start_mem = "start_mem:: 'memory"
 for Nodes Start Exit Edges free_set can_read start_mem L update_mem
begin

(* Per-thread LLVM semantics *)
(* MSOS? *)

inductive LLVM_step where
assign [intro]: "\<lbrakk>L p = (x = opr ty e1, e2); p \<noteq> Exit\<rbrakk> \<Longrightarrow>
   LLVM_step t mem gt (p0, p, env, stack, allocad) {}
    (p, next_node Edges seq p, env(x := eval env gt opr e1 e2), stack, allocad)" |
ret_pop [intro]: "\<lbrakk>L p = Ret ty e; p \<noteq> Exit; (p, ret_addr, ret) \<in> Edges\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (_, p, env, (ret_addr, ret_var, ret_env, ret_allocad) # rest, allocad)
 (Free t ` allocad) (p, ret_addr, ret_env(ret_var := eval_expr env gt e), rest, ret_allocad)" |
ret_main [intro]: "\<lbrakk>L p = Ret ty e; p \<noteq> Exit; (p, Exit, ret) \<in> Edges\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (_, p, env, [], allocad) (Free t ` allocad)
 (p, Exit, env, [], {})" (* what to do when main function returns? *) |
branch_i [intro]: "\<lbrakk>L p = Br_i1 e; p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad) {}
 (p, next_node Edges (if eval_expr env gt e = CInt 0 then false else true) p, env, stack, allocad)" 
(* default to true unless cond is 0 *) |
branch_u [intro]: "\<lbrakk>L p = Br_label; p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad) {}
 (p, next_node Edges seq p, env, stack, allocad)" |
(* memory ops *)
alloca [intro!]: "\<lbrakk>L p = Alloca x ty; new_loc \<in> free_set mem; p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad)
 {Alloc t new_loc} (p, next_node Edges seq p, env(x := CPointer new_loc), stack, insert new_loc allocad)" |
load [intro!]: "\<lbrakk>L p = Load x ty e; eval_expr env gt e = CPointer l; v \<in> can_read mem t l; p \<noteq> Exit\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (_, p, env, stack, allocad) {Read t l v} (p, next_node Edges seq p, env(x := v), stack, allocad)" |
store [intro]: "\<lbrakk>L p = Store ty1 e1 ty2 e2; eval_expr env gt e2 = CPointer l; p \<noteq> Exit\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (_, p, env, stack, allocad) {Write t l (eval_expr env gt e1)} (p, next_node Edges seq p, env, stack, allocad)" |
cmpxchg_eq [intro]: "\<lbrakk>L p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3; eval_expr env gt e1 = CPointer l; v \<in> can_read mem t l;
 eval_expr env gt e2 = v; p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad) {ARW t l v (eval_expr env gt e3)}
 (p, next_node Edges seq p, env(x := v), stack, allocad)" |
cmpxchg_no [intro]: "\<lbrakk>L p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3; eval_expr env gt e1 = CPointer l; v \<in> can_read mem t l;
 eval_expr env gt e2 \<noteq> v; p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad) {ARW t l v v} 
 (p, next_node Edges seq p, env(x := v), stack, allocad)" |
icmp [intro]: "\<lbrakk>L p = (x = icmp cmp ty e1, e2); p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad) {}
 (p, next_node Edges seq p, env(x := eval_cmp env gt cmp e1 e2), stack, allocad)" |
phi [intro]: "\<lbrakk>L p = (x = phi ty vals); p \<noteq> Exit; (p0, e) \<in> set vals\<rbrakk> \<Longrightarrow> LLVM_step t mem gt
 (p0, p, env, stack, allocad) {} (p, next_node Edges seq p, env(x := eval_expr env gt e), stack, allocad)" |
call [intro]: "\<lbrakk>L p = (x = call ty args); p \<noteq> Exit\<rbrakk> \<Longrightarrow> LLVM_step t mem gt (_, p, env, stack, allocad) {}
 (p, next_node Edges proc_call p, init_env env gt args, (next_node Edges seq p, x, env, allocad) # stack, {})" |
ispointer [intro]: "\<lbrakk>L p = IsPointer e; eval_expr env gt e = CPointer l; p \<noteq> Exit\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (_, p, env, stack, allocad) {} (p, next_node Edges seq p, env, stack, allocad)"

lemma step_next [simp]: "LLVM_step t mem gt (p0, p, rest) a (p', rest') \<Longrightarrow> p' = p"
by (erule LLVM_step.cases, simp_all)

lemma not_exit: "LLVM_step t mem gt (p0, p, rest) a C' \<Longrightarrow> p \<noteq> Exit"
by (erule LLVM_step.cases, simp_all)

lemma branch_true [intro]: "\<lbrakk>L p = Br_i1 e; p \<noteq> Exit; eval_expr env gt e \<noteq> CInt 0\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (p0, p, env, stack, allocad) {} (p, next_node Edges true p, env, stack, allocad)" 
by (smt branch_i)

lemma branch_false [intro]: "\<lbrakk>L p = Br_i1 e; p \<noteq> Exit; eval_expr env gt e = CInt 0\<rbrakk> \<Longrightarrow> 
 LLVM_step t mem gt (p0, p, env, stack, allocad) {} (p, next_node Edges false p, env, stack, allocad)" 
by (smt branch_i)

end

definition "alloc_mem r \<equiv> case r of (stack, allocad) \<Rightarrow> allocad \<union> (\<Union>(a, b, c, d)\<in>set stack. d)"

context LLVM begin

lemma finite_ops: "\<lbrakk>LLVM_step t mem gt (p0, p, env, stack, allocad) ops (p, p', env', stack', allocad'); 
 finite (alloc_mem (stack, allocad))\<rbrakk> \<Longrightarrow> finite ops \<and> finite (alloc_mem (stack', allocad'))"
by (erule LLVM_step.cases, auto simp add: alloc_mem_def)

lemma step_mem: "\<lbrakk>LLVM_step t mem gt (p0, p, env, stack, allocad) ops (p, p', env', stack', allocad'); 
 l \<notin> free_set mem; l \<notin> alloc_mem (stack, allocad)\<rbrakk> \<Longrightarrow> l \<notin> alloc_mem (stack', allocad')"
by (erule LLVM_step.cases, auto simp add: alloc_mem_def)

end

type_synonym ('thread, 'node) LLVM_tCFG =
 "('thread, ('node, LLVM_edge_type, 'node concrete_LLVM_instr) flowgraph) map"

context LLVM_MM begin

(* Process global variable declarations to get initial environments and memory. *)
inductive declare_global where
global [intro!]: "\<lbrakk>new_loc \<in> free_set mem; update_mem mem {Alloc t new_loc} mem'; 
 update_mem mem' {ARW t' new_loc CUndef c} mem''\<rbrakk> \<Longrightarrow> 
 declare_global (env, mem) (Global_Decl s c) (env(s := CPointer new_loc), mem'')"
inductive declare_globals where
no_globals [intro!, simp]: "declare_globals (env, mem) [] (env, mem)" |
a_global [intro!]: "\<lbrakk>declare_global (env, mem) d (env', mem'); 
 declare_globals (env', mem') rest (env'', mem'')\<rbrakk> \<Longrightarrow>
 declare_globals (env, mem) (d # rest) (env'', mem'')"

lemma declare_past: "\<lbrakk>\<forall>c. Global_Decl s c \<notin> set ds; declare_globals (env, mem0) ds (gt, mem)\<rbrakk> \<Longrightarrow>
 gt s = env s"
apply (induct ds arbitrary: env mem0, auto)
apply (erule declare_globals.cases, clarsimp+)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
done

lemma declare_not_free: "\<lbrakk>l \<notin> free_set mem; declare_globals (env, mem) ds (gt, mem')\<rbrakk> \<Longrightarrow>
 l \<notin> free_set mem'"
apply (induct ds arbitrary: env mem, auto)
apply (erule declare_globals.cases, clarsimp+)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
apply (drule stays_not_free, simp+)+
apply force
done

lemma global_alloc: "\<lbrakk>Global_Decl s c \<in> set ds; declare_globals C ds (gt, mem)\<rbrakk> \<Longrightarrow>
 \<exists>l. gt s = CPointer l \<and> l \<notin> free_set mem"
apply (induct ds arbitrary: c C gt mem, auto)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
apply (case_tac "\<exists>c. Global_Decl s c \<in> set rest", clarsimp+)
apply (drule declare_past, simp+)
apply (drule alloc_not_free, force, simp+)
apply (drule stays_not_free, simp+)
apply (drule declare_not_free, simp+)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
done

lemma declare_new: "\<lbrakk>Global_Decl s c \<in> set ds; declare_globals (e, mem) ds (gt, mem'); 
 gt s = CPointer l\<rbrakk> \<Longrightarrow> l \<in> free_set mem"
apply (induct ds arbitrary: e mem c, auto)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
apply (case_tac "\<exists>c. Global_Decl s c \<in> set rest", clarsimp)
apply (rule ccontr, drule stays_not_free, simp+, drule stays_not_free, simp+)
apply (drule declare_past, simp+)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
apply (rule ccontr, drule stays_not_free, simp+, drule stays_not_free, simp+)
done

lemma global_diff: "\<lbrakk>Global_Decl s c \<in> set ds; Global_Decl s' c' \<in> set ds; 
 declare_globals C ds (gt, mem); gt s = gt s'\<rbrakk> \<Longrightarrow> s = s'"
apply (frule global_alloc, simp+, clarsimp)
apply (induct ds arbitrary: c c' C, auto)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
apply (case_tac "\<exists>c. Global_Decl s c \<in> set rest", clarsimp+)
apply (drule declare_past, simp+)
apply (drule declare_new, simp+)
apply (drule alloc_not_free, force, simp+)
apply (drule stays_not_free, simp+)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
apply (case_tac "\<exists>c. Global_Decl s' c \<in> set rest", clarsimp+)
apply (drule declare_past, simp+)
apply (drule declare_new, simp+)
apply (drule alloc_not_free, force, simp+)
apply (drule stays_not_free, simp+)
apply (erule declare_globals.cases, auto elim!: declare_global.cases)
done

end

locale LLVM_decls = fixes decls::"LLVM_decl list"

locale LLVM_base =
 LLVM_MM
 where free_set = "free_set :: 'memory \<Rightarrow> int set" 
    and can_read = "can_read :: 'memory \<Rightarrow> 'thread \<Rightarrow> int \<Rightarrow> (int, int) LLVM_const set" 
    and start_mem = "start_mem:: 'memory"
    and update_mem="update_mem::'memory \<Rightarrow> 
  ('thread, int, (int, int) LLVM_const) access set \<Rightarrow> 'memory \<Rightarrow> bool" +
 LLVM_decls where decls = "decls::LLVM_decl list"
 for free_set and can_read and start_mem and update_mem and decls +
 fixes gt::"string \<Rightarrow> concrete_LLVM_const"
begin

abbreviation "step t G mem \<equiv> LLVM.LLVM_step (Exit G) (Edges G) free_set can_read (Label G) t mem gt"

lemma LLVM_graph': "is_flowgraph G seq LLVM_instr_edges \<Longrightarrow> 
  LLVM (Nodes G) (Start G) (Exit G) (Edges G) free_set (Label G) update_mem"
by (simp add: LLVM_def is_flowgraph_def LLVM_flowgraph_def, unfold_locales)

lemmas step_cases' = LLVM.LLVM_step.cases [OF LLVM_graph']
lemmas step_next' [simp] = LLVM.step_next [OF LLVM_graph']

lemma out_edges_shape: "\<lbrakk>{(u, t). (p, u, t) \<in> Edges G} = S; (p', t) \<in> S\<rbrakk> \<Longrightarrow>
  (p, p', t) \<in> Edges G"
by force

lemma step_along_edge': "\<lbrakk>is_flowgraph G seq LLVM_instr_edges; step t G m (pp, p, r) a (p, p', r'); p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 \<exists>e. (p, p', e) \<in> Edges G"
apply (subgoal_tac "LLVM (Nodes G) (Start G) (Exit G) (Edges G) free_set (Label G) update_mem") 
apply (clarsimp simp add: is_flowgraph_def flowgraph_def flowgraph_axioms_def)
apply ((erule_tac x=p in allE)+)
apply (frule pointed_graph.finite_edges)
apply (erule LLVM.LLVM_step.cases, simp_all, simp_all, clarsimp)
apply (clarsimp simp add: out_edges_def, force)
apply (clarsimp simp add: out_edges_def, force)
apply force
apply clarsimp
apply (rule conjI, clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (clarsimp simp add: out_edges_def, frule_tac p'=p' in out_edges_shape, force, force)
apply (simp add: LLVM_def LLVM_flowgraph_def is_flowgraph_def, unfold_locales)
done

end

lemmas option.splits [split]

(* Concurrent semantics *)
fun get_point where "get_point (_, p, _) = p"

sublocale LLVM_base \<subseteq> step_rel where free_set=free_set and update_mem=update_mem 
  and start_mem=start_mem and can_read=can_read and step_rel=step
  and get_point=get_point 
  and instr_edges="LLVM_instr_edges::'node concrete_LLVM_instr \<Rightarrow> (LLVM_edge_type \<Rightarrow> nat) set" 
  and Seq=seq 
  and start_state="\<lambda>CFGs C0 mem0. declare_globals (start_env, start_mem) decls (gt, mem0) \<and> 
     C0 = (\<lambda>t. case CFGs t of Some G \<Rightarrow> Some (Start G, Start G, start_env, [], {}) | None \<Rightarrow> None)"
apply unfold_locales
apply (rule ext, simp add: start_points_def map_comp_def)
apply clarsimp
apply (frule step_next', simp, clarsimp)
apply (metis step_along_edge')
done

lemma (in LLVM_base) one_step_next: "\<lbrakk>one_step t G ((p0, p, rest), m) ((p', rest'), m');
  is_flowgraph G seq LLVM_instr_edges\<rbrakk> \<Longrightarrow> p' = p"
by (erule one_step.cases, auto)

print_locale LLVM_base
locale LLVM_threads = LLVM_tCFG
 where CFGs="CFGs::('thread, 'node) LLVM_tCFG" + 
 LLVM_base
 where update_mem="update_mem::'memory \<Rightarrow> ('thread, int, concrete_LLVM_const) access set \<Rightarrow> 'memory \<Rightarrow> bool"
   and free_set = "free_set :: 'memory \<Rightarrow> int set" 
    and can_read = "can_read :: 'memory \<Rightarrow> 'thread \<Rightarrow> int \<Rightarrow> (int, int) LLVM_const set" 
    and start_mem = "start_mem:: 'memory"
    and decls = "decls::LLVM_decl list"
    and gt = "gt::char list \<Rightarrow> (int, int) LLVM_const" 
 for free_set CFGs update_mem can_read start_mem decls gt

begin

lemma LLVM_graph [simp, intro]: "CFGs t = Some G \<Longrightarrow> 
 LLVM (Nodes G) (Start G) (Exit G) (Edges G) free_set (Label G) update_mem"
by (frule CFGs, erule LLVM_graph')

lemmas step_cases = LLVM.LLVM_step.cases [OF LLVM_graph]
lemmas step_next [simp] = LLVM.step_next [OF LLVM_graph]

lemma step_along_edge: "\<lbrakk>CFGs t = Some G; step t G m (pp, p, r) a (p, p', r'); p \<in> Nodes G\<rbrakk> \<Longrightarrow> 
 \<exists>e. (p, p', e) \<in> Edges G"
by (rule step_along_edge', drule CFGs, auto)

abbreviation "conc_step_star \<equiv> (conc_step CFGs)^**"

lemma ops_thread: "\<lbrakk>step t G mem state ops state'; CFGs t = Some G; a \<in> ops\<rbrakk> \<Longrightarrow> get_thread a = t"
by (rule step_cases, auto)

definition "all_alloc_mem states \<equiv> \<Union>(a0, a, b, c, d)\<in>ran states. alloc_mem (c, d)"

lemma run_global: "\<lbrakk>run_prog CFGs C; Global_Decl s c \<in> set decls\<rbrakk> \<Longrightarrow>
 \<exists>l. gt s = CPointer l \<and> l \<notin> free_set (snd C) \<and> l \<notin> all_alloc_mem (fst C)"
apply (rule run_prog_induct, simp, clarsimp simp add: run_prog_def)
apply (drule global_alloc, simp+, clarsimp simp add: all_alloc_mem_def ran_def alloc_mem_def 
 split: option.splits)
apply clarsimp
apply (erule conc_step.cases, clarsimp simp add: all_alloc_mem_def ran_def)
apply (rule conjI, clarsimp)
apply (drule stays_not_free, simp, clarsimp simp add: alloc_mem_def)
apply (drule step_cases, simp, simp_all, force, force)
apply clarsimp
apply (case_tac "al \<noteq> t", force, clarsimp)
apply (frule step_next, simp+)
apply (drule_tac can_read=can_read and t=t in LLVM.step_mem [OF LLVM_graph], simp+, force, simp)
done

lemma call_edges [simp]: "finite (Edges G) \<Longrightarrow>
  (edge_types (out_edges (Edges G) p) = no_edges(proc_call := Suc 0, seq := Suc 0))
 = (\<exists>m n. out_edges (Edges G) p = {(m, proc_call), (n, seq)})"
by simp

end

(* Memory models *)
locale LLVM_TSO = tCFG where instr_edges=LLVM_instr_edges and Seq=seq and 
  CFGs="CFGs::('thread, 'node) LLVM_tCFG" + TSO where undef="CUndef::concrete_LLVM_const" for CFGs

sublocale LLVM_TSO \<subseteq> TSO: LLVM_threads where update_mem=update_mem and free_set=free_set 
  and can_read=can_read and start_mem=start_mem
by (unfold_locales)

locale LLVM_SC = tCFG where instr_edges=LLVM_instr_edges and Seq=seq and 
  CFGs="CFGs::('thread, 'node) LLVM_tCFG" + SC where undef="CUndef::concrete_LLVM_const" for CFGs

sublocale LLVM_SC \<subseteq> SC: LLVM_threads where update_mem=update_mem and free_set=free_set 
  and can_read=can_read and start_mem=start_mem
by (unfold_locales)

locale LLVM_PSO = tCFG where instr_edges=LLVM_instr_edges and Seq=seq and 
  CFGs="CFGs::('thread, 'node) LLVM_tCFG" + PSO where undef="CUndef::concrete_LLVM_const" for CFGs

sublocale LLVM_PSO \<subseteq> PSO: LLVM_threads where update_mem=update_mem and free_set=free_set 
  and can_read=can_read and start_mem=start_mem
by (unfold_locales)

lemma (in LLVM_SC) safe_mem: "\<lbrakk>l \<notin> free_set mem; l \<notin> alloc_mem (stack, allocad); CFGs t = Some G;
 LLVM.LLVM_step (Exit G) (Edges G) free_set can_read (Label G) t mem gt (p0, p, env, stack, allocad) 
 ops (p, p', env', stack', allocad'); update_mem mem ops mem'; finite (alloc_mem (stack, allocad))\<rbrakk> \<Longrightarrow>
 l \<notin> free_set mem' \<and> l \<notin> alloc_mem (stack', allocad') \<and> finite (alloc_mem (stack', allocad'))"
by (rule LLVM.LLVM_step.cases, erule LLVM_graph, simp, auto simp add: alloc_mem_def)

(* Memory models in LLVM. *)
context LLVM_threads begin

declare step_cases [elim]

abbreviation "step_SC \<equiv> LLVM_base.step SC.free_set SC.can_read gt"
abbreviation "step_TSO \<equiv> LLVM_base.step TSO.free_set TSO.can_read gt"

declare eval.simps [simp del] eval_cmp.simps [simp del]

end

(*context LLVM_SC begin

lemma LLVM_TSO_graph: "CFGs t = Some G \<Longrightarrow> LLVM (Nodes G) (Start G) (Exit G) (Edges G) TSO.free_set 
 (Label G) TSO.update_mem"
apply (drule LLVM_graph, clarsimp simp add: LLVM_def)
apply unfold_locales
apply (metis TSO_alloc_not_free)
apply (metis TSO_stays_not_free)
done

(* automate? *)
lemma SC_lt_TSO_step: "\<lbrakk>step_SC t mem gt state ops state'; t \<in> dom CFGs\<rbrakk> \<Longrightarrow> 
 step_TSO t (mem, \<lambda>t. []) gt state ops state'"
apply (drule domD, clarsimp)
apply (rule step_cases, simp_all, simp_all)
apply (rule LLVM.assign, rule LLVM_TSO_graph, simp+)
apply (rule LLVM.ret_pop, rule LLVM_TSO_graph, simp+)
apply (rule LLVM.ret_main, rule LLVM_TSO_graph, simp_all, force)
apply (rule conjI)
apply (clarsimp, rule LLVM.branch_false, rule LLVM_TSO_graph, simp+)
apply (clarsimp, rule LLVM.branch_true, rule LLVM_TSO_graph, simp+)
apply (rule LLVM.branch_u, rule LLVM_TSO_graph, simp+)
apply (rule LLVM.alloca, rule LLVM_TSO_graph, simp_all)
apply (rule LLVM.load, rule LLVM_TSO_graph, simp, force, simp+)
apply (rule LLVM.store, rule LLVM_TSO_graph, simp_all, force)
apply (rule LLVM.cmpxchg_eq, rule LLVM_TSO_graph, simp, force, simp+)
apply (rule LLVM.cmpxchg_no, rule LLVM_TSO_graph, simp, force, simp+)
apply (rule LLVM.icmp, rule LLVM_TSO_graph, simp+)
apply (rule LLVM.phi, rule LLVM_TSO_graph, simp+, force, simp+)
apply (rule LLVM.call, rule LLVM_TSO_graph, simp+)
apply (rule LLVM.ispointer, rule LLVM_TSO_graph, auto)
done

thm LLVM_threads.step_thread
abbreviation "conc_step_SC \<equiv> LLVM_threads.conc_step free_set_SC CFGs can_read_SC update_mem_SC"
abbreviation "conc_step_TSO \<equiv> LLVM_threads.conc_step free_set_TSO CFGs can_read_TSO update_mem_TSO"

lemma SC_lt_TSO_step_threads: "conc_step_SC gt (states, mem) (states', mem') \<Longrightarrow> 
 conc_step_TSO gt (states, mem, \<lambda>t. []) (states', mem', \<lambda>t. [])"
apply (rule LLVM_threads.conc_step.cases, unfold_locales, simp, clarsimp)
apply (rule_tac ops=ops in LLVM_threads.step_thread, unfold_locales)
apply (metis TSO_alloc_not_free)
apply (metis TSO_stays_not_free)
apply (simp add: dom_def, force)
apply (cut_tac t=t in SC_lt_TSO_step, auto)
done

term LLVM_threads.conc_step_star
abbreviation "conc_step_star_SC \<equiv> LLVM_threads.conc_step_star free_set_SC CFGs can_read_SC update_mem_SC"
abbreviation "conc_step_star_TSO \<equiv> LLVM_threads.conc_step_star free_set_TSO CFGs can_read_TSO update_mem_TSO"

(* SC is stricter than TSO. *)
theorem SC_lt_TSO_star: "conc_step_star_SC gt (states, mem) (states', mem') \<Longrightarrow> 
 conc_step_star_TSO gt (states, mem, \<lambda>t. []) (states', mem', \<lambda>t. [])"
apply (induct rule: rtranclp_induct2, auto)
apply (drule SC_lt_TSO_step_threads, auto)
done

end*)

(* Patterns and substitution *)
(*
type_synonym 'mvar pattern =
 "(('mvar node_lit, 'mvar, (LLVM_type, 'mvar) literal, 
 ('mvar, ('mvar,int) LLVM_expr) expr_pattern, (LLVM_op, 'mvar) literal, (LLVM_cmp, 'mvar) literal) LLVM_instr, 'mvar) literal"
*)
term "expr_pattern_fv"
(* Replaced by earlier instr_pattern_fv
primrec instr_pattern_fv :: "(string, LLVM_type_pat, LLVM_expr_pat, LLVM_op pat, (LLVM_cmp,'mvar)literal,
 (string node_const pat \<times> LLVM_expr_pat)list pat, LLVM_expr_pat list pat) LLVM_instr \<Rightarrow> string set" where
"instr_pattern_fv (Assign x opr ty e1 e2) = {x} \<union> base_lit_fv opr \<union> LLVM_type_lit_fv ty \<union> expr_pattern_fv expr_fv e1 \<union> expr_pattern_fv expr_fv e2" |
"instr_pattern_fv (Ret ty e) = LLVM_type_lit_fv ty \<union> expr_pattern_fv expr_fv e" |
"instr_pattern_fv (Br_i1 e) = expr_pattern_fv expr_fv e" |
"instr_pattern_fv (Br_label) = {}" |
"instr_pattern_fv (Alloca x ty) = {x} \<union> LLVM_type_lit_fv ty" |
"instr_pattern_fv (Load x ty e) = {x} \<union> LLVM_type_lit_fv ty \<union> expr_pattern_fv expr_fv e" |
"instr_pattern_fv (Store ty1 e1 ty2 e2) = LLVM_type_lit_fv ty1 \<union> expr_pattern_fv expr_fv e1 \<union> LLVM_type_lit_fv ty2 \<union> expr_pattern_fv expr_fv e2" |
"instr_pattern_fv (Cmpxchg x ty1 e1 ty2 e2 ty3 e3) = {x} \<union> LLVM_type_lit_fv ty1 \<union> expr_pattern_fv expr_fv e1 \<union> 
 LLVM_type_lit_fv ty2 \<union> expr_pattern_fv expr_fv e2 \<union> LLVM_type_lit_fv ty3 \<union> expr_pattern_fv expr_fv e3" |
"instr_pattern_fv (ICmp x cmp ty e1 e2) = {x} \<union> base_lit_fv cmp \<union> LLVM_type_lit_fv ty \<union> expr_pattern_fv expr_fv e1 \<union> expr_pattern_fv expr_fv e2" |
"instr_pattern_fv (Phi x ty es) = {x} \<union> LLVM_type_lit_fv ty \<union> lit_fv philist_fv es
(*(\<Union>(n, e)\<in>set es. node_fv n \<union> expr_pattern_fv expr_fv e)*)" |
"instr_pattern_fv (Call x ty es) = {x} \<union> LLVM_type_lit_fv ty \<union> lit_fv eplist_fv es
 (*(\<Union>e\<in>set es. expr_pattern_fv expr_fv e)*)" |
"instr_pattern_fv (IsPointer e) = expr_pattern_fv expr_fv e"

lemma finite_instr_pattern_fv [simp]: "finite (instr_pattern_fv i)"
by (induct i, auto)
*)

abbreviation pattern_fv::" ('mvar gen_LLVM_instr, 'mvar)literal  \<Rightarrow> 'mvar set" where
"pattern_fv \<equiv> \<lambda> p. lit_fv instr_pattern_fv p"

lemma finite_pattern_fv [simp]:
fixes p shows "finite (pattern_fv p)"
by (case_tac p, auto)

(* Applying a valuation of metavariables to an expression pattern yields a concrete expression. *)

(* Objects are the values metavariables can take. *)
datatype ('thread, 'node, 'mvar) object =
   ONode 'node 
 | OThread 'thread
 | OInt int
 | OLoc int
 | OType LLVM_type
 | OConst concrete_LLVM_const
 | OExpr concrete_LLVM_expr
 | OVarName "string"
 | OInstr "'node concrete_LLVM_instr"
 | OSynFunc "'mvar" "'mvar gen_LLVM_expr"
 | OEdgeType LLVM_edge_type
 | OOp LLVM_op
 | OCmp LLVM_cmp
 | OPhiList "'node concrete_philist"
 | OEPList "concrete_LLVM_expr list"

fun get_node where "get_node (ONode n) = Some n" | "get_node _ = None"
fun get_thread where "get_thread (OThread t) = Some t" | "get_thread _ = None"
fun get_int where "get_int (OInt n) = Some n" | "get_int _ = None"
fun get_memloc where "get_memloc (OLoc n) = Some n" | "get_memloc _ = None"
fun get_type where "get_type (OType ty) = Some ty" | "get_type _ = None"
fun get_const where "get_const (OConst n) = Some n" | "get_const _ = None"
fun get_expr where "get_expr (OExpr n) = Some n" | "get_expr _ = None"
fun get_var_name where "get_var_name (OVarName v) = Some v" | "get_var_name _ = None"
(*
fun get_local_var where "get_local_var (OExpr (Local v)) = Some v" | "get_local_var _ = None"
fun get_global_var where "get_global_var (OExpr (Global v)) = Some v" | "get_global_var _ = None"
*)
fun get_instr where "get_instr (OInstr i) = Some i" | "get_instr _ = None"
fun get_synfunc where "get_synfunc (OSynFunc x f) = Some (x, f)" | "get_synfunc _ = None"
fun get_edgetype where "get_edgetype (OEdgeType e) = Some e" | "get_edgetype _ = None"
fun get_op where "get_op (OOp n) = Some n" | "get_op _ = None"
fun get_cmp where "get_cmp (OCmp n) = Some n" | "get_cmp _ = None"
fun get_philist where "get_philist (OPhiList phl) = Some phl" | "get_philist _ = None"
fun get_eplist where "get_eplist (OEPList epl) = Some epl" | "get_eplist _ = None"

primrec LLVM_type_lit_subst where
  "LLVM_type_lit_subst \<sigma> PInt_ty = Some Int_ty"
| "LLVM_type_lit_subst \<sigma> (Tymvar x) = get_type (\<sigma> x)"
| "LLVM_type_lit_subst \<sigma> (PPointer_ty pty) =
   (case LLVM_type_lit_subst \<sigma> pty of Some ty \<Rightarrow> Some (Pointer_ty ty)  | _ \<Rightarrow> None)"

lemma LLVM_type_lit_same_subst [simp]:
 "\<forall>x\<in>LLVM_type_lit_fv ty. \<sigma> x = \<sigma>' x \<Longrightarrow>
  LLVM_type_lit_subst \<sigma> ty = LLVM_type_lit_subst \<sigma>' ty"
by (induct ty, auto)


primrec const_subst :: "('mvar \<Rightarrow> ('thread, 'node, 'mvar) object) \<Rightarrow>
 'mvar gen_LLVM_const \<Rightarrow> concrete_LLVM_const option" where
  "const_subst \<sigma> (CInt ip) = map_option CInt (base_lit_subst get_int \<sigma> ip)"
| "const_subst \<sigma> CNull = Some CNull"
| "const_subst \<sigma> (CPointer ip) = map_option CPointer (base_lit_subst get_int \<sigma> ip)"
| "const_subst \<sigma> CUndef = Some CUndef"

lemma const_same_subst [simp]: "\<forall>x\<in>LLVM_const_lit_fv c. \<sigma> x = \<sigma>' x \<Longrightarrow> const_subst \<sigma> c = const_subst \<sigma>' c"
proof (cases c, auto)
 fix var
 assume A: "\<forall>x\<in>base_lit_fv var. \<sigma> x = \<sigma>' x " and B: "c = CInt var"
 from A
 have B: "base_lit_subst get_int \<sigma> var = base_lit_subst get_int \<sigma>' var"
 by simp
 from B
 show "map_option CInt (base_lit_subst get_int \<sigma> var) = map_option CInt (base_lit_subst get_int \<sigma>' var)"
 by simp
 next fix loc
 assume A: "\<forall>x\<in>base_lit_fv loc. \<sigma> x = \<sigma>' x" and B: "c = CPointer loc"
 from A
 have B: "base_lit_subst get_int \<sigma> loc = base_lit_subst get_int \<sigma>' loc"
 by simp
 from B
 show " map_option CPointer (base_lit_subst get_int \<sigma> loc) = map_option CPointer (base_lit_subst get_int \<sigma>' loc)"
 by simp
qed

primrec expr_subst ::
 "('mvar \<Rightarrow> ('thread, 'node, 'mvar) object) \<Rightarrow> 'mvar gen_LLVM_expr \<Rightarrow>
  concrete_LLVM_expr option" where
  "expr_subst \<sigma> (Local i) = map_option Local (get_var_name (\<sigma> i))" 
| "expr_subst \<sigma> (Const p) = map_option Const (lit_subst const_subst get_const \<sigma> p)"
| "expr_subst \<sigma> (Global s) = map_option Global (get_var_name (\<sigma> s))"

term "expr_subst"

lemma expr_same_subst [simp]:
 fixes \<sigma> :: "'mvar \<Rightarrow> ('thread, 'node, 'mvar) object"
   and \<sigma>' :: "'mvar \<Rightarrow> ('thread, 'node, 'mvar) object"
   and e :: "'mvar gen_LLVM_expr"
 shows "\<forall>v\<in>expr_fv e. \<sigma> v = \<sigma>' v \<Longrightarrow> expr_subst \<sigma> e = expr_subst \<sigma>' e"
proof (case_tac e, auto, case_tac cvar, simp_all)
 fix c :: "'mvar gen_LLVM_const"
 assume A: "\<forall>(v::'mvar)\<in>LLVM_const_lit_fv c. \<sigma> v = \<sigma>' v"
 from A have A1: "const_subst \<sigma> c = const_subst \<sigma>' c" by simp
 from A1
 show "map_option Const (const_subst \<sigma> c) = map_option Const (const_subst \<sigma>' c)" by simp
qed

term "expr_subst"

(* Why would you expect this to be true?  You could very well have two different
   metavariables referring to the same programming variable 
lemma self_subst: "expr_subst (\<lambda>y. OExpr (Local y)) e = Some e"
by (induct e, auto)

corollary subst_out: "\<forall>v\<in>expr_fv e. \<sigma> v = OExpr (Local v) \<Longrightarrow> expr_subst \<sigma> e = Some e"
by (rule trans, rule expr_same_subst, auto simp add: self_subst)

lemma sub_out: "\<lbrakk>v \<in> expr_fv e; v' \<notin> expr_fv e\<rbrakk> \<Longrightarrow> \<exists>e'. 
 expr_subst ((\<lambda>y. OExpr (Local y))(v := OExpr (Local v'))) e = Some e' \<and>
 expr_subst ((\<lambda>y. OExpr (Local y))(v' := OExpr (Local v))) e' = Some e"
by (induct e, auto)
*)

primrec expr_pattern_subst :: "('mvar \<Rightarrow> ('thread, 'node, 'mvar) object) \<Rightarrow>
 'mvar LLVM_expr_pat \<Rightarrow> concrete_LLVM_expr option"
 where
"expr_pattern_subst \<sigma> (EPInj e) = expr_subst \<sigma> e"
(*| "expr_pattern_subst \<sigma> (x<e>) = (case (\<sigma> x, expr_subst \<sigma> e) of 
 (OSynFunc x e, Some e') \<Rightarrow> expr_subst ((\<lambda>y. OExpr (Local y))(x := OExpr e')) e
 | _ \<Rightarrow> None)"*)
| "expr_pattern_subst \<sigma> (x<e>) =
    (case (\<sigma> x, expr_subst \<sigma> e) of (OSynFunc y e', Some e'') \<Rightarrow>
       expr_subst (\<lambda> y. ((OExpr e''):: ('thread, 'node, 'mvar) object)) e'
      | _ \<Rightarrow> None)"
| "expr_pattern_subst \<sigma> (EPMVar x) = get_expr (\<sigma> x)"


(* Isabelle note: this type annotation is necessary because OExpr e', in itself,
   is of type (?, ?) object.  We need to identify the missing types with existing
   type variables, or they'll be introduced as separate variables. *)

lemma expr_pattern_same_subst [simp]: "\<forall>v\<in>expr_pattern_fv expr_fv e. \<sigma> v = \<sigma>' v \<Longrightarrow>
 expr_pattern_subst \<sigma> e = expr_pattern_subst \<sigma>' e"
apply (induct e, auto split: object.split LLVM_expr.split)
apply (drule expr_same_subst, simp)+
done

term "(\<lambda> epl'. map_option (\<lambda> ep'. ep' # epl) (expr_pattern_subst \<sigma> ep))"

abbreviation eplist_subst :: "('mvar \<Rightarrow> ('thread, 'node, 'mvar) object) \<Rightarrow>
 'mvar LLVM_expr_pat list \<Rightarrow> concrete_LLVM_expr list option" where
"eplist_subst \<equiv> 
\<lambda> \<sigma> epl. foldr 
 (\<lambda> ep r. flatten_option
    (map_option
      (\<lambda> epl'. map_option (\<lambda> ep'. ep' # epl') (expr_pattern_subst \<sigma> ep))
      r)) epl (Some [])"

(* Reformulate this in terms of map_option and flatten_option ---ELG *)
lemma eplist_same_subst :
"\<forall> es. (\<forall>v\<in>eplist_fv es. \<sigma> v = \<sigma>' v) \<longrightarrow> (eplist_subst \<sigma> es = eplist_subst \<sigma>' es)"
proof (rule allI)
 fix es 
 show "(\<forall>v\<in>eplist_fv es. \<sigma> v = \<sigma>' v) \<longrightarrow> (eplist_subst \<sigma> es = eplist_subst \<sigma>' es)"
 proof (induct es, auto)
  fix a es
  assume A1: "eplist_subst \<sigma> es = eplist_subst \<sigma>' es"
   and A2: "\<forall>v\<in>expr_pattern_fv expr_fv a \<union> eplist_fv es. \<sigma> v = \<sigma>' v"
  show "flatten_option (map_option (\<lambda>epl'. map_option (\<lambda>ep'. ep' # epl') (expr_pattern_subst \<sigma> a)) (eplist_subst \<sigma>' es)) =
       flatten_option (map_option (\<lambda>epl'. map_option (\<lambda>ep'. ep' # epl') (expr_pattern_subst \<sigma>' a)) (eplist_subst \<sigma>' es))"
  proof -
   from A2
   have A3: "expr_pattern_subst \<sigma> a = expr_pattern_subst \<sigma>' a"
   by auto
   from A3 show ?thesis
   by simp
  qed
 qed
qed

(* We make no assumptions about our type of concrete nodes here *)
fun node_subst where
  "node_subst CFGs \<sigma> (MVar m) = get_node (\<sigma> m)"
| "node_subst CFGs \<sigma> (Inj (NExit t)) = map_option Exit (flatten_option (map_option CFGs (get_thread (\<sigma> t))))"
(*   (case \<sigma> t of OThread t' \<Rightarrow>  map_option Exit t' | _ \<Rightarrow> None) *)
| "node_subst CFGs \<sigma> (Inj (NStart t)) = map_option Start (flatten_option (map_option CFGs (get_thread (\<sigma> t))))"
(*   (case \<sigma> t of OThread t' \<Rightarrow> map_option Start t' | _ \<Rightarrow> None)*)

term "node_subst"

lemma node_same_subst:
 "\<forall>x\<in> lit_fv node_fv n. \<sigma> x = \<sigma>' x \<Longrightarrow> node_subst CFGs \<sigma> n = node_subst CFGs \<sigma>' n"
apply (cases n, auto)
apply (case_tac data, auto split: object.splits)
done
abbreviation edge_type_subst where "edge_type_subst \<equiv> base_lit_subst get_edgetype"
term "edge_type_subst =  base_lit_subst get_edgetype"

lemma edge_type_same_subst: "\<forall>x\<in>base_lit_fv ety. \<sigma> x = \<sigma>' x \<Longrightarrow> edge_type_subst \<sigma> ety = edge_type_subst \<sigma>' ety"
by simp

abbreviation op_subst where "op_subst \<equiv> base_lit_subst get_op"

(*
lemma op_same_subst: "\<forall>x\<in>base_lit_fv p. \<sigma> x = \<sigma>' x \<Longrightarrow> op_subst \<sigma> p = op_subst \<sigma>' p"
by (simp)
*)

abbreviation cmp_subst where "cmp_subst \<equiv> base_lit_subst get_cmp"

lemma cmp_same_subst: "\<forall>x\<in>base_lit_fv p. \<sigma> x = \<sigma>' x \<Longrightarrow> cmp_subst \<sigma> p = cmp_subst \<sigma>' p"
by auto

lemma case_node [simp]: "(get_node v = Some n) = (v = ONode n)"
by (case_tac "v", auto)

lemma case_int [simp]: "(get_int v = Some i) = (v = OInt i)"
by (case_tac "v", auto)

lemma case_loc [simp]: "(get_memloc v = Some i) = (v = OLoc i)"
by (case_tac "v", auto)

lemma case_instr [simp]: "(get_instr v = Some i) = (v = OInstr i)"
by (case_tac "v", auto)

lemma case_expr [simp]: "(get_expr v = Some a) = (v = OExpr a)"
by (case_tac "v", auto)

(*  When do we actually use OSynFunc? Is x<e> used in any examples we have? ---ELG *)
lemma case_syn_func [simp]: "(get_synfunc v = Some (x,f)) = (v = OSynFunc x f)"
by (case_tac "v", auto)

lemma case_edge_type [simp]: "(get_edgetype v = Some e) = (v = OEdgeType e)"
by (case_tac "v", auto)

lemma case_thread [simp]: "((case v of OThread x \<Rightarrow> P x | _ \<Rightarrow> False)) = (\<exists>t. v = OThread t \<and> P t)"
by (case_tac "v", auto)

lemma get_thread_simp [simp]: "(get_thread v = Some t) = (v = OThread t)"
by (case_tac "v", auto)

lemma case_const [simp]: "(get_const v = Some c) = (v = OConst c)"
by (case_tac "v", auto)

lemma case_type [simp]: "(get_type v = Some a) = (v = OType a)"
by (case_tac "v", auto)

lemma case_op [simp]: "(get_op v = Some a) = (v = OOp a)"
by (case_tac "v", auto)

term "node_subst (G::('thread \<Rightarrow> ('node, LLVM_edge_type, 'node concrete_LLVM_instr)flowgraph option))"
abbreviation philist_subst
(*
:: "('thread \<Rightarrow> ('thread, 'node, 'mvar)flowgraph option) \<Rightarrow> 
  ('mvar \<Rightarrow> ('thread, 'node, 'mvar) object) \<Rightarrow>
  (('mvar node_const,'mvar)literal, 'mvar) gen_philist \<Rightarrow>
  ('node \<times> concrete_LLVM_expr) list option" 
*)
 where
"philist_subst \<equiv> \<lambda> (G::('thread \<Rightarrow> ('node, LLVM_edge_type, 'node concrete_LLVM_instr)flowgraph option))
 (\<sigma>::('mvar \<Rightarrow> ('thread, 'node, 'mvar) object))
 (es::'mvar gen_philist).
 foldr (\<lambda>(n, e) r.
  flatten_option (map_option
  (\<lambda> es'. flatten_option (map_option
         (\<lambda> e'. map_option
                (\<lambda> n'. (n',e') # es')
                (node_subst G \<sigma> n ))
         (expr_pattern_subst \<sigma> e)))
  r))
  (es:: 'mvar gen_philist)
  (Some [])"

term "philist_subst"
term "philist_fv"
lemma philist_same_subst [simp]:
"(\<forall>x\<in> philist_fv es. \<sigma> x = \<sigma>' x) \<Longrightarrow> philist_subst CFGs \<sigma> es = philist_subst CFGs \<sigma>' es"
apply (erule rev_mp)
apply (induct es, auto (*split del: option.splits*))
apply (cut_tac \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and e=b in expr_pattern_same_subst, simp, simp (no_asm_simp))
by (cut_tac \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and n=a and CFGs = CFGs in node_same_subst, simp, simp (no_asm_simp))

term "philist_subst"
(* Similarly, applying a valuation of metavariables to an instruction pattern yields a concrete instruction. *)
primrec instr_subst ::
"('thread \<Rightarrow> ('node, LLVM_edge_type, 'node concrete_LLVM_instr)flowgraph option) \<Rightarrow>
 ('mvar \<Rightarrow> ('thread, 'node, 'mvar) object) \<Rightarrow>
 'mvar gen_LLVM_instr \<Rightarrow>
 'node concrete_LLVM_instr option" where
"instr_subst CFGs \<sigma> (Assign x opr ty e1 e2) =
 flatten_option (map_option (\<lambda> x'. flatten_option (map_option
  (\<lambda> opr'. flatten_option (map_option (\<lambda> ty'. flatten_option (map_option
   (\<lambda> e1'. map_option (\<lambda> e2'. Assign x' opr' ty' e1' e2') (expr_pattern_subst \<sigma> e2))
   (expr_pattern_subst \<sigma> e1)))
   (LLVM_type_lit_subst \<sigma> ty)))
  (op_subst \<sigma> opr)))
  (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (Ret ty e) =
 (case (LLVM_type_lit_subst \<sigma> ty, expr_pattern_subst \<sigma> e) of (Some ty', Some e') \<Rightarrow> 
   Some (Ret ty' e') | _ \<Rightarrow> None)" |
"instr_subst CFGs \<sigma> (Br_i1 e) = map_option Br_i1 (expr_pattern_subst \<sigma> e)" |
"instr_subst CFGs \<sigma> Br_label = Some Br_label" |
"instr_subst CFGs \<sigma> (Alloca x ty) =
 flatten_option (map_option (\<lambda> x'. map_option (\<lambda> ty'. Alloca x' ty')
                                  (LLVM_type_lit_subst \<sigma> ty))
                 (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (Load x ty e) = 
 flatten_option (map_option
  (\<lambda> x'. flatten_option (map_option
  (\<lambda> ty'. map_option (\<lambda> e'. Load x' ty' e') (expr_pattern_subst \<sigma> e))
  (LLVM_type_lit_subst \<sigma> ty)))
  (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (Store ty1 e1 ty2 e2) =
 flatten_option (map_option
  (\<lambda> ty1'. flatten_option (map_option
  (\<lambda> e1'. flatten_option (map_option
  (\<lambda> ty2'. map_option (\<lambda> e2'. Store ty1' e1' ty2' e2') (expr_pattern_subst \<sigma> e2))
  (LLVM_type_lit_subst \<sigma> ty2)))
  (expr_pattern_subst \<sigma> e1)))
  (LLVM_type_lit_subst \<sigma> ty1))" |
"instr_subst CFGs \<sigma> (Cmpxchg x ty1 e1 ty2 e2 ty3 e3) =
 flatten_option (map_option
  (\<lambda> x'. flatten_option (map_option
  (\<lambda> ty1'. flatten_option (map_option
  (\<lambda> e1'. flatten_option (map_option
  (\<lambda> ty2'. flatten_option (map_option
  (\<lambda> e2'. flatten_option (map_option
  (\<lambda> ty3'. (map_option 
  (\<lambda> e3'. Cmpxchg x' ty1' e1' ty2' e2' ty3' e3')
  (expr_pattern_subst \<sigma> e3)))
  (LLVM_type_lit_subst \<sigma> ty3)))
  (expr_pattern_subst \<sigma> e2)))
  (LLVM_type_lit_subst \<sigma> ty2)))
  (expr_pattern_subst \<sigma> e1)))
  (LLVM_type_lit_subst \<sigma> ty1)))
  (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (ICmp x opr ty e1 e2) =
 flatten_option (map_option
  (\<lambda> x'. flatten_option (map_option
  (\<lambda> opr'. flatten_option (map_option
  (\<lambda> ty'. flatten_option (map_option
  (\<lambda> e1'. (map_option
  (\<lambda> e2'. ICmp x' opr' ty' e1' e2')
  (expr_pattern_subst \<sigma> e2)))
  (expr_pattern_subst \<sigma> e1)))
  (LLVM_type_lit_subst \<sigma> ty)))
  (cmp_subst \<sigma> opr)))
  (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (Phi x ty es) =
 flatten_option (map_option
  (\<lambda> x'. flatten_option (map_option
  (\<lambda> ty'. (map_option
  (\<lambda> es'. Phi x' ty' es')
  (lit_subst (philist_subst CFGs) get_philist \<sigma> es)))
  (LLVM_type_lit_subst \<sigma> ty)))
  (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (Call x ty es) = 
 flatten_option (map_option
  (\<lambda> x'. flatten_option (map_option
  (\<lambda> ty'. (map_option
  (\<lambda> es'. Call x' ty' es')
  (lit_subst eplist_subst get_eplist \<sigma> es)))
  (LLVM_type_lit_subst \<sigma> ty)))
  (get_var_name (\<sigma> x)))" |
"instr_subst CFGs \<sigma> (IsPointer e) = map_option IsPointer (expr_pattern_subst \<sigma> e)"

(*
declare [[show_types = true]]
*)

lemma instr_same_subst [simp]:
 fixes CFGs :: "'thread \<Rightarrow> ('node, LLVM_edge_type, 'node concrete_LLVM_instr)flowgraph option"
 and \<sigma> :: "'mvar \<Rightarrow> ('thread, 'node, 'mvar) object"
 and \<sigma>':: "'mvar \<Rightarrow> ('thread, 'node, 'mvar) object"
 and i :: "'mvar gen_LLVM_instr"
 assumes FV_assum:"\<forall>x\<in>instr_pattern_fv i. \<sigma> x = \<sigma>' x"
 shows "instr_subst CFGs \<sigma> i = instr_subst CFGs \<sigma>' i"
using FV_assum
proof (cases i, auto)
 fix var and opr::"(LLVM_op,'mvar)literal" and type and expr1 and expr2
 assume A1: "\<sigma> var = \<sigma>' var"
  and B1: "\<forall>x\<in>LLVM_type_lit_fv type \<union> base_lit_fv opr \<union> expr_pattern_fv expr_fv expr1 \<union> expr_pattern_fv expr_fv expr2. \<sigma> x = \<sigma>' x"
  from B1 have E1: "(op_subst \<sigma> opr = op_subst \<sigma>' opr) \<and>
                     (LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type) \<and>
                     (expr_pattern_subst \<sigma> expr1) = (expr_pattern_subst \<sigma>' expr1) \<and>
                     (expr_pattern_subst \<sigma> expr2) = (expr_pattern_subst \<sigma>' expr2)"
   by simp
   from E1 show "flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                  (map_option
                    (\<lambda>opr'. flatten_option
                              (map_option
                                (\<lambda>ty'. flatten_option
                                         (map_option (\<lambda>e1'. map_option (Assign x' opr' ty' e1')
                                          (expr_pattern_subst \<sigma> expr2)) (expr_pattern_subst \<sigma> expr1)))
                                (LLVM_type_lit_subst \<sigma> type)))
                    (op_subst \<sigma> opr)))
          (get_var_name (\<sigma>' var))) =
       flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                  (map_option
                    (\<lambda>opr'. flatten_option
                              (map_option
                                (\<lambda>ty'. flatten_option
                                         (map_option (\<lambda>e1'. map_option (Assign x' opr' ty' e1') (expr_pattern_subst \<sigma>' expr2)) (expr_pattern_subst \<sigma>' expr1)))
                                (LLVM_type_lit_subst \<sigma>' type)))
                    (op_subst \<sigma>' opr)))
          (get_var_name (\<sigma>' var)))" by simp
 next (* 15 *)
 fix type and expr and x2
 assume A2: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x "
 from A2 have E2: "(LLVM_type_lit_subst \<sigma>' type = LLVM_type_lit_subst \<sigma> type)" by simp
 assume B2: "LLVM_type_lit_subst \<sigma> type = None"
 from B2 and E2 show "LLVM_type_lit_subst \<sigma>' type = None" by simp
 next (* 14 *)
 fix type expr x2 x2a
 assume A3: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
 from A3 have E3:  "(expr_pattern_subst \<sigma> expr) = (expr_pattern_subst \<sigma>' expr)" by simp
 assume B3: "expr_pattern_subst \<sigma> expr = None" and C3: "expr_pattern_subst \<sigma>' expr = \<lfloor>x2a\<rfloor>"
 from B3 and C3 and E3 show "LLVM_type_lit_subst \<sigma>' type = None" by simp
 next (* 13 *)
 fix type and expr x2
 assume A4: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
  from A4 have E4: "(LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type)"
   by simp
 assume B4: "LLVM_type_lit_subst \<sigma> type = \<lfloor>x2\<rfloor>"
 from E4 and B4
 show "\<exists>y. LLVM_type_lit_subst \<sigma>' type = Some y"
 by (rule_tac x = "x2" in exI, clarsimp)
 next (* 12 *)
 fix type expr x2 x2a x2b
 assume A5: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x "
 from A5 have E5: "(expr_pattern_subst \<sigma> expr) = (expr_pattern_subst \<sigma>' expr)" by simp
 assume B5: "expr_pattern_subst \<sigma> expr = \<lfloor>x2a\<rfloor>" and C5: "expr_pattern_subst \<sigma>' expr = None"
 from E5 and B5 and C5
 show "False" by simp
 next (* 11 *)
 fix type expr x2 x2a x2b x2c
 assume A6: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
 from A6 have E6: "(LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type)" by simp
 assume B6: "LLVM_type_lit_subst \<sigma> type = \<lfloor>x2\<rfloor>" and C6: "LLVM_type_lit_subst \<sigma>' type = \<lfloor>x2b\<rfloor>"
 from E6 and B6 and C6
 show "x2 = x2b" by simp
 next (* 10 *)
 fix type expr x2 x2a x2b x2c
 assume A7: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
 from A7 have E7: "(expr_pattern_subst \<sigma> expr) = (expr_pattern_subst \<sigma>' expr)" by simp
 assume B7: "expr_pattern_subst \<sigma> expr = \<lfloor>x2a\<rfloor>" and C7: "expr_pattern_subst \<sigma>' expr = \<lfloor>x2c\<rfloor>"
 from E7 and B7 and C7 
 show "x2a = x2c" by simp
 next (* 9 *)
 fix expr
 assume A8: "\<forall>x\<in>expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
 from A8 have E8: "(expr_pattern_subst \<sigma> expr) = (expr_pattern_subst \<sigma>' expr)" by simp
 from E8
 show "map_option Br_i1 (expr_pattern_subst \<sigma> expr) = map_option Br_i1 (expr_pattern_subst \<sigma>' expr)"
 by simp
 next (* 8 *)
 fix var type
 assume A9: "\<sigma> var = \<sigma>' var" and B9: "\<forall>x\<in>LLVM_type_lit_fv type. \<sigma> x = \<sigma>' x"
 from A9 and B9 have E9: "(LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type)" by simp
 from E9
 show "flatten_option (map_option (\<lambda>x'. map_option (Alloca x') (LLVM_type_lit_subst \<sigma> type)) (get_var_name (\<sigma>' var))) =
       flatten_option (map_option (\<lambda>x'. map_option (Alloca x') (LLVM_type_lit_subst \<sigma>' type)) (get_var_name (\<sigma>' var)))"
 by simp
 next (* 7 *)
 fix var type expr
 assume A10: "\<sigma> var = \<sigma>' var"
   and B10: "\<forall>x\<in>LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
 from A10 and B10
 have E10: "(LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type) \<and>
            (expr_pattern_subst \<sigma> expr) = (expr_pattern_subst \<sigma>' expr)" by simp
 from E10
 show "flatten_option
        (map_option (\<lambda>x'. flatten_option (map_option (\<lambda>ty'. map_option (Load x' ty') (expr_pattern_subst \<sigma> expr)) (LLVM_type_lit_subst \<sigma> type)))
          (get_var_name (\<sigma>' var))) =
       flatten_option
        (map_option (\<lambda>x'. flatten_option (map_option (\<lambda>ty'. map_option (Load x' ty') (expr_pattern_subst \<sigma>' expr)) (LLVM_type_lit_subst \<sigma>' type)))
          (get_var_name (\<sigma>' var)))" by simp
 next (* 6 *)
 fix type1 expr1 type2 expr2
 assume A11: "\<forall>x\<in>LLVM_type_lit_fv type1 \<union> expr_pattern_fv expr_fv expr1 \<union> LLVM_type_lit_fv type2 \<union> expr_pattern_fv expr_fv expr2. \<sigma> x = \<sigma>' x "
 from A11 have E11: "(LLVM_type_lit_subst \<sigma> type1 = LLVM_type_lit_subst \<sigma>' type1) \<and>
                     (expr_pattern_subst \<sigma> expr1) = (expr_pattern_subst \<sigma>' expr1) \<and>
                     (LLVM_type_lit_subst \<sigma> type2 = LLVM_type_lit_subst \<sigma>' type2) \<and>
                     (expr_pattern_subst \<sigma> expr2) = (expr_pattern_subst \<sigma>' expr2)" by simp
 from E11
 show "flatten_option
        (map_option
          (\<lambda>ty1'. flatten_option
                    (map_option (\<lambda>e1'. flatten_option (map_option (\<lambda>ty2'. map_option (Store ty1' e1' ty2') (expr_pattern_subst \<sigma> expr2)) (LLVM_type_lit_subst \<sigma> type2)))
                      (expr_pattern_subst \<sigma> expr1)))
          (LLVM_type_lit_subst \<sigma> type1)) =
       flatten_option
        (map_option
          (\<lambda>ty1'. flatten_option
                    (map_option
                      (\<lambda>e1'. flatten_option (map_option (\<lambda>ty2'. map_option (Store ty1' e1' ty2') (expr_pattern_subst \<sigma>' expr2)) (LLVM_type_lit_subst \<sigma>' type2)))
                      (expr_pattern_subst \<sigma>' expr1)))
          (LLVM_type_lit_subst \<sigma>' type1))" by simp
 next (* 5 *)
 fix var type1 expr1 type2 expr2 type3 expr3
 assume A12: "\<sigma> var = \<sigma>' var"
   and B12: "\<forall>x\<in>LLVM_type_lit_fv type1 \<union> expr_pattern_fv expr_fv expr1 \<union> LLVM_type_lit_fv type2 \<union> expr_pattern_fv expr_fv expr2 \<union> LLVM_type_lit_fv type3 \<union>
           expr_pattern_fv expr_fv expr3. \<sigma> x = \<sigma>' x"
 from A12 and B12 have E12: "(LLVM_type_lit_subst \<sigma> type1 = LLVM_type_lit_subst \<sigma>' type1) \<and>
                     (expr_pattern_subst \<sigma> expr1) = (expr_pattern_subst \<sigma>' expr1) \<and>
                     (LLVM_type_lit_subst \<sigma> type2 = LLVM_type_lit_subst \<sigma>' type2) \<and>
                     (expr_pattern_subst \<sigma> expr2) = (expr_pattern_subst \<sigma>' expr2) \<and>
                     (LLVM_type_lit_subst \<sigma> type3 = LLVM_type_lit_subst \<sigma>' type3) \<and>
                     (expr_pattern_subst \<sigma> expr3) = (expr_pattern_subst \<sigma>' expr3)" by simp
 from E12 show "flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                  (map_option
                    (\<lambda>ty1'. flatten_option
                              (map_option
                                (\<lambda>e1'. flatten_option
                                         (map_option
                                           (\<lambda>ty2'. flatten_option
                                                     (map_option
                                                       (\<lambda>e2'. flatten_option
                                                                (map_option (\<lambda>ty3'. map_option (Cmpxchg x' ty1' e1' ty2' e2' ty3') (expr_pattern_subst \<sigma> expr3))
                                                                  (LLVM_type_lit_subst \<sigma> type3)))
                                                       (expr_pattern_subst \<sigma> expr2)))
                                           (LLVM_type_lit_subst \<sigma> type2)))
                                (expr_pattern_subst \<sigma> expr1)))
                    (LLVM_type_lit_subst \<sigma> type1)))
          (get_var_name (\<sigma>' var))) =
       flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                  (map_option
                    (\<lambda>ty1'. flatten_option
                              (map_option
                                (\<lambda>e1'. flatten_option
                                         (map_option
                                           (\<lambda>ty2'. flatten_option
                                                     (map_option
                                                       (\<lambda>e2'. flatten_option
                                                                (map_option (\<lambda>ty3'. map_option (Cmpxchg x' ty1' e1' ty2' e2' ty3') (expr_pattern_subst \<sigma>' expr3))
                                                                  (LLVM_type_lit_subst \<sigma>' type3)))
                                                       (expr_pattern_subst \<sigma>' expr2)))
                                           (LLVM_type_lit_subst \<sigma>' type2)))
                                (expr_pattern_subst \<sigma>' expr1)))
                    (LLVM_type_lit_subst \<sigma>' type1)))
          (get_var_name (\<sigma>' var)))" by simp
 next (* 4 *)
 fix var and cmp :: "(LLVM_cmp,'mvar)literal" and type and expr1 and expr2
 assume A13: "\<sigma> var = \<sigma>' var"
  and B13: "\<forall>x\<in>base_lit_fv cmp \<union> LLVM_type_lit_fv type \<union> expr_pattern_fv expr_fv expr1 \<union> expr_pattern_fv expr_fv expr2. \<sigma> x = \<sigma>' x"
 from A13 and B13 
 have E13: "(cmp_subst \<sigma> cmp = cmp_subst \<sigma>' cmp) \<and>
                     (LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type) \<and>
                     (expr_pattern_subst \<sigma> expr1) = (expr_pattern_subst \<sigma>' expr1) \<and>
                     (expr_pattern_subst \<sigma> expr2) = (expr_pattern_subst \<sigma>' expr2)"
   by simp
 from E13
 show "flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                  (map_option
                    (\<lambda>opr'. flatten_option
                              (map_option
                                (\<lambda>ty'. flatten_option (map_option (\<lambda>e1'. map_option (ICmp x' opr' ty' e1') (expr_pattern_subst \<sigma> expr2)) (expr_pattern_subst \<sigma> expr1)))
                                (LLVM_type_lit_subst \<sigma> type)))
                    (cmp_subst \<sigma> cmp)))
          (get_var_name (\<sigma>' var))) =
       flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                  (map_option
                    (\<lambda>opr'. flatten_option
                              (map_option
                                (\<lambda>ty'. flatten_option
                                         (map_option (\<lambda>e1'. map_option (ICmp x' opr' ty' e1') (expr_pattern_subst \<sigma>' expr2)) (expr_pattern_subst \<sigma>' expr1)))
                                (LLVM_type_lit_subst \<sigma>' type)))
                    (cmp_subst \<sigma>' cmp)))
          (get_var_name (\<sigma>' var)))" by simp
 next (* 3 *)
 fix var type phi_list
 assume A14: "\<sigma> var = \<sigma>' var"
  and B14: "\<forall>x\<in>LLVM_type_lit_fv type \<union> lit_fv philist_fv phi_list. \<sigma> x = \<sigma>' x"
 from A14 and B14
 have E14: "(lit_subst (philist_subst CFGs) get_philist \<sigma> phi_list = lit_subst(philist_subst CFGs) get_philist \<sigma>' phi_list) \<and>
            (LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type)"
 proof auto
 show "lit_subst (philist_subst CFGs) get_philist \<sigma> phi_list = lit_subst (philist_subst CFGs) get_philist \<sigma>' phi_list"
thm lit_same_subst
  proof (rule_tac data_fv = "philist_fv" and data_subst = "philist_subst CFGs"  and get_data = get_philist in lit_same_subst)
   show "\<forall>x. (\<forall>v\<in>philist_fv x. \<sigma> v = \<sigma>' v) \<longrightarrow> philist_subst CFGs \<sigma> x = philist_subst CFGs \<sigma>' x"
   by auto
  next
  from B14
  show "\<forall>v\<in>lit_fv philist_fv phi_list. \<sigma> v = \<sigma>' v" by auto
  qed
 qed
 from E14
 show "flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                 (map_option
                   (\<lambda>ty'. map_option (Phi x' ty')
                           (lit_subst (philist_subst CFGs) get_philist \<sigma>
                             phi_list))
                   (LLVM_type_lit_subst \<sigma> type)))
          (get_var_name (\<sigma>' var))) =
       flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                 (map_option
                   (\<lambda>ty'. map_option (Phi x' ty')
                           (lit_subst (philist_subst CFGs) get_philist \<sigma>'
                             phi_list))
                   (LLVM_type_lit_subst \<sigma>' type)))
          (get_var_name (\<sigma>' var)))"
 by simp
 next (* 2 *)
 fix var type args
 assume A15: "\<sigma> var = \<sigma>' var"
  and B15: "\<forall>x\<in>LLVM_type_lit_fv type \<union> lit_fv eplist_fv args. \<sigma> x = \<sigma>' x "
 from A15 and B15
 have E15: "((lit_subst eplist_subst get_eplist \<sigma> args) = (lit_subst eplist_subst get_eplist \<sigma>' args)) \<and>
            (LLVM_type_lit_subst \<sigma> type = LLVM_type_lit_subst \<sigma>' type)"
 proof auto
  show "lit_subst eplist_subst get_eplist \<sigma> args = lit_subst eplist_subst get_eplist \<sigma>' args"
  proof (rule_tac data_fv = "eplist_fv" and data_subst = "eplist_subst"  and get_data = get_eplist in lit_same_subst)
   show "\<forall>x. (\<forall>v\<in>eplist_fv x. \<sigma> v = \<sigma>' v) \<longrightarrow> eplist_subst \<sigma> x = eplist_subst \<sigma>' x" 
   by (rule eplist_same_subst)
   next
   from B15
   show " \<forall>v\<in>lit_fv eplist_fv args. \<sigma> v = \<sigma>' v" by auto
  qed
 qed
 from E15
 show "flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                 (map_option (\<lambda>ty'. map_option (Call x' ty') (lit_subst eplist_subst get_eplist \<sigma> args)) (LLVM_type_lit_subst \<sigma> type)))
          (get_var_name (\<sigma>' var))) =
       flatten_option
        (map_option
          (\<lambda>x'. flatten_option
                 (map_option (\<lambda>ty'. map_option (Call x' ty') (lit_subst eplist_subst get_eplist \<sigma>' args)) (LLVM_type_lit_subst \<sigma>' type)))
          (get_var_name (\<sigma>' var)))"
 by simp
 next (* 1 *)
 fix expr
 assume A16: "\<forall>x\<in>expr_pattern_fv expr_fv expr. \<sigma> x = \<sigma>' x"
 from A16
 have E16: "(expr_pattern_subst \<sigma> expr = expr_pattern_subst \<sigma>' expr)" by simp
 from E16
 show "map_option IsPointer (expr_pattern_subst \<sigma> expr) = map_option IsPointer (expr_pattern_subst \<sigma>' expr)"
 by simp
qed


primrec subst where
"subst CFGs \<sigma> (Inj i) = instr_subst CFGs \<sigma> i" |
"subst CFGs \<sigma> (MVar x) = get_instr (\<sigma> x)"

term "subst"

term "pattern_fv"
term "instr_subst G \<sigma>"
lemma pattern_same_subst:
fixes CFGs and \<sigma> and \<sigma>'
shows  "\<forall>x\<in>pattern_fv p. \<sigma> x = \<sigma>' x \<Longrightarrow> subst CFGs \<sigma> p = subst CFGs \<sigma>' p"
by (cases p, auto)

end
