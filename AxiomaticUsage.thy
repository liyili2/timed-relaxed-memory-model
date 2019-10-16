theory AxiomaticUsage
imports Main AxiomaticModel
begin

locale axiomaticUsage = axiomaticModel
begin

(* floating point type *)
datatype LLVM_FP_type = Half | Float | Double (*| Fp128 | X86_fp80 *)| Ppc_fp128

datatype atomicAttr = Atomic | NonAtomic

(*
datatype 'ty LLVM_vector = Vector "nat*'ty"
datatype 'ty maybe_vector = Plain 'ty | Vect "'ty LLVM_vector"
*)

type_synonym int_ty = nat

(* General utility type for defining syntax with variables. *)
datatype ('data, 'mvar) literal = Inj 'data | MVar 'mvar

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

fun flatten_option where
  "flatten_option (Some (Some x)) = Some x"
| "flatten_option _ = None"

(* General utility type for defining syntax with variables. *)

primrec lit_fv where
"lit_fv fv (Inj data) = fv data" |
"lit_fv _ (MVar mv) = {mv}"

lemma union_list_finite [simp]:
fixes f l 
assumes A: "\<forall> x. finite (f x)"
shows "finite (\<Union>x\<in>set l. f x)"
using A
by (induct l, auto)

lemma lit_fv_finite [simp]: fixes fv assumes A: "\<forall> t. finite (fv t)" shows "finite (lit_fv fv l)"
using A
by (case_tac l, auto)

abbreviation "base_lit_fv t \<equiv> lit_fv (\<lambda>x. {}) t"

lemma finite_base_lit_fv [simp]: "finite (base_lit_fv t)"
by (case_tac t, auto)

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

(* Expression pattern e<e'> matches "an expression e with e' somewhere in it",
   allowing basic pattern-matching within a transformation. *)
datatype ('expr, 'mvar) expr_pattern 
=
       EPInj "'expr"
     | EPMVar "'mvar"
     | EPSubst 'mvar "'expr" ("_<_>" 102)

(* Collecting free variables. *)

primrec expr_pattern_fv where
"expr_pattern_fv expr_fv (EPInj e) = expr_fv e" |
"expr_pattern_fv expr_fv (x<e>) = insert x (expr_fv e)" |
"expr_pattern_fv expr_fv (EPMVar x) = {x}"

lemma expr_pattern_fv_finite [simp]:
fixes "expr_fv"and "ep" assumes A: "\<forall> e. finite (expr_fv e)" shows "finite (expr_pattern_fv expr_fv ep)"
using A
by (induct_tac "ep", auto)

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

(* Basic syntax bits: node and edge literals. *)
(* Note that these arguments are thread patterns (mvars), not concrete threads. *)
datatype 'mvar node_const = NStart 'mvar  | NExit 'mvar

type_synonym 'mvar node_lit = "('mvar node_const, 'mvar) literal"

(*
type_synonym 'thread gen_node = "(('thread, string) literal) node_const"

term "(x::('thread gen_node, string) literal)"
*)

type_synonym 'node concrete_philist = "('node \<times> concrete_LLVM_expr) list"
type_synonym 'mvar gen_philist = "(('mvar node_const,'mvar)literal  \<times> ('mvar LLVM_expr_pat))list"

fun node_fv where
"node_fv (NStart t) = {t}" |
"node_fv (NExit t) = {t}"

lemma node_fv_finite [simp]: shows "finite (node_fv n)" 
  by (case_tac n, auto)

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


end

end