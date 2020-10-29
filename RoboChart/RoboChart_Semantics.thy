section \<open> RoboChart Static Semantics \<close>

theory RoboChart_Semantics
  imports RoboChart_Validation RoboChart_Parser RoboChart_StateMachine "Optics.Optics"
  keywords "interface" "func" "robotic_platform" "stm" :: "thy_decl_block"
begin

text \<open> Finally, we turn the validated AST representations into semantics. This often requires
  the production of terms, which can also be represented in HOL and then code generated. \<close>

definition "fun_spec P Q = (\<lambda> x. if (P x) then (THE y. Q x y) else undefined)"

definition "rel_spec P Q = {(x, y). P x \<and> Q x y}"

definition add_free_types :: "(ID \<times> typ) list \<Rightarrow> term \<Rightarrow> term" where
"add_free_types ps x = subst_free (map (\<lambda> (n, t). (Free n dummyT, Free n t)) ps) x"

fun func_body :: "Function \<Rightarrow> term" where
"func_body (Func n ps t P Q) = 
  (let res = STR ''result'';
       Pt = constraint boolT (add_free_types ps P); 
       Qt = constraint boolT (add_free_types ((res, t) # ps) Q); 
       p = mk_tuple (map (\<lambda> (i, t). Free i t) ps)
   in mk_equals (free n) (const @{const_name fun_spec} 
      $ (tupled_lambda p Pt) 
      $ (tupled_lambda p (tupled_lambda (Free (res) t) Qt))))"

code_reflect RC_Semantics
  functions add_free_types func_body

ML \<open>

structure RC_Compiler =
struct

open RC_AST;
open RC_Validation;
open RC_Semantics;

type interface = unit RC_AST.interface_ext RC_AST.named_ext;
type roboticPlatform = unit RC_AST.container_ext RC_AST.interface_ext RC_AST.named_ext;
type stateMachineDef = unit stateMachineDef_ext RC_AST.container_ext RC_AST.interface_ext RC_AST.named_ext

structure RCInterfaces = Theory_Data
  (type T = interface Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

structure RCPlatforms = Theory_Data
  (type T = roboticPlatform Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

(* Semantic processors *)

type RCSem_Proc = 
  { itf_sem: interface -> theory -> theory
  , rpl_sem: roboticPlatform -> theory -> theory
  , stm_sem: stateMachineDef -> theory -> theory
  }

val null_RCSem_Proc = 
  { itf_sem = K I, rpl_sem = K I, stm_sem = K I }

structure Stm_Sem = Theory_Data
  (type T = RCSem_Proc
   val empty = null_RCSem_Proc
   val extend = I
   val merge = fn (_, x) => x);

fun compileFuncDecl ctx (FuncDecl (n, ps, t, P, Q)) =
  let open Syntax in
    Func (n, map (fn (p, t) => (p, read_typ ctx t)) ps, read_typ ctx t, parse_term ctx P, parse_term ctx Q)
  end;

fun compileFunction x thy = 
  let open Syntax
      val ctx = (Named_Target.theory_init thy)
      val f = check_term ctx (func_body (compileFuncDecl ctx x))
  in Local_Theory.exit_global (snd (Specification.definition NONE [] [] ((Binding.empty, []), f) ctx))

  end;

exception ROBOCHART_INVALID;

fun compileInterface itf thy = 
  if (validate_Interface itf) 
  then Dataspace.dataspace_cmd (ident itf) [] (map decl_of (constants itf)) [] (map decl_of (variables itf)) (map decl_of (events itf)) 
        ((*RCInterfaces.map (Symtab.update (ident itf, itf))*) thy)
  else raise ROBOCHART_INVALID;
 
val machineN = "machine";

(* Create a local context with variables and events, and generate a semantic state machine *)

fun context_Stm_Semantics smd thy = 
  let open Syntax; open Logic; open RC_Stm; open Specification
      val ctx = (Named_Target.init (Context.theory_name thy ^ "." ^ ident smd) (compileInterface smd thy))
      (* State definitions *)
      val seqs = map (check_term ctx o compile_Node_defn ctx) (nodes smd)
      val teqs = map (check_term ctx o compile_Transition_defn ctx) (transitions smd)
      val smeq = check_term ctx (mk_equals (free machineN, RC_Stm.compile_StateMachineDef ctx smd))
  in Local_Theory.exit_global 
      ((  fold (fn seq => snd o definition NONE [] [] ((Binding.empty, []), seq)) seqs
       #> fold (fn teq => snd o definition NONE [] [] ((Binding.empty, []), teq)) teqs
       #> snd o definition NONE [] [] ((Binding.empty, []), smeq)
       ) ctx)
  end;

val ctx_semantics: RCSem_Proc = 
  { itf_sem = K I, rpl_sem = K I, stm_sem = context_Stm_Semantics }

fun compileStateMachine (n, defs) thy =
  let val smd = RC_AST.mk_StateMachineDef (n, defs)
  in 
    if (validate_StateMachine smd)
    (* Get the current semantic processor *)
    then #stm_sem (Stm_Sem.get thy) smd thy
    else raise ROBOCHART_INVALID
  end;

end

val _ =
  Outer_Syntax.command @{command_keyword func} "define RoboChart functions" 
    (RC_Parser.functionParser >> (Toplevel.theory o RC_Compiler.compileFunction));

val _ =
  Outer_Syntax.command @{command_keyword interface} "define RoboChart interfaces" 
    (RC_Parser.interfaceParser >> (Toplevel.theory o RC_Compiler.compileInterface));

val _ =
  Outer_Syntax.command @{command_keyword robotic_platform} "define RoboChart robotic platforms" 
    (RC_Parser.roboticPlatformParser >> (Toplevel.theory o K I));

val _ =
  Outer_Syntax.command @{command_keyword stm} "define RoboChart state machines"
    (RC_Parser.stateMachineDefParser >> (Toplevel.theory o RC_Compiler.compileStateMachine));
\<close>

text \<open> Set the default semantic processor \<close>

setup \<open>
  RC_Compiler.Stm_Sem.put (RC_Compiler.ctx_semantics)
\<close>

end