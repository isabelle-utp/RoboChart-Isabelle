section \<open> RoboChart Static Semantics \<close>

theory RoboChart_Semantics
  imports RoboChart_Validation RoboChart_Parser
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
  (let Pt = constraint boolT (add_free_types ps P); 
       Qt = constraint boolT (add_free_types ((STR ''result'', t) # ps) Q); 
       p = mk_tuple (map (\<lambda> (i, t). Free i t) ps)
   in mk_equals (free n) (const (STR ''RoboChart_Semantics.fun_spec'') 
      $ (tupled_lambda p Pt) 
      $ (tupled_lambda p (tupled_lambda (Free (STR ''result'') t) Qt))))"

code_reflect RC_Semantics
  functions add_free_types func_body

ML \<open>

structure RC_Compiler =
struct

open HOLogic;
open Syntax;
open RC_AST;
open RC_Validation;
open RC_Semantics;

type interface = unit interface_ext named_ext;
type roboticPlatform = unit container_ext interface_ext named_ext;

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

fun compileDummy _ thy = thy;

fun compileFunction x thy = 
  let val ctx = (Named_Target.theory_init thy)
      val f = check_term ctx (func_body x)
  in Local_Theory.exit_global (snd (Specification.definition NONE [] [] ((Binding.empty, []), f) ctx))

  end;

exception ROBOCHART_INVALID;

fun compileInterface itf thy = 
  if (validate_Interface itf) 
  then RCInterfaces.map (Symtab.update (ident itf, itf)) thy
  else raise ROBOCHART_INVALID;

end

val _ =
  Outer_Syntax.command @{command_keyword func} "define RoboChart functions" 
    (RC_Parser.functionParser @{context} >> (Toplevel.theory o RC_Compiler.compileFunction));

val _ =
  Outer_Syntax.command @{command_keyword interface} "define RoboChart interfaces" 
    (RC_Parser.interfaceParser @{context} >> (Toplevel.theory o RC_Compiler.compileInterface));

val _ =
  Outer_Syntax.command @{command_keyword robotic_platform} "define RoboChart robotic platforms" 
    (RC_Parser.roboticPlatformParser @{context} >> (Toplevel.theory o K I));

val _ =
  Outer_Syntax.command @{command_keyword stm} "define RoboChart state machines" 
    (RC_Parser.stateMachineDefParser @{context} >> (Toplevel.theory o K I));

\<close>


end