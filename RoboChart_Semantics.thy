section \<open> RoboChart Static Semantics \<close>

theory RoboChart_Semantics
  imports RoboChart_Validation RoboChart_Parser RoboChart_StateMachine 
    RoboChart_Semantic_Processors "Z_Toolkit.Z_Toolkit" "Optics.Optics"
  keywords 
    "interface" "func" "robotic_platform" "stm" 
    "operation" "controller" "module" :: "thy_decl_block"
begin

text \<open> Finally, we turn the validated AST representations into semantics. This often requires
  the production of terms, which can also be represented in HOL and then code generated. \<close>

text \<open> We can encode functions in different ways. For now, we chose to encode them as partial functions. \<close>

definition "fun_spec P Q = (\<lambda> x. if (P x) then (THE y. Q x y) else undefined)"

definition pfun_spec :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Zpfun> 'b" where
"pfun_spec P Q = (\<lambda> x | P x \<and> (\<exists> y. Q x y) \<bullet> SOME y. Q x y)"

lemma pfun_spec_app_eqI [intro]: "\<lbrakk> P x; \<And> y. Q x y \<longleftrightarrow> y = f x \<rbrakk> \<Longrightarrow> (pfun_spec P Q)(x)\<^sub>p = f x"
  by (simp add: pfun_spec_def, subst pabs_apply, auto)

definition "rel_spec P Q = {(x, y). P x \<and> Q x y}"

definition add_free_types :: "(ID \<times> typ) list \<Rightarrow> term \<Rightarrow> term" where
"add_free_types ps x = subst_free (map (\<lambda> (n, t). (Free n dummyT, Free n t)) ps) x"

fun func_body :: "Function \<Rightarrow> term" where
"func_body (Func n ps t P Q) = 
  (let res = STR ''result'';
       Pt = constraint boolT (add_free_types ps P); 
       Qt = constraint boolT (add_free_types ((res, t) # ps) Q); 
       p = mk_tuple (map (\<lambda> (i, t). Free i t) ps)
   in mk_equals (free n) (const @{const_name pfun_spec} 
      $ (tupled_lambda p Pt) 
      $ (tupled_lambda p (tupled_lambda (Free (res) t) Qt))))"

code_reflect RC_Semantics
  functions add_free_types func_body

ML \<open> RC_SemProc.RCSem_Proc_ext \<close>

ML \<open>

structure RC_Compiler =
struct

open RC_AST;
open RC_Validation;
open RC_Semantics;
open RC_SemProc;

type RCSem_Proc = unit rCSem_Proc_ext;

structure Stm_Sem = Theory_Data
  (type T = RCSem_Proc
   val empty = null_RCSem_Proc
   val extend = I
   val merge = fn (_, x) => x);

fun compileFuncDecl ctx (FuncDecl (n, ps, t, P, Q)) =
  let open Syntax; open HOLogic in
    Func (n, map (fn (p, t) => (p, read_typ ctx t)) ps, read_typ ctx t, Library.foldr mk_conj (map (parse_term ctx) P, @{term True}), Library.foldr mk_conj (map (parse_term ctx) Q, @{term True}))
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
  then Dataspace.dataspace_cmd 
        (ident itf) [] 
        (map decl_of (constants itf)) [] 
        (map decl_of (variables itf)) 
        (map decl_of (events itf)) 
        ((*RCInterfaces.map (Symtab.update (ident itf, itf))*) thy)
  else raise ROBOCHART_INVALID;

fun compileContainer cnt thy = 
  if (validate_Interface cnt) (* FIXME: Proper container validation *)
  then Dataspace.dataspace_cmd 
        (ident cnt) (uses cnt) 
        (map decl_of (constants cnt)) [] 
        (map decl_of (variables cnt)) 
        (map decl_of (events cnt)) 
        ((*RCInterfaces.map (Symtab.update (ident itf, itf))*) thy)
  else raise ROBOCHART_INVALID;

val machineN = "machine";

(* Create a local context with variables and events, and generate a semantic state machine *)

fun stransitionT predT actT probT = Type (@{type_name STransition}, [predT, actT, probT])

val sm_defs = (Binding.empty, [Token.make_src (@{named_theorems sm_defs}, Position.none) []])

fun prove_simplify ctx thms goal = 
  Goal.prove ctx [] []
      (hd (Type_Infer_Context.infer_types ctx [ goal ]))
      (fn {context = context, prems = _} =>
          EVERY [ PARALLEL_ALLGOALS 
                    (asm_simp_tac 
                      (fold Simplifier.add_simp 
                        (thms @ [@{thm Pure.reflexive}] ) 
                  context)) ]);

fun context_Stm_Semantics cont smd thy = 
  let open Syntax; open Logic; open RC_Stm; open Specification
      val ctx = (Named_Target.init [] (Context.theory_name thy ^ "." ^ ident smd) 
                  (compileContainer smd thy))
      val rsp = Stm_Sem.get thy
      val predT = predT (rctypes rsp) Lens_Lib.astateT
      val actionT = actionT (rctypes rsp) Lens_Lib.astateT Dataspace.achanT
      val probT = probT (rctypes rsp) Lens_Lib.astateT
      (* State definitions *)
      val seqs = map (compile_Node_defn ctx (rctypes rsp) predT actionT probT) (nodes smd)
      val tdefs = map (compile_Transition ctx (rctypes rsp) predT actionT probT) (transitions smd)
      fun tr_thms ctx = 
        map 
            (prove_simplify ctx (Proof_Context.get_thms ctx @{named_theorems sm_defs}) o check_term ctx)
            (List.concat (map snd tdefs))
      fun nd_thms ctx = 
        map 
            (prove_simplify ctx (Proof_Context.get_thms ctx @{named_theorems sm_defs}) o check_term ctx)
            (List.concat (map snd seqs))
      val smdef = RC_Stm.compile_StateMachineDef ctx predT actionT probT smd
      fun sm_thms ctx = 
        map 
            (prove_simplify ctx (Proof_Context.get_thms ctx @{named_theorems sm_defs}) o check_term ctx)
            (snd smdef)
      val simp = Attrib.check_src ctx (Token.make_src ("simp", Position.none) [])
  in Local_Theory.exit_global 
      ((  fold (fn (seq, _) => snd o definition NONE [] [] (sm_defs, seq)) seqs
       #> fold (fn (teq, _) => snd o definition NONE [] [] (sm_defs, check_term ctx teq)) tdefs
       #> snd o definition NONE [] [] (sm_defs, fst smdef)
       #> (fn ctx => Local_Theory.note ((Binding.name "transitions", [simp]), (tr_thms ctx)) ctx |> snd)
       #> (fn ctx => Local_Theory.note ((Binding.name "nodes", [simp]), (nd_thms ctx)) ctx |> snd)
       #> (fn ctx => Local_Theory.note ((Binding.name "machine", [simp]), (sm_thms ctx)) ctx |> snd)
       #> cont
       ) ctx)
  end;

fun ctx_semantics rsp cont =
  rctypes_update (K rsp) null_RCSem_Proc 
  |> stm_sem_update (K (context_Stm_Semantics cont));

fun compileStateMachine (n, defs) thy =
  let val smd = RC_AST.mk_StateMachineDef (n, defs)
  in 
    if (validate_StateMachine smd)
    (* Get the current semantic processor *)
    then stm_sem (Stm_Sem.get thy) smd thy
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
  Outer_Syntax.command @{command_keyword controller} "define RoboChart controllers" 
    (RC_Parser.controllerParser >> (Toplevel.theory o K I));

val _ =
  Outer_Syntax.command @{command_keyword robotic_platform} "define RoboChart robotic platforms" 
    (RC_Parser.roboticPlatformParser >> (Toplevel.theory o K I));

val _ =
  Outer_Syntax.command @{command_keyword module} "define RoboChart modules" 
    (RC_Parser.moduleParser >> (Toplevel.theory o K I));

val _ =
  Outer_Syntax.command @{command_keyword stm} "define RoboChart state machines"
    (RC_Parser.stateMachineDefParser >> (Toplevel.theory o RC_Compiler.compileStateMachine));

val _ =
  Outer_Syntax.command @{command_keyword operation} "define RoboChart operations"
    (RC_Parser.operationParser >> (Toplevel.theory o K I));
\<close>

text \<open> Set the default semantic processor \<close>

setup \<open>
  let open RC_Compiler; open RC_SemProc in
  Stm_Sem.put (ctx_semantics null_RCTypes I)
  end
\<close>

end