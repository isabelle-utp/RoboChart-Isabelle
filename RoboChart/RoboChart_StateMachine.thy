section \<open> Semantics of State Machines \<close>

theory RoboChart_StateMachine
  imports "RoboChart_AST"
begin

text \<open> The following types represent state machines that have been supplied with typed contextual
  information. Predicates, actions, and expressions have all been enriched with type data, which
  is carried using the type parameters. \<close>

datatype ('pred, 'act, 'prob) STransition = 
  STransition (tn_source: ID) (tn_target: ID) (tn_trigger: "'act option")
              (tn_probability: "'prob option") (tn_condition: "'pred option") (tn_action: "'act option")

datatype ('pred, 'act, 'prob) SNode =
  SNode (n_name: ID) (n_entry: "'act option") (n_during: "'act option") (n_exit: "'act option") 
        (n_nodes: "('pred, 'act, 'prob) SNode list") (n_transitions: "('pred, 'act, 'prob) STransition list")

datatype ('pred, 'act, 'prob) SStateMachine =
  SStateMachine (sm_initial: "ID") (sm_finals: "ID list")
                (sm_nodes: "('pred, 'act, 'prob) SNode list")
                (sm_transitions: "('pred, 'act, 'prob) STransition list")

(*
notation sm_initial ("init\<index>")
notation sm_finals ("finals\<index>")
notation sm_nodes ("nodes\<index>")
notation sm_transitions ("\<^bold>T\<index>")
*)

definition "mk_None = const @{const_name None}"
definition "mk_Some t = const @{const_name Some} $ t"
fun mk_option :: "term option \<Rightarrow> term" where
"mk_option (Some t) = mk_Some t" | "mk_option None = mk_None"

abbreviation "read_opt_term ctx u \<equiv> mk_option (map_option (read_term ctx) u)"

definition compile_Transition :: "Proof.context \<Rightarrow> Transition \<Rightarrow> term" where
"compile_Transition ctx t = 
  const @{const_name STransition} 
  $ mk_literal (from t)
  $ mk_literal (to t)
  $ read_opt_term ctx (trigger t)
  $ read_opt_term ctx (probability t)
  $ read_opt_term ctx (condition t)
  $ read_opt_term ctx (action t)"

definition "basic_Node n = SNode n None None None [] []"

definition get_Entry :: "Action list \<Rightarrow> uterm option" where
"get_Entry acts = map_option act (find is_Entry acts)"

definition get_During :: "Action list \<Rightarrow> uterm option" where
"get_During acts = map_option act (find is_During acts)"

definition get_Exit :: "Action list \<Rightarrow> uterm option" where
"get_Exit acts = map_option act (find is_Exit acts)"

fun compile_Node :: "Proof.context \<Rightarrow> Node \<Rightarrow> term" where
"compile_Node ctx (Initial n) = 
  const @{const_name basic_Node} $ mk_literal n" |
"compile_Node ctx (Final n) =
  const @{const_name basic_Node} $ mk_literal n" |
"compile_Node ctx (Junction n) =
  const @{const_name basic_Node} $ mk_literal n" |
"compile_Node ctx (ProbabilisticJunction n) =
  const @{const_name basic_Node} $ mk_literal n" |
"compile_Node ctx (State n ns ts acts) = 
  const @{const_name SNode}
  $ mk_literal n
  $ read_opt_term ctx (get_Entry acts)
  $ read_opt_term ctx (get_During acts)
  $ read_opt_term ctx (get_Exit acts)
  $ mk_list dummyT (map (compile_Node ctx) ns)
  $ mk_list dummyT (map (compile_Transition ctx) ts)"

definition get_Initial :: "Node list \<Rightarrow> ID" where
"get_Initial ns = sname (the (find is_Initial ns))"

definition get_Finals :: "Node list \<Rightarrow> ID list" where
"get_Finals ns = map sname (filter is_Final ns)"

definition compile_StateMachineDef :: "Proof.context \<Rightarrow> StateMachineDef \<Rightarrow> term" where
"compile_StateMachineDef ctx sm = 
  const @{const_name SStateMachine}
  $ mk_literal (get_Initial (nodes sm))
  $ mk_list dummyT (map mk_literal (get_Finals (nodes sm)))
  $ mk_list dummyT (map (compile_Node ctx) (nodes sm))
  $ mk_list dummyT (map (compile_Transition ctx) (transitions sm))"

code_reflect RC_Stm
  functions compile_StateMachineDef

ML \<open>
  Syntax.check_term @{context} (@{code compile_Transition} @{context} (RC_AST.Named_ext ("t1", (RC_AST.Transition_ext ("s1", "s2", NONE, NONE, NONE, NONE, ())))))
\<close>

end