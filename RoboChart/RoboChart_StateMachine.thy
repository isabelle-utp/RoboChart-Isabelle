section \<open> Semantics of State Machines \<close>

theory RoboChart_StateMachine
  imports "RoboChart_AST"
begin

text \<open> The following types represent state machines that have been supplied with typed contextual
  information. Predicates, actions, and expressions have all been enriched with type data, which
  is carried using the type parameters. \<close>

record ('pred, 'act, 'prob) STransition = 
  tn_source      :: ID
  tn_target      :: ID
  tn_trigger     :: "'act option"
  tn_probability :: "'prob"
  tn_condition   :: "'pred"
  tn_action      :: "'act"

datatype ('pred, 'act, 'prob) SNode =
  SNode (n_name: ID) (n_entry: 'act) (n_during: 'act) (n_exit: 'act) 
        (n_nodes: "('pred, 'act, 'prob) SNode list") (n_transitions: "('pred, 'act, 'prob) STransition list")

record ('pred, 'act, 'prob) SStateMachine =
  sm_initial     :: "string" ("init\<index>")
  sm_finals      :: "string list" ("finals\<index>")
  sm_nodes       :: "('pred, 'act, 'prob) SNode list" ("nodes\<index>")
  sm_transitions :: "('pred, 'act, 'prob) STransition list" ("\<^bold>T\<index>")

end