theory RoboChart_Semantic_Processors
  imports RoboChart_AST "HOL.Real"
begin

type_synonym PredType = "typ \<Rightarrow> typ"
type_synonym ActionType = "typ \<Rightarrow> typ \<Rightarrow> typ"
type_synonym ProbType = "typ \<Rightarrow> typ"

definition "null_predT = (\<lambda> _. @{typ bool})"
definition "null_actionT = (\<lambda> _ _. @{typ bool})"
definition "null_probT = (\<lambda> _. @{typ real})"

record RCTypes =
  predT      :: PredType
  pred_syn   :: "String.literal"
  actionT    :: ActionType
  action_syn :: "String.literal"
  probT      :: ProbType
  prob_syn   :: "String.literal"

record RCSem_Proc = 
  rctypes    :: RCTypes
  itf_sem    :: "Interface \<Rightarrow> theory \<Rightarrow> theory"
  rpl_sem    :: "RoboticPlatform \<Rightarrow> theory \<Rightarrow> theory"
  stm_sem    :: "StateMachineDef \<Rightarrow> theory \<Rightarrow> theory"

definition "null_RCTypes =
  \<lparr> predT = null_predT
  , pred_syn = STR ''any''
  , actionT = null_actionT
  , action_syn = STR ''any''
  , probT = null_probT
  , prob_syn = STR ''any'' \<rparr>"

definition "null_RCSem_Proc =
  \<lparr> rctypes = null_RCTypes
  , itf_sem = (\<lambda> _. id)
  , rpl_sem = (\<lambda> _. id)
  , stm_sem = (\<lambda> _. id)
  \<rparr>"

code_reflect RC_SemProc
  datatypes RCTypes_ext = RCTypes_ext and RCSem_Proc_ext = RCSem_Proc_ext
  functions null_predT null_actionT null_probT null_RCTypes null_RCSem_Proc predT pred_syn actionT action_syn probT rctypes itf_sem rpl_sem stm_sem

end