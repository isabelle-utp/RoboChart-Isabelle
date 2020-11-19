section \<open> Circus Statemachine Semantics \<close>

theory Circus_SM_Semantics
  imports "RoboChart.RoboChart" Actions
begin recall_syntax

subsection \<open> Alphabet \<close>

alphabet robochart_ctrl =
  rc_ctrl :: ID 

type_synonym 's rcst = "'s robochart_ctrl_scheme"
type_synonym ('s, 'e) RoboAction = "('s robochart_ctrl_scheme, 'e) Actions.Action"
type_synonym 's RoboPred = "'s robochart_ctrl_scheme upred"

translations
  (type) "'s rcst" <= (type) "'s robochart_ctrl_scheme"
  (type) "('s, 'e) RoboAction" <= (type) "('s rcst, 'e) Action"
  (type) "'s RoboPred" <= (type) "'s rcst upred"

abbreviation "rc_state \<equiv> robochart_ctrl.more\<^sub>L"

notation rc_state ("\<^bold>r")

syntax
  "_svid_rc_state"  :: "svid" ("\<^bold>r")

translations
  "_svid_rc_state" == "CONST rc_state"
  "_svid_dot \<^bold>r x" <= "x ;\<^sub>L \<^bold>r"

type_synonym ('s, 'e) RTransition = "('s upred, ('s, 'e) Action, unit) STransition"
type_synonym ('s, 'e) RNode = "('s upred, ('s, 'e) Action, unit) SNode"
type_synonym ('s, 'e) RStateMachine = "('s upred, ('s, 'e) Action, unit) SStateMachine"

subsection \<open> State Machine Semantics \<close>

abbreviation "trigger_semantics t \<equiv> 
  (case tn_trigger t of 
    Some e \<Rightarrow> e | 
    None \<Rightarrow> skip)"

definition tn_condition :: "('s, 'e) RTransition \<Rightarrow> 's upred" where
"tn_condition t = case_option true_upred id (tn_cond t)"

definition tn_action :: "('s, 'e) RTransition \<Rightarrow> ('s, 'e) Action" where
"tn_action t = case_option skip id (tn_act t)"

no_utp_lift tn_condition

definition tr_semantics :: "('s, 'e) RTransition \<Rightarrow> (unit, 'e) chan \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>T") where
"tr_semantics t \<epsilon> \<equiv> 
  let tsem = trigger_semantics t ; tn_action t
  in
  tn_condition t \<oplus>\<^sub>p rc_state \<^bold>& 
  rc_state:[if productive tsem then tsem else tsem ; sync \<epsilon>]\<^sub>A\<^sup>+ ; rc_ctrl := \<guillemotleft>tn_target t\<guillemotright>"

definition "n_entry_sem n = case_option skip id (n_entry n)"

definition "n_exit_sem n = case_option skip id (n_exit n)"

definition node_semantics :: 
  "('s, 'e) RStateMachine \<Rightarrow> (unit, 'e) chan \<Rightarrow> ('s, 'e) RNode \<Rightarrow> ('s, 'e) RoboAction" ("_;_ \<turnstile> \<lbrakk>_\<rbrakk>\<^sub>N" [10,0,0] 10) where
  "node_semantics M \<epsilon> node  = 
  (rc_state:[n_entry_sem node]\<^sub>A\<^sup>+ ;
   (foldr (\<box>) (map (\<lambda> t. \<lbrakk>t\<rbrakk>\<^sub>T \<epsilon>) (the (Tmap\<^bsub>M\<^esub> (n_name node)))) stop) ;
   rc_state:[n_exit_sem node]\<^sub>A\<^sup>+)"

dataspace stm_context =
  channels null_event :: unit 

context stm_context
begin

notation null_event ("\<epsilon>")

end

definition sm_semantics :: "('st, 'ch) RStateMachine \<Rightarrow> _ \<Rightarrow> ('st, 'ch) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>M") where
"sm_semantics M null_event = 
    (rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ;
    iteration (map (\<lambda> n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) (sm_inters M)))"

lemmas sm_sem_def = sm_semantics_def node_semantics_def sm_inters_def sm_inter_names_def

lemma tr_semantics_subst_ctrl: "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> (\<lbrakk>a\<rbrakk>\<^sub>T null_event) = \<lbrakk>a\<rbrakk>\<^sub>T null_event"
  by (simp add: tr_semantics_def action_simp action_subst usubst unrest frame_asubst Let_unfold)

lemma tr_choice_subst_ctrl:
  "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> foldr (\<box>) (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop = foldr (\<box>) (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop"
  by (induct ts, simp_all add: action_simp action_subst usubst tr_semantics_subst_ctrl)

lemma sm_semantics_subst_ctrl:
  "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> node_semantics M null_event node = node_semantics M null_event node"
  by (simp add: node_semantics_def action_simp action_subst frame_asubst tr_choice_subst_ctrl unrest)

(* Tests *)

definition "circus_predT stT = Type @{type_name upred} [stT]"
definition "circus_actionT stT evT = Type @{type_name Action} [stT, evT]"
definition "circus_probT stT = @{typ unit}"

definition "actionN = STR ''action''"

definition "action_eq = 
  mk_equals (free actionN) (const @{const_name sm_semantics} $ free machineN $ free STR ''null_event'')"

definition "add_stm_context smd = 
  smd\<lparr> uses := STR ''stm_context'' # uses smd \<rparr>"

code_reflect RC_Circus_Semantics
  functions circus_predT circus_actionT circus_probT action_eq add_stm_context

setup \<open>
  let open RC_Compiler; open RC_Circus_Semantics; open Specification
    val cont = snd o definition NONE [] [] ((Binding.empty, []), action_eq)
    val circus_semantics = 
      { predT = circus_predT, actionT = circus_actionT, probT = circus_probT
     , itf_sem = K I, rpl_sem = K I, stm_sem = context_Stm_Semantics cont o add_stm_context } : RCSem_Proc

  in
    Stm_Sem.put circus_semantics
  end
\<close>

context stm_context
begin

term null_event

end

stm stm1 =
  var x :: int
  event e :: unit
  initial s1
  final s2
  transition t1 [frm s1 to s2 condition "U(x = 0)" action "act(x := 1)"]

lemma entry_basic_Node [simp]: "n_entry_sem (basic_Node n) = skip"
  by (simp add: n_entry_sem_def basic_Node_def)

lemma exit_basic_Node [simp]: "n_exit_sem (basic_Node n) = skip"
  by (simp add: n_exit_sem_def basic_Node_def)


lemma basic_Node_sem:
  "(M;\<epsilon> \<turnstile> \<lbrakk>basic_Node n\<rbrakk>\<^sub>N) = foldr (\<box>) (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T \<epsilon>) (the (Tmap\<^bsub>M\<^esub> n))) stop"
  by (simp add: node_semantics_def action_simp)


lemma [simp]: "productive P \<Longrightarrow> productive (P ; Q)"
  by (transfer, simp add: closure)

lemma [simp]: "productive Q \<Longrightarrow> productive (P ; Q)"
  by (transfer, simp add: closure)


context stm1
begin

term null_event

thm t1_def

term machine

term "action"

lemma [simp]: "Init\<^bsub>machine\<^esub> = STR ''s1''"
  by (simp add: machine_def)

lemma [simp]: "Tmap\<^bsub>machine\<^esub> = [STR ''s1'' \<mapsto> [t1], STR ''s2'' \<mapsto> []]"
  by (auto simp add: sm_trans_map_def machine_def s1_def s2_def t1_def)

lemma [simp]: "sm_inters machine = [s1]"
  by (auto simp add: machine_def sm_inters_def s1_def s2_def basic_Node_def)

lemma "action = undefined"
  apply (simp add: action_def sm_semantics_def)
  apply (simp add: s1_def basic_Node_sem)
  apply (simp add: tr_semantics_def t1_def tn_action_def Let_unfold action_simp tn_condition_def)
  oops

end

end