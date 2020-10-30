section \<open> Circus Statemachine Semantics \<close>

theory Circus_SM_Semantics
  imports "RoboChart.RoboChart" Actions
begin

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

abbreviation "trigger_semantics t null_event \<equiv> 
  (case tn_trigger t of 
    Some e \<Rightarrow> if productive e then e else sync null_event | 
    None \<Rightarrow> sync null_event)"

definition tn_condition :: "('s, 'e) RTransition \<Rightarrow> 's upred" where
"tn_condition t = case_option true_upred id (tn_cond t)"

definition tn_action :: "('s, 'e) RTransition \<Rightarrow> ('s, 'e) Action" where
"tn_action t = case_option skip id (tn_act t)"

no_utp_lift tn_condition

definition tr_semantics :: "('s, 'e) RTransition \<Rightarrow> (unit, 'e) chan \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>T") where
"tr_semantics t null_event \<equiv> 
  tn_condition t \<oplus>\<^sub>p rc_state \<^bold>& 
  rc_state:[trigger_semantics t null_event ; tn_action t]\<^sub>A\<^sup>+ ; rc_ctrl := \<guillemotleft>tn_target t\<guillemotright>"

definition "n_entry_sem n = case_option skip id (n_entry n)"

definition "n_exit_sem n = case_option skip id (n_exit n)"

definition node_semantics :: 
  "('s, 'e) RStateMachine \<Rightarrow> (unit, 'e) chan \<Rightarrow> ('s, 'e) RNode \<Rightarrow> ('s, 'e) RoboAction" ("_;_ \<turnstile> \<lbrakk>_\<rbrakk>\<^sub>N" [10,0,0] 10) where
  "node_semantics M null_event node  = 
  (rc_state:[n_entry_sem node]\<^sub>A\<^sup>+ ;
   (foldr (\<box>) (map (\<lambda> t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) (the (Tmap\<^bsub>M\<^esub> (n_name node)))) stop) ;
   rc_state:[n_exit_sem node]\<^sub>A\<^sup>+)"

definition sm_semantics :: "('s, 'e) RStateMachine \<Rightarrow> (unit, 'e) chan \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>M") where
"sm_semantics M null_event = 
    (rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ;
    iteration (map (\<lambda> n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) (sm_inters M)))"

lemmas sm_sem_def = sm_semantics_def node_semantics_def sm_inters_def sm_inter_names_def

lemma tr_semantics_subst_ctrl: "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> (\<lbrakk>a\<rbrakk>\<^sub>T null_event) = \<lbrakk>a\<rbrakk>\<^sub>T null_event"
  by (simp add: tr_semantics_def action_simp usubst unrest frame_asubst)

lemma tr_choice_subst_ctrl:
  "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> foldr (\<box>) (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop = foldr (\<box>) (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop"
  by (induct ts, simp_all add: action_simp usubst tr_semantics_subst_ctrl)

lemma sm_semantics_subst_ctrl:
  "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> node_semantics M null_event node = node_semantics M null_event node"
  by (simp add: node_semantics_def action_simp frame_asubst tr_choice_subst_ctrl unrest)

(* Tests *)

definition "circus_predT stT = Type @{type_name upred} [stT]"
definition "circus_actionT stT evT = Type @{type_name Action} [stT, evT]"
definition "circus_probT stT = @{typ unit}"

code_reflect RC_Circus_Semantics
  functions circus_predT circus_actionT circus_probT

setup \<open>
  let open RC_Compiler; open RC_Circus_Semantics in
  Stm_Sem.put (ctx_semantics circus_predT circus_actionT circus_probT)
  end
\<close>


dataspace stm_context =
  channels null_event :: unit 

context stm_context
begin

notation null_event ("\<epsilon>")

end

stm stm1 =
  var x :: int
  event e :: unit
  initial s1
  final s2
  transition t1 [frm s1 to s2 condition "U(x = 0)" action "act(x := 1 ; e)"]

context stm1
begin

thm t1_def

term machine

term "\<lbrakk>machine\<rbrakk>\<^sub>M"

end

end