theory Simple_Stm
  imports "RoboChart-Circus.RoboChart_Circus"
begin

stm stm1 =
  var x :: int
  event e :: unit
  initial s1
  final s2
  transition t1 [frm s1 to s2 condition "x = 0" action "x := 1"]

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