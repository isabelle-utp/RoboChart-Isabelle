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

thm nodes

thm transitions

thm machine

lemma "action = undefined"
  apply (simp add: sm_sem action_simp sm_trans_map_def action_def)
  oops

lemma "action = undefined"
  apply (simp add: action_def sm_semantics_def)
  apply (simp add: s1_def basic_Node_sem)
  apply (simp add: tr_semantics_def t1_def tn_action_def Let_unfold action_simp tn_condition_def)
  oops

end


end