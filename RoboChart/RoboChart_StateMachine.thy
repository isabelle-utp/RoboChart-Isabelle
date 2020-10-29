section \<open> Semantics of State Machines \<close>

theory RoboChart_StateMachine
  imports "RoboChart_AST"
begin

subsection \<open> Semantic AST \<close>

text \<open> The following types represent state machines that have been supplied with typed contextual
  information. Predicates, actions, and expressions have all been enriched with type data, which
  is carried using the type parameters. \<close>

datatype ('pred, 'act, 'prob) STransition = 
  STransition (tn_source: ID) (tn_target: ID) (tn_trigger: "'act option")
              (tn_probability: "'prob option") (tn_cond: "'pred option") (tn_act: "'act option")

datatype ('pred, 'act, 'prob) SNode =
  SNode (n_name: ID) (n_entry: "'act option") (n_during: "'act option") (n_exit: "'act option") 
        (n_nodes: "('pred, 'act, 'prob) SNode list") (n_transitions: "('pred, 'act, 'prob) STransition list")

datatype ('pred, 'act, 'prob) SStateMachine =
  SStateMachine (sm_initial: "ID") (sm_finals: "ID list")
                (sm_nodes: "('pred, 'act, 'prob) SNode list")
                (sm_transitions: "('pred, 'act, 'prob) STransition list")

notation sm_initial ("Init\<index>")
notation sm_finals ("Finals\<index>")
notation sm_nodes ("Nodes\<index>")
notation sm_transitions ("\<^bold>T\<index>")

subsection \<open> Query Functions \<close>

definition sm_node_names :: "('pred, 'act, 'prob) SStateMachine \<Rightarrow> String.literal set" ("Nnames\<index>") where
"sm_node_names sm \<equiv> n_name ` set(sm_nodes sm)"

definition sm_inters :: "('pred, 'act, 'prob) SStateMachine \<Rightarrow> ('pred, 'act, 'prob) SNode list" where
"sm_inters sm = filter (\<lambda> n. n_name n \<notin> set(sm_finals sm)) (sm_nodes sm)"

definition sm_inter_names ("Inames\<index>") where
"sm_inter_names sm \<equiv> n_name ` set (sm_inters sm)"

abbreviation sm_final_names ("Fnames\<index>") where
"sm_final_names M \<equiv> set (Finals\<^bsub>M\<^esub>)"

definition sm_node_map :: 
  "('pred, 'act, 'prob) SStateMachine \<Rightarrow> (ID \<rightharpoonup> ('pred, 'act, 'prob) SNode)" ("Nmap\<index>") where
"sm_node_map M = map_of (map (\<lambda> n. (n_name n, n)) (sm_nodes M))"

definition sm_trans_map :: 
  "('pred, 'act, 'prob) SStateMachine \<Rightarrow> (ID \<rightharpoonup> ('pred, 'act, 'prob) STransition list)" ("Tmap\<index>") where
"sm_trans_map M = map_of (map (\<lambda> n. (n_name n, filter (\<lambda> t. tn_source t = n_name n) (sm_transitions M))) (sm_nodes M))"

lemma dom_sm_node_map: "dom(Nmap\<^bsub>M\<^esub>) = Nnames\<^bsub>M\<^esub>"
  using image_iff by (force simp add: sm_node_map_def sm_node_names_def dom_map_of_conv_image_fst)

lemma dom_sm_trans_map: "dom(Tmap\<^bsub>M\<^esub>) = Nnames\<^bsub>M\<^esub>"
  using image_iff by (force simp add: sm_trans_map_def sm_node_names_def dom_map_of_conv_image_fst)

lemma nnames_finite: "finite(Nnames\<^bsub>M\<^esub>)"
  by (force simp add: sm_node_names_def)

abbreviation sm_init_node :: 
  "('pred, 'act, 'prob) SStateMachine \<Rightarrow> ('pred, 'act, 'prob) SNode" ("Ninit\<index>") where
"sm_init_node M \<equiv> the (sm_node_map M (sm_initial M))"

subsection \<open> Well-formedness \<close>

locale WfStateMachine =
  fixes M :: "('pred, 'act, 'prob) SStateMachine" (structure)
  \<comment> \<open> The list of nnames is a set \<close>
  assumes nnames_distinct: "distinct (map n_name Nodes)"
  and init_is_state: "Init \<in> Nnames"
  and init_not_final: "Init \<notin> Fnames"
  and trans_wf: " \<And> t. t \<in> set(\<^bold>T) \<Longrightarrow> tn_source t \<in> Inames \<and> tn_target t \<in> Nnames"
begin
  lemma init_is_inter: "Init \<in> Inames"
    using init_is_state init_not_final by (auto simp add: sm_inters_def sm_inter_names_def sm_node_names_def)

  lemma nmap_init: "Nmap Init = Some Ninit"
    by (metis domIff dom_sm_node_map init_is_state option.exhaust_sel)

  lemma n_name_init: "n_name Ninit = Init"
  proof (simp add: sm_node_map_def)
    have "map_of (map (\<lambda>n. (n_name n, n)) Nodes) Init = Some (the (map_of (map (\<lambda>n. (n_name n, n)) Nodes) Init))"
      by (metis (no_types) nmap_init sm_node_map_def)
    then show "n_name (the (map_of (map (\<lambda>n. (n_name n, n)) Nodes) Init)) = Init"
      using map_of_SomeD by force
  qed

  lemma nmap_name:
    assumes "n \<in> set Nodes"
    shows "Nmap (n_name n) = Some n"
  proof -
    have "distinct (map fst (map (\<lambda>n. (n_name n, n)) Nodes))"
      by (simp add: comp_def nnames_distinct)
    with assms show ?thesis
      by (simp add: sm_node_map_def)
  qed

  lemma ninit_is_node: "Ninit \<in> set Nodes"
    using init_is_state nmap_name by (auto simp add: sm_node_names_def)

  lemma tmap_node_in_trans: 
    assumes "n \<in> Nnames" "ts \<in> ran(Tmap)"
    shows "set(ts) \<subseteq> set(\<^bold>T)"
    using assms by (auto simp add: sm_trans_map_def ran_distinct nnames_distinct comp_def)

  lemma node_tran_exists:
    assumes "n \<in> Nnames" "t \<in> set(the(Tmap n))"
    shows "t \<in> set(\<^bold>T)"
    by (metis (mono_tags, hide_lams) assms(1) assms(2) domIff dom_sm_trans_map in_mono init_is_state option.collapse ranI tmap_node_in_trans)

end

method check_machine uses defs = 
  (unfold_locales, 
   simp_all add: defs sm_node_names_def sm_inter_names_def sm_inters_def, safe, simp_all)

subsection \<open> Compilation of Semantic State Machines \<close>

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

definition compile_Transition_defn :: "Proof.context \<Rightarrow> Transition \<Rightarrow> term" where
"compile_Transition_defn ctx tr = mk_equals (free (ident tr)) (compile_Transition ctx tr)"

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

definition compile_Node_defn :: "Proof.context \<Rightarrow> Node \<Rightarrow> term" where
"compile_Node_defn ctx node = mk_equals (free (sname node)) (compile_Node ctx node)"

definition get_Initial :: "Node list \<Rightarrow> ID" where
"get_Initial ns = sname (the (find is_Initial ns))"

definition get_Finals :: "Node list \<Rightarrow> ID list" where
"get_Finals ns = map sname (filter is_Final ns)"

definition compile_StateMachineDef :: "Proof.context \<Rightarrow> StateMachineDef \<Rightarrow> term" where
"compile_StateMachineDef ctx sm = 
  const @{const_name SStateMachine}
  $ mk_literal (get_Initial (nodes sm))
  $ mk_list dummyT (map mk_literal (get_Finals (nodes sm)))
  $ mk_list dummyT (map (free \<circ> sname) (nodes sm))
  $ mk_list dummyT (map (free \<circ> ident) (transitions sm))"

code_reflect RC_Stm
  functions 
    compile_Transition 
    compile_Transition_defn
    compile_Node
    compile_Node_defn
    compile_StateMachineDef

end