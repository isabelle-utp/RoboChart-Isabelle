section \<open> Inner Syntax Antiquotations \<close>

theory Inner_Antiquotations
  imports Term Type
begin

syntax
  "_inner_const_name" :: "id \<Rightarrow> logic" ("@{const'_name _}")
  "_inner_type_name" :: "type \<Rightarrow> logic" ("@{type'_name _}")

parse_translation \<open>
  [(@{syntax_const "_inner_const_name"}, 
    fn ctx => fn terms => 
    case terms of [Free (n, _)] => 
      let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} ctx n
      in HOLogic.mk_literal c end)
  ,(@{syntax_const "_inner_type_name"}, 
    fn ctx => fn terms => 
    case terms of [Const (n, _)] => 
      let val Type (c, _) = Proof_Context.read_type_name {proper = true, strict = false} ctx (Lexicon.unmark_type n)
      in HOLogic.mk_literal c end)
]
\<close>

end