section \<open> Inner Syntax Antiquotations \<close>

theory Inner_Antiquotations
  imports Term Type
begin

syntax
  "_inner_const_name" :: "id \<Rightarrow> logic" ("@{const'_name _}")
  "_inner_type_name"  :: "type \<Rightarrow> logic" ("@{type'_name _}")
  "_inner_typ"        :: "type \<Rightarrow> logic" ("@{typ _}")

ML \<open> 
\<close>

parse_translation \<open>
let
  open Syntax;
  open HOLogic;
  fun 
    lift_typ (Type (n, ps)) = 
      const @{const_name Type} $ mk_literal n $ mk_list dummyT (map lift_typ ps) |
    lift_typ (TFree (n, sort)) = 
      const @{const_name TFree} $ mk_literal n $ mk_list dummyT (map mk_literal sort) |
    lift_typ (TVar ((n, i), sort)) =
      const @{const_name TVar} $ (mk_prod (mk_literal n, mk_numeral i)) $ mk_list dummyT (map mk_literal sort)
in
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
  ,(@{syntax_const "_inner_typ"},
    fn ctx => fn terms => 
    case terms of [t] => 
      lift_typ (Syntax_Phases.decode_typ t))
]
end
\<close>

end