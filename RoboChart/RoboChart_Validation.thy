section \<open> RoboChart Validation Rules \<close>

theory RoboChart_Validation
  imports RoboChart_AST
begin

text \<open> Validation rules can be defined as predicates on the AST. Provided they are not too complicated
  they can be code generated for use in guarding the semantic processing. \<close>

text \<open> The following predicate requires that list of named elements each have unique names. \<close>

definition Named_unique :: "'a Named_ext list \<Rightarrow> bool" where
"Named_unique xs = (distinct xs \<and> (\<forall> x \<in> set xs. \<forall> y \<in> set xs. ident x = ident y \<longrightarrow> x = y))"

text \<open> We encode some the well-formedness constraints for interfaces below, and then code generate. \<close>

fun validate_Interface :: "Interface \<Rightarrow> bool" where
"validate_Interface itf = 
  (Named_unique (variables itf @ constants itf) 
   \<and> Named_unique (operations itf)
   \<and> Named_unique (events itf)
   \<and> distinct (events itf))" 

code_reflect RC_Validation
  functions validate_Interface

end