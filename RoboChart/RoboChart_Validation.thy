section \<open> RoboChart Validation Rules \<close>

theory RoboChart_Validation
  imports RoboChart_AST
begin

definition Named_unique :: "'a Named_ext list \<Rightarrow> bool" where
"Named_unique xs = (distinct xs \<and> (\<forall> x \<in> set xs. \<forall> y \<in> set xs. ident x = ident y \<longrightarrow> x = y))"

fun validate_Interface :: "Interface \<Rightarrow> bool" where
"validate_Interface itf = 
  (Named_unique (variables itf @ constants itf) 
   \<and> Named_unique (operations itf)
   \<and> Named_unique (events itf)
   \<and> distinct (events itf))" 

code_reflect RC_Validation
  functions validate_Interface

end