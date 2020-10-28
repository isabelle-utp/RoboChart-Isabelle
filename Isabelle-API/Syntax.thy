section \<open> Syntax \<close>

theory Syntax
  imports Term Proof Inner_Antiquotations
begin

subsection \<open> Functions \<close>

consts read_term :: "Proof.context \<Rightarrow> String.literal \<Rightarrow> term"

subsection \<open> Code Generation Axioms \<close>

code_printing
  constant "read_term" \<rightharpoonup> (SML) "Syntax.read'_term"

end