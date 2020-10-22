theory RoboChart_Examples
  imports RoboChart "HOL.Transcendental"
begin

text \<open> We can't use braces, because they are both designated as major keywords in Isar. \<close>

interface i1 =
  clock
    myclk
  var 
    x :: int = "1"
    y :: int = 1
  const 
    z :: int
  var
    a :: "string list"
  opdecl
    myop(x :: int, y :: nat) [terminates]
  opdecl
    myop2(v :: string)
  broadcast event e1 :: "int \<times> string" e2 :: "bool"
  event v1 :: "string"

robotic_platform n =
  var x :: int
  requires f

(* Linking this to the Circus semantics should be two step:
   outer-syntax transitions with uninterpreted terms --> 
   inner-syntax transitions with compiled actions and expressions (+ alphabet / channel context) --> 
   state machine via semantic function *)

stm s1 =
  initial s1
  final s2
  final s3
  state s4 [entry "True"]
  transition t1 [frm s1 to s2 condition "True"]
  transition t2 [frm s1 to s2 condition "False"]

thm s1_def

stm s2 =
  var v1 :: int
  uses v
  initial i1
  final f
  var v2 :: real
  broadcast event e1 :: real e2 :: int e3 :: string
  state ms [entry "True" exit "True"]
  transition t1 [frm i1 to act trigger "True" condition "True"]
  transition t1 [frm p1 to act probability "0.1"]
  probabilistic p1
  event e4 :: string

func sqrt_alt(x :: real) :: real
  precondition "x \<ge> 0"
  postcondition "result \<ge> 0 \<and> result\<^sup>2 = x"

lemma sqrt_alt: "x \<ge> 0 \<Longrightarrow> sqrt_alt x = sqrt x"
  by (auto simp add: sqrt_alt_def fun_spec_def) 

func f2(x :: int, y :: int) :: int
  precondition "x > y"
  postcondition "result = x + 1"

func f3(x :: int) :: int
  postcondition "result = x + 1"

lemma "f3 = (\<lambda> x. x + 1)"
  by (simp add: f3_def fun_spec_def)

end