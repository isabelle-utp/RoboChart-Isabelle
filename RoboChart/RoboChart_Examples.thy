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

stm s1 =
  var v1 :: int
  uses v
  initial i1
  final f
  var v2 :: real
  broadcast event e1 :: real e2 :: int e3 :: string
  state ms [entry "act" exit "hello"]
  transition t1 [frm i1 to act trigger "a?(b)" condition "x > 1"]
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