theory RoboChart_Examples
  imports RoboChart "HOL.Transcendental"
begin

text \<open> We can't use braces, because they are both designated as major keywords in Isar. \<close>

interface itf1 =
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
  broadcast event ev1 :: "int \<times> string" ev2 :: "bool"

context itf1
begin

end

robotic_platform rp1 =
  var x :: int
  requires f

(* Linking this to the Circus semantics should be two step:
   outer-syntax transitions with uninterpreted terms --> 
   inner-syntax transitions with compiled actions and expressions (+ alphabet / channel context) --> 
   state machine via semantic function *)

stm stm1 =
  var 
    x :: int = "1"
    y :: int = 1
  initial s1
  final s2
  final s3

context stm1
begin

term s1

term machine

thm machine_def

end

controller c1 =
  sref s1 = stm1
  connection stm1 on x to stm1 on x async
  connection stm1 on x to stm2 on y

module rpm1 =
  cref c1 = c1
  rref rp1 = rp1
  connection c1 on x to rp1 on x

operation op1(x :: int) =
  var y :: int
  precondition "x > 1"
  postcondition "y > x"
  terminates

stm s2 =
  var v1 :: int
  uses itf1
  initial i1
  final f
  var v2 :: real
  broadcast event e1 :: real e2 :: int e3 :: string
  state ms [entry "True" exit "True"]
  transition t1 [frm i1 to act trigger "True" probability "0.5" condition "True"]
  transition t2 [frm p1 to act trigger "False" probability "0.1" condition "False"]
  probabilistic p1
  event e4 :: string

context s2
begin

thm machine_def
thm t1_def

end

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