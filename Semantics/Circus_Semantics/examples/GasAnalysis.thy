theory GasAnalysis
  imports "RoboChart-Circus.RoboChart_Circus"
begin

typedecl Chem
type_synonym Intensity = real

subsection \<open> Enumerated Types \<close>

datatype Angle = Left | Right | Back | Front
datatype Status = noGas | gasD

subsection \<open> Data Types \<close>

record GasSensor =
  c :: Chem
  i :: Intensity

subsection \<open> Functions \<close>
 
func analysis(gs :: "GasSensor list"):: Status

func goreq(i1 :: Intensity, i2 :: Intensity):: bool  

func angle(x :: nat) :: Angle

func intensity(gs :: "GasSensor list") :: real
  precondition "#gs \<ge> 0"
  postcondition "\<forall> x :: nat. 0 \<le> x \<and> x \<le> #gs \<longrightarrow> goreq(result, (i (gs ! x)))"
  postcondition "\<exists> y :: nat. 0 \<le> y \<and> y \<le> #gs \<longrightarrow> result = (i (gs ! y))"

func location(gs :: "GasSensor list") :: Angle
  precondition "#gs \<ge> 0"
  postcondition "\<exists> x :: nat. 0 \<le> x \<and> x \<le> #gs \<longrightarrow> i (gs ! x) = intensity gs \<and> result = angle(x)"

utp_lit_vars

stm GasAnalysis =
  const thr :: Intensity
  var sts::Status gs::"GasSensor list"  ins::Intensity  anl::Angle
  event resume stop  turn::Angle  gas::"GasSensor list"
  initial InitState
  state NoGas
  state Reading
  final FinalState
  state Analysis [entry "sts := analysis(gs)"]
  state GasDetected [entry "ins := intensity(gs)"]
  transition t1 [frm InitState to NoGas action "gs := [] ; anl := Front"]
  transition t2 [frm NoGas to Analysis trigger "gas?(gs)"]
  transition t3 [frm Analysis to NoGas condition "sts = noGas" action "resume"]
  transition t4 [frm Analysis to GasDetected condition "sts = gasD"]
  transition t5 [frm GasDetected to FinalState condition "goreq(ins, thr)" action "stop"]
  transition t6 [frm GasDetected to Reading condition "\<not> goreq(ins, thr)" action "anl := location(gs) ; turn!(anl)"]
  transition t7 [frm Reading to Analysis trigger "gas?(gs)"]

context GasAnalysis
begin

thm transitions
thm nodes
thm machine
thm sm_defs

thm nodes

lemma "dlockf \<sqsubseteq> action"
  apply (simp add: action_def action_simp sm_sem Let_unfold usubst)
  apply (simp add: action_rep_eq closure)
  oops


term thr

thm Analysis_def

term machine
term "action"
term sm_inters

thm action_def
thm sm_semantics_def
thm machine_def




end


end