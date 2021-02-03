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

consts goreq     :: "Intensity \<Rightarrow> Intensity \<Rightarrow> bool"
consts analysis  :: "GasSensor list \<Rightarrow> Status"

consts intensity :: "GasSensor list \<Rightarrow> Intensity"

consts location  :: "GasSensor list \<Rightarrow> real"

utp_lit_vars

stm GasAnalysis =
  const thr :: Intensity
  var sts::Status gs::"GasSensor list"  ins::Intensity  anl::real
  event resume stop  turn::real  gas::"GasSensor list"
  initial InitState
  state NoGas
  state Reading
  final FinalState
  state Analysis [entry "sts := analysis(gs)"]
  state GasDetected [entry "ins := intensity(gs)"]
  transition t1 [frm InitState to NoGas action "gs := [] ; anl := 0"]
  transition t2 [frm NoGas to Analysis trigger "gas?(gs)"]
  transition t3 [frm Analysis to NoGas condition "sts = noGas" action "resume"]
  transition t4 [frm Analysis to GasDetected condition "sts = gasD"]
  transition t5 [frm GasDetected to FinalState condition "goreq ins thr" action "stop"]
  transition t6 [frm GasDetected to Reading condition "\<not> goreq ins thr" action "anl := location(gs) ; turn!(anl)"]
  transition t7 [frm Reading to Analysis trigger "gas?(gs)"]

context GasAnalysis
begin

thm transitions
thm nodes
thm machine
thm sm_defs

thm nodes

lemma "action = undefined"
  apply (simp add: action_def action_simp sm_sem Let_unfold usubst)
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