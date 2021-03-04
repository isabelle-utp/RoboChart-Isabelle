(******************************************************************************)
(* Project: RoboChart in Isabelle/HOL                                         *)
(* File: RoboChart.thy                                                        *)
(* Authors: Simon Foster (University of York, UK)                             *)
(* Emails: simon.foster@york.ac.uk                                            *)
(******************************************************************************)

theory RoboChart
  imports 
    "RoboChart_AST" 
    "RoboChart_Parser"
    "RoboChart_Validation"
    "RoboChart_StateMachine"
    "RoboChart_Semantics"
begin

text \<open> The following types and constants are added for compatibility with RoboTool \<close>

type_synonym boolean = bool

end