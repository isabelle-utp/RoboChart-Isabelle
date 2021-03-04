(******************************************************************************)
(* Project: RoboChart in Isabelle/HOL                                         *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster (University of York, UK)                             *)
(* Emails: simon.foster@york.ac.uk                                            *)
(******************************************************************************)

session "RoboChart"
  = "Isabelle-API" +
  options [document = false, timeout = 1000]
  sessions Optics Z_Toolkit
  theories
    RoboChart

session "RoboChart-Circus" in "Semantics/Circus_Semantics"
  = "UTP-Circus" +
  options [document = false, timeout = 1000]
  sessions "RoboChart"
  theories
    RoboChart_Circus
  
