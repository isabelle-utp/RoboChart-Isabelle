(******************************************************************************)
(* Project: RoboChart in Isabelle/HOL                                         *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster (University of York, UK)                             *)
(* Emails: simon.foster@york.ac.uk                                            *)
(******************************************************************************)

session "Isabelle-API" in "Isabelle-API"
  = "HOL" +
  options [document = false, timeout = 1000]
  theories
    Isabelle_API

session "RoboChart" in "RoboChart"
  = "Isabelle-API" +
  options [document = false, timeout = 1000]
  sessions Optics
  theories
    RoboChart
  