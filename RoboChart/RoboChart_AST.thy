section \<open> RoboChart AST with HOL terms and types \<close>

theory RoboChart_AST
  imports "Isabelle-API.Isabelle_API"
begin

text \<open> Here, we define the RoboChart AST using a series of HOL data types. We also define some 
  basic processing functions for helping conversion of the textual syntax to AST elements. 
  We code generate all of these to ML, which allows them to be used for semantic generation. \<close>

type_synonym ID = "String.literal"
type_synonym uterm = "String.literal" \<comment> \<open> unprocessed terms \<close>
type_synonym utyp = "String.literal"  \<comment> \<open> unprocessed types \<close> 

datatype VariableModifier = VAR | CNST

record Named =
  ident :: ID

record Typed = Named +
  ttyp :: "utyp"

record Variable = Typed +
  initial :: "uterm option" \<comment> \<open> unparsed term \<close>

definition Variable :: "(ID \<times> utyp) \<times> uterm option \<Rightarrow> Variable" where
"Variable = (\<lambda> ((n, t), i) . \<lparr> ident = n, ttyp = t, initial = i \<rparr>)"

record Parameterised = Named +
  parameters :: "(ID \<times> utyp) list"

record ODecl = Parameterised +
  terminate  :: bool

record EDecl = Named +
  etype :: "utyp"
  bcast :: bool

text \<open> This is the syntactic representation of an interface element. The body of interface consists
  of a list of these elements. \<close>

datatype InterfaceDecl =
  VarDecl VariableModifier "Variable list" |
  ClockDecl ID |
  OpDecl ID "(ID \<times> utyp) list" "bool" |
  EventDecl bool "(ID \<times> utyp) list"

record Interface = Named +
  constants  :: "Variable list"
  variables  :: "Variable list"
  clocks     :: "ID list"
  operations :: "ODecl list"
  events     :: "EDecl list"

datatype ContainerDecl =
  IntfDecl InterfaceDecl |
  UsesDecl ID |
  ProvDecl ID |
  ReqDecl ID

abbreviation "emptyInterface \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], operations = [], events = [] \<rparr>"

record Container = Interface +
  uses     :: "ID list"
  provides :: "ID list"
  requires :: "ID list"

abbreviation "emptyContainer \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], operations = [], events = [], uses = [], provides = [], requires = [] \<rparr>"

text \<open> This is essentially an imperative algorithm for updating an interface. We use this to 
  turn a sequence of definitions into an interface object. \<close>

fun upd_Interface :: "InterfaceDecl \<Rightarrow> 'a Interface_scheme \<Rightarrow> 'a Interface_scheme" where
"upd_Interface (VarDecl CNST vs) i = i\<lparr>constants := constants i @ vs\<rparr>" |
"upd_Interface (VarDecl VAR vs) i = i\<lparr>variables := variables i @ vs\<rparr>" |
"upd_Interface (ClockDecl n) i = i\<lparr>clocks := clocks i @ [n]\<rparr>" |
"upd_Interface (OpDecl n ps t) i = i\<lparr>operations := operations i @ [\<lparr>ident = n, parameters = ps, terminate = t\<rparr>]\<rparr>" |
"upd_Interface (EventDecl b es) i = i\<lparr>events := events i @ map (\<lambda> (n, t). \<lparr> ident = n, etype = t, bcast = b \<rparr>) es\<rparr>"

definition mk_Interface :: "ID \<times> InterfaceDecl list \<Rightarrow> Interface" where
"mk_Interface = (\<lambda> (n, its). fold upd_Interface its (emptyInterface\<lparr> ident := n \<rparr>))"

text \<open> Same as the above, but for container-like structures (e.g. robotic platforms) \<close>

fun upd_Container :: "ContainerDecl \<Rightarrow> 'a Container_scheme \<Rightarrow> 'a Container_scheme" where
"upd_Container (IntfDecl d) c = upd_Interface d c" |
"upd_Container (UsesDecl d) c = c\<lparr>uses := uses c @ [d]\<rparr>" |
"upd_Container (ProvDecl d) c = c\<lparr>provides := provides c @ [d]\<rparr>" |
"upd_Container (ReqDecl d) c = c\<lparr>requires := requires c @ [d]\<rparr>"

definition mk_Container :: "ID \<times> ContainerDecl list \<Rightarrow> Container" where
"mk_Container = (\<lambda> (n, its). fold upd_Container its (emptyContainer\<lparr> ident := n \<rparr>))"

type_synonym RoboticPlatform = ContainerDecl

(* For now, triggers simply action terms (inner syntax) to be interpreted by the particular 
  semantic model. *)

(*
datatype TriggerType =
  Input ID ID | 
  Output ID "uterm" | \<comment> \<open> unparsed term \<close>
  Sync ID "uterm"

record Trigger =
  start   :: "uterm option"
  trig    :: "TriggerType"
  time    :: "ID option"
  reset   :: "ID list"
  "end"   :: "uterm option"
*)  

record Transition = Named +
  "from"        :: "ID"
  "to"          :: "ID"
  "trigger"     :: "uterm option"
  "probability" :: "uterm option"
  "condition"   :: "uterm option"
  "action"      :: "uterm option"

datatype Action = Entry (act: uterm) | During (act: uterm) | Exit (act: uterm)

fun is_Entry :: "Action \<Rightarrow> bool" where "is_Entry (Entry _) = True" | "is_Entry _ = False"
fun is_During :: "Action \<Rightarrow> bool" where "is_During (During _) = True" | "is_During _ = False"
fun is_Exit :: "Action \<Rightarrow> bool" where "is_Exit (Exit _) = True" | "is_Exit _ = False"

datatype Node =
  State (sname: ID) (snodes: "Node list") (stransitions: "Transition list") (sactions: "Action list") |
  Initial (sname: ID) |
  Junction (sname: ID) |
  Final (sname: ID) |
  ProbabilisticJunction (sname: ID)

fun is_Initial :: "Node \<Rightarrow> bool" where "is_Initial (Initial _) = True" | "is_Initial _ = False"
fun is_Final :: "Node \<Rightarrow> bool" where "is_Final (Final _) = True" | "is_Final _ = False"

datatype StateMachineDecl = 
  StmContainerDecl ContainerDecl |
  NodeDecl Node |
  TransitionDecl Transition

record StateMachineDef = Container +
  nodes       :: "Node list"
  transitions :: "Transition list"

abbreviation "emptyStm \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], operations = [], events = [], uses = [], provides = [], requires = [], nodes = [], transitions = [] \<rparr>"

fun upd_StateMachineDef :: "StateMachineDecl \<Rightarrow> StateMachineDef \<Rightarrow> StateMachineDef" where
"upd_StateMachineDef (StmContainerDecl cd) stm = upd_Container cd stm" |
"upd_StateMachineDef (NodeDecl nd) stm = stm\<lparr>nodes := nodes stm @ [nd]\<rparr>" |
"upd_StateMachineDef (TransitionDecl td) stm = stm\<lparr>transitions := transitions stm @ [td]\<rparr>"

definition mk_StateMachineDef :: "ID \<times> StateMachineDecl list \<Rightarrow> StateMachineDef" where
"mk_StateMachineDef = (\<lambda> (n, sds). fold upd_StateMachineDef sds (emptyStm\<lparr> ident := n \<rparr>))"

datatype FuncDecl = FuncDecl ID "(ID \<times> utyp) list" "utyp" "uterm" "uterm"

datatype Function = Func ID "(ID \<times> typ) list" "typ" "term" "term"

code_reflect RC_AST
  datatypes VariableModifier = VAR | CNST 
  and Named_ext = Named_ext
  and Typed_ext = Typed_ext
  and Parameterised_ext = Parameterised_ext
  and FuncDecl = FuncDecl
  and Function = Func
  and Variable_ext = Variable_ext
  and ODecl_ext = ODecl_ext
  and EDecl_ext = EDecl_ext
  and InterfaceDecl = VarDecl | ClockDecl | OpDecl | EventDecl
  and Interface_ext = Interface_ext
  and ContainerDecl = IntfDecl | UsesDecl | ProvDecl | ReqDecl
  and Container_ext = Container_ext
(*
  and TriggerType = Input | Output | Sync
  and Trigger_ext = Trigger_ext
*)
  and Transition_ext = Transition_ext
  and Action = Entry | During | Exit
  and Node = State | Initial | Junction | Final | ProbabilisticJunction
  and StateMachineDecl = StmContainerDecl | NodeDecl | TransitionDecl
  and StateMachineDef_ext = StateMachineDef_ext
functions Variable ident ttyp variables mk_Interface mk_Container mk_StateMachineDef Transition_ext
  "from" "to" "trigger" "probability" "condition" "action"

end