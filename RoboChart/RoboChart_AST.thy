section \<open> RoboChart AST with HOL terms and types \<close>

theory RoboChart_AST
  imports "Isabelle-API.Isabelle_API"
begin

text \<open> Here, we define the RoboChart AST using a series of HOL data types. We also define some 
  basic processing functions for helping conversion of the textual syntax to AST elements. 
  We code generate all of these to ML, which allows them to be used for semantic generation. \<close>

type_synonym ID = "String.literal"

datatype VariableModifier = VAR | CNST

record Named =
  ident :: ID

record Typed = Named +
  type :: "typ"

record Variable = Typed +
  initial :: "term option"

definition Variable :: "(String.literal \<times> typ) \<times> term option \<Rightarrow> Variable" where
"Variable = (\<lambda> ((n, t), i) . \<lparr> ident = n, type = t, initial = i \<rparr>)"

record Parameterised = Named +
  parameters :: "(ID \<times> typ) list"

record ODecl = Parameterised +
  terminate  :: bool

record EDecl = Named +
  etype :: "typ"
  bcast :: bool

text \<open> This is the syntactic representation of an interface element. The body of interface consists
  of a list of these elements. \<close>

datatype InterfaceDecl =
  VarDecl VariableModifier "Variable list" |
  ClockDecl ID |
  OpDecl ID "(ID \<times> typ) list" "bool" |
  EventDecl bool "(ID \<times> typ) list"

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

type_synonym RoboticPlatform = ContainerDecl

datatype TriggerType =
  Input ID ID | Output ID "term" | Sync ID "term"

record Trigger =
  start   :: "term option"
  trig    :: "TriggerType"
  time    :: "ID option"
  reset   :: "ID list"
  "end"   :: "term option"
  
record Transition = Named +
  "from"        :: "ID"
  "to"          :: "ID"
  "trigger"     :: "Trigger option"
  "probability" :: "term option"
  "condition"   :: "term option"
  "action"      :: "term option"

datatype Action = Entry ID | During ID | Exit ID

datatype Node =
  State (sname: ID) (snodes: "Node list") (stransitions: "Transition list") (sactions: "Action list") |
  Initial ID |
  Junction ID |
  Final ID |
  ProbabilisticJunction ID

datatype StateMachineDecl = 
  StmContainerDecl ContainerDecl |
  NodeDecl Node |
  TransitionDecl Transition

record StateMachineDef = Container +
  nodes       :: "Node list"
  transitions :: "Transition list"

text \<open> This is essentially an imperative algorithm for updating an interface. We use this to 
  turn a sequence of definitions into an interface object. \<close>

fun upd_Interface :: "InterfaceDecl \<Rightarrow> 'a Interface_scheme \<Rightarrow> 'a Interface_scheme" where
"upd_Interface (VarDecl CNST vs) i = i\<lparr>constants := constants i @ vs\<rparr>" |
"upd_Interface (VarDecl VAR vs) i = i\<lparr>variables := variables i @ vs\<rparr>" |
"upd_Interface (ClockDecl n) i = i\<lparr>clocks := clocks i @ [n]\<rparr>" |
"upd_Interface (OpDecl n ps t) i = i\<lparr>operations := operations i @ [\<lparr>ident = n, parameters = ps, terminate = t\<rparr>]\<rparr>" |
"upd_Interface (EventDecl b es) i = i\<lparr>events := events i @ map (\<lambda> (n, t). \<lparr> ident = n, etype = t, bcast = b \<rparr>) es\<rparr>"

definition mk_Interface :: "ID \<times> InterfaceDecl list \<Rightarrow> Interface" where
"mk_Interface = (\<lambda> (n, its). foldr upd_Interface its (emptyInterface\<lparr> ident := n \<rparr>))"

text \<open> Same as the above, but for container-like structures (e.g. robotic platforms) \<close>

fun upd_Container :: "ContainerDecl \<Rightarrow> Container \<Rightarrow> Container" where
"upd_Container (IntfDecl d) c = upd_Interface d c" |
"upd_Container (UsesDecl d) c = c\<lparr>uses := uses c @ [d]\<rparr>" |
"upd_Container (ProvDecl d) c = c\<lparr>provides := provides c @ [d]\<rparr>" |
"upd_Container (ReqDecl d) c = c\<lparr>requires := requires c @ [d]\<rparr>"

definition mk_Container :: "ID \<times> ContainerDecl list \<Rightarrow> Container" where
"mk_Container = (\<lambda> (n, its). foldr upd_Container its (emptyContainer\<lparr> ident := n \<rparr>))"

datatype Function = Func ID "(ID \<times> typ) list" "typ" "term" "term"

code_reflect RC_AST
  datatypes VariableModifier = VAR | CNST 
  and Named_ext = Named_ext
  and Typed_ext = Typed_ext
  and Parameterised_ext = Parameterised_ext
  and Function = Func
  and Variable_ext = Variable_ext
  and ODecl_ext = ODecl_ext
  and EDecl_ext = EDecl_ext
  and InterfaceDecl = VarDecl | ClockDecl | OpDecl | EventDecl
  and Interface_ext = Interface_ext
  and ContainerDecl = IntfDecl | UsesDecl | ProvDecl | ReqDecl
  and Container_ext = Container_ext
  and TriggerType = Input | Output | Sync
  and Trigger_ext = Trigger_ext
  and Transition_ext = Transition_ext
  and Action = Entry | During | Exit
  and Node = State | Initial | Junction | Final | ProbabilisticJunction
  and StateMachineDecl = StmContainerDecl | NodeDecl | TransitionDecl
  and StateMachineDef_ext = StateMachineDef_ext
functions Variable ident variables mk_Interface mk_Container Transition_ext

end