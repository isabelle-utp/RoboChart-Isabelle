section \<open> RoboChart AST with HOL terms and types \<close>

theory RoboChart_AST
  imports "Isabelle-API.Isabelle_API" "HOL-Eisbach.Eisbach"
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

definition decl_of :: "'a Typed_scheme \<Rightarrow> ID \<times> utyp" where
"decl_of x = (ident x, ttyp x)"

record Variable = Typed +
  initial :: "uterm option" \<comment> \<open> unparsed term \<close>

definition Variable :: "(ID \<times> utyp) \<times> uterm option \<Rightarrow> Variable" where
"Variable = (\<lambda> ((n, t), i) . \<lparr> ident = n, ttyp = t, initial = i \<rparr>)"

record Parameterised = Named +
  parameters :: "(ID \<times> utyp) list"

record ODecl = Parameterised +
  terminate  :: bool

record EDecl = Typed +
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
  opdecls    :: "ODecl list"
  events     :: "EDecl list"

datatype ContainerDecl =
  IntfDecl InterfaceDecl |
  UsesDecl ID |
  ProvDecl ID |
  ReqDecl ID

abbreviation "emptyInterface \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], opdecls = [], events = [] \<rparr>"

record Container = Interface +
  "uses"     :: "ID list"
  "provides" :: "ID list"
  "requires" :: "ID list"

abbreviation "emptyContainer \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], opdecls = [], events = [], uses = [], provides = [], requires = [] \<rparr>"

text \<open> This is essentially an imperative algorithm for updating an interface. We use this to 
  turn a sequence of definitions into an interface object. \<close>

fun upd_Interface :: "InterfaceDecl \<Rightarrow> 'a Interface_scheme \<Rightarrow> 'a Interface_scheme" where
"upd_Interface (VarDecl CNST vs) i = i\<lparr>constants := constants i @ vs\<rparr>" |
"upd_Interface (VarDecl VAR vs) i = i\<lparr>variables := variables i @ vs\<rparr>" |
"upd_Interface (ClockDecl n) i = i\<lparr>clocks := clocks i @ [n]\<rparr>" |
"upd_Interface (OpDecl n ps t) i = i\<lparr>opdecls := opdecls i @ [\<lparr>ident = n, parameters = ps, terminate = t\<rparr>]\<rparr>" |
"upd_Interface (EventDecl b es) i = i\<lparr>events := events i @ map (\<lambda> (n, t). \<lparr> ident = n, ttyp = t, bcast = b \<rparr>) es\<rparr>"

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

datatype (discs_sels) Action = Entry (act: uterm) | During (act: uterm) | Exit (act: uterm)

datatype (discs_sels) Node =
  State (sname: ID) (snodes: "Node list") (stransitions: "Transition list") (sactions: "Action list") |
  Initial (sname: ID) |
  Junction (sname: ID) |
  Final (sname: ID) |
  ProbabilisticJunction (sname: ID)

datatype (discs_sels) StateDecl = 
  ActionDecl Action |
  InnerNodeDecl Node |
  InnerTransitionDecl Transition

definition mk_State :: "ID \<Rightarrow> StateDecl list \<Rightarrow> Node" where
"mk_State n xs = 
  State n [a. InnerNodeDecl a \<leftarrow> xs] [a. InnerTransitionDecl a \<leftarrow> xs] [a. ActionDecl a \<leftarrow> xs]"

datatype StateMachineDecl = 
  StmContainerDecl ContainerDecl |
  NodeDecl Node |
  TransitionDecl Transition

record StateMachineDef = Container +
  nodes       :: "Node list"
  transitions :: "Transition list"

abbreviation "emptyStm \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], opdecls = [], events = [], uses = [], provides = [], requires = [], nodes = [], transitions = [] \<rparr>"

fun upd_StateMachineDef :: "StateMachineDecl \<Rightarrow> 'a StateMachineDef_scheme \<Rightarrow> 'a StateMachineDef_scheme" where
"upd_StateMachineDef (StmContainerDecl cd) stm = upd_Container cd stm" |
"upd_StateMachineDef (NodeDecl nd) stm = stm\<lparr>nodes := nodes stm @ [nd]\<rparr>" |
"upd_StateMachineDef (TransitionDecl td) stm = stm\<lparr>transitions := transitions stm @ [td]\<rparr>"

definition mk_StateMachineDef :: "ID \<times> StateMachineDecl list \<Rightarrow> StateMachineDef" where
"mk_StateMachineDef = (\<lambda> (n, sds). fold upd_StateMachineDef sds (emptyStm\<lparr> ident := n \<rparr>))"

datatype OperationDecl =
  OpStmDecl StateMachineDecl |
  PreDecl uterm |
  PostDecl uterm |
  TerminatesDecl

record Operation = StateMachineDef +
  opparams       :: "(ID \<times> utyp) list"
  preconditions  :: "uterm list"
  postconditions :: "uterm list"
  opterminates   :: bool

abbreviation "emptyOp \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], opdecls = [], events = []
  , uses = [], provides = [], requires = [], nodes = [], transitions = []
  , opparams = [], preconditions = [], postconditions = [], opterminates = False \<rparr>"

fun upd_Operation :: "OperationDecl \<Rightarrow> Operation \<Rightarrow> Operation" where
"upd_Operation (OpStmDecl sd) op = upd_StateMachineDef sd op" |
"upd_Operation (PreDecl p) op = op\<lparr>preconditions := preconditions op @ [p]\<rparr>" |
"upd_Operation (PostDecl p) op = op\<lparr>postconditions := postconditions op @ [p]\<rparr>" |
"upd_Operation TerminatesDecl op = op\<lparr>opterminates := True\<rparr>"

definition mk_Operation :: "(ID \<times> (ID \<times> utyp) list) \<times> OperationDecl list \<Rightarrow> Operation" where
"mk_Operation = (\<lambda> ((n, ps), sds). fold upd_Operation sds (emptyOp\<lparr> ident := n, opparams := ps \<rparr>))"

datatype Connection =
  Connection (cfrom: "ID \<times> ID") (cto: "ID \<times> ID") (async: bool) (bidir: bool)

type_synonym RoboticPlatform = Container

record BlockContainer = Container +
  connections :: "Connection list"

type_synonym Ref = "ID \<times> ID"

datatype ControllerDecl = 
  CtrlContainerDecl ContainerDecl |
  OpRefDecl Ref |
  StmRefDecl Ref |
  ConnectionDecl Connection
  (* TBD: Operations -- I think these should be by reference only *)

record Controller = BlockContainer +
  oprefs  :: "Ref list"
  srefs   :: "Ref list"

abbreviation "emptyCtrl \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], opdecls = []
  , events = [], uses = [], provides = [], requires = []
  , connections = [], oprefs = [], srefs = [] \<rparr>"

fun upd_Controller :: "ControllerDecl \<Rightarrow> Controller \<Rightarrow> Controller" where
"upd_Controller (CtrlContainerDecl cd) ct = upd_Container cd ct" |
"upd_Controller (OpRefDecl orf) ct = ct\<lparr>oprefs := oprefs ct @ [orf]\<rparr>" |
"upd_Controller (StmRefDecl srf) ct = ct\<lparr>srefs := srefs ct @ [srf]\<rparr>" |
"upd_Controller (ConnectionDecl cn) ct = ct\<lparr>connections := connections ct @ [cn]\<rparr>" 

definition mk_Controller :: "ID \<times> ControllerDecl list \<Rightarrow> Controller" where
"mk_Controller = (\<lambda> (n, ct). fold upd_Controller ct (emptyCtrl\<lparr> ident := n \<rparr>))"

record RCModule = BlockContainer +
  rrefs :: "Ref list"
  crefs :: "Ref list"

datatype RCModuleDecl = 
  RCModuleContainerDecl ContainerDecl |
  RRefDecl Ref |
  CRefDecl Ref |
  ModConnectionDecl Connection

abbreviation "emptyRCModule \<equiv> 
  \<lparr> ident = STR '''', constants = [], variables = [], clocks = [], opdecls = []
  , events = [], uses = [], provides = [], requires = []
  , connections = [], rrefs = [], crefs = [] \<rparr>"

fun upd_RCModule :: "RCModuleDecl \<Rightarrow> RCModule \<Rightarrow> RCModule" where
"upd_RCModule (RCModuleContainerDecl cd) ct = upd_Container cd ct" |
"upd_RCModule (RRefDecl rrf) ct = ct\<lparr>rrefs := rrefs ct @ [rrf]\<rparr>" |
"upd_RCModule (CRefDecl crf) ct = ct\<lparr>crefs := crefs ct @ [crf]\<rparr>" |
"upd_RCModule (ModConnectionDecl cn) ct = ct\<lparr>connections := connections ct @ [cn]\<rparr>" 

definition mk_RCModule :: "ID \<times> RCModuleDecl list \<Rightarrow> RCModule" where
"mk_RCModule = (\<lambda> (n, ct). fold upd_RCModule ct (emptyRCModule\<lparr> ident := n \<rparr>))"

datatype FuncDecl = FuncDecl ID "(ID \<times> utyp) list" "utyp" "uterm list" "uterm list"

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
  and StateDecl = ActionDecl | InnerNodeDecl | InnerTransitionDecl
  and StateMachineDecl = StmContainerDecl | NodeDecl | TransitionDecl
  and StateMachineDef_ext = StateMachineDef_ext
  and OperationDecl = OpStmDecl | PreDecl | PostDecl | TerminatesDecl
  and Operation_ext = Operation_ext
  and Connection = Connection
  and ControllerDecl = CtrlContainerDecl | OpRefDecl | StmRefDecl | ConnectionDecl
  and Controller_ext = Controller_ext
  and RCModuleDecl = RCModuleContainerDecl | RRefDecl | CRefDecl | ModConnectionDecl
  and RCModule_ext = RCModule_ext
functions Variable decl_of ident ttyp variables mk_Interface mk_Container mk_State
  mk_StateMachineDef mk_Operation mk_Controller mk_RCModule Transition_ext "from" "to" "trigger" "probability" 
  "condition" "action" "constants" "events" "nodes" "transitions"
  "uses" "provides" "requires" "connections" "oprefs" "srefs" "crefs"
  "preconditions" "postconditions" "opparams"

end