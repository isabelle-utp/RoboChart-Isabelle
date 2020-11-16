section \<open> RoboChart Parser Library \<close>

theory RoboChart_Parser
  imports RoboChart_AST "HOL.Real"
  keywords 
    "var" "const" "clock" "opdecl" "terminates" 
    "broadcast" "event" "precondition" "postcondition"
    "uses" "provides" "requires"
    "state" "entry" "during" "exit" "probabilistic" "initial" "final" "junction"
    "transition" "frm" "to" "trigger" "probability" "condition" "action" "!" "?" "]>" "<["
    "opref" "sref" "rref" "cref" "connection" "on" "async" "mult"
begin

text \<open> We define a set of parser combinators for the RoboChart commands. These simply produce 
  elements of the AST, but do no semantic processing. The only exception is that types are parsed
  and interpreted as these cannot be defined within most structures. Terms are not processed,
  as this depends on the particular action semantics being employed. \<close>

ML \<open>
structure RC_Parser =
struct

open HOLogic;
open Parse;
open Scan;
open Syntax;
open RC_AST;

fun quad1 (((a, b), c), d) = (a, b, c, d);
fun quint1 ((((a, b), c), d), e) = (a, b, c, d, e);

val nameParser = name -- ($$$ "::" |-- typ);

val variableParser = 
  (nameParser -- (option (@{keyword "="} |-- term)))
  >> variable;

val parameterParser = 
  @{keyword "("} |-- repeat (nameParser --| @{keyword ","}) -- nameParser --| @{keyword ")"}
  >> (fn (xs, x) => xs @ [x])

val varDeclParser = 
  (@{keyword "var"} >> (fn _ => VAR) || @{keyword "const"} >> (fn _ => CNST)) 
    -- repeat1 variableParser >> VarDecl;
  
val clockDeclParser =
  (@{keyword "clock"} |-- name) >> ClockDecl;

val terminatesParser =
  optional (@{keyword "["} |-- (@{keyword "terminates"} >> (fn _ => true)) --| @{keyword "]"}) false;

val operationSigParser =
  @{keyword "opdecl"} |-- (name -- parameterParser -- terminatesParser) >> triple1 >> OpDecl

val eventDecl =
  (Scan.optional (@{keyword "broadcast"} >> (fn _ => true)) false 
  -- (@{keyword "event"} |-- repeat1 nameParser)) >> EventDecl

val intfKeyParser =
  varDeclParser || clockDeclParser || operationSigParser || eventDecl

val interfaceParser = 
  (name -- 
    (@{keyword "="} |--
      repeat1 intfKeyParser
    )) >> mk_Interface;

val usesParser = @{keyword uses} |-- name >> UsesDecl;
val provParser = @{keyword provides} |-- name >> ProvDecl;
val reqParser = @{keyword requires} |-- name >> ReqDecl;

val containerDeclParser =
  (intfKeyParser >> IntfDecl) || usesParser || provParser || reqParser;
  
val actionParser =
  (@{keyword "entry"} |-- name >> Entry) || 
  (@{keyword "during"} |-- name >> During) || 
  (@{keyword "exit"} |-- name >> Exit);

val nodeParser =
  (@{keyword "initial"} |-- name >> Initial) ||
  (@{keyword "junction"} |-- name >> Junction) ||
  (@{keyword "final"} |-- name >> Final) ||
  (@{keyword "probabilistic"} |-- name >> ProbabilisticJunction) ||
  (@{keyword "state"} |-- name -- 
    ($$$ "[" |-- repeat actionParser --| $$$ "]") >> (fn (n, a) => State (n, [], [], a)))

(*
val eventParser = 
  ((name --| (@{keyword "?"} -- @{keyword "["})) -- name --| @{keyword "]"}) >> Input ||
  ((name --| (@{keyword "!"} -- @{keyword "["})) -- term --| @{keyword "]"}) >> Output

val triggerParser =
  (@{keyword "trigger"}) |--
  option ($$$ "[" |-- term --| $$$ "]>") --
  eventParser --
  option ($$$ "<[" |-- term --| $$$ "]")
  >> (fn ((bg, ev), ed) => Trigger_ext (bg, ev, NONE, [], ed, ()))
*)

val transitionParser =
  (@{keyword "transition"} |-- name) --
    ($$$ "[" |--
      (@{keyword "frm"} |-- name) --
      (@{keyword "to"} |-- name) --
      option (@{keyword "trigger"} |-- term) --
      option (@{keyword "probability"} |-- term) --
      option (@{keyword "condition"} |-- term) --
      option (@{keyword "action"} |-- term)
     --| $$$ "]") >> (fn (n, (((((s, t), tr), p), c), a)) => Named_ext (n, Transition_ext (s, t, tr, p, c, a, ())));

val stateMachineBodyParser = 
  (containerDeclParser >> StmContainerDecl) || (nodeParser >> NodeDecl) || (transitionParser >> TransitionDecl) ;

val stateMachineDefParser =
  (name --
    (@{keyword "="} |--
      repeat1 stateMachineBodyParser
    ));

val operationBodyParser = 
  (stateMachineBodyParser >> OpStmDecl) ||
  ((@{keyword "precondition"} |-- term) >> PreDecl) ||
  ((@{keyword "postcondition"} |-- term) >> PostDecl) ||
  (@{keyword "terminates"} >> K TerminatesDecl)
  
val operationParser =
  ((name -- parameterParser) -- (@{keyword "="} |-- repeat1 operationBodyParser))
 >> mk_Operation

val connectionParser =
  ((@{keyword connection} |-- name) 
  -- (@{keyword on} |-- name)
  -- (@{keyword to} |-- name)
  -- (@{keyword on} |-- name)
  -- Scan.optional (@{keyword async} >> K true) false
  -- Scan.optional (@{keyword mult} >> K true) false
  ) >> (fn (((((f,o1),t),o2),a),m) => Connection ((f, o1), (t, o2), a, m))

val controllerDeclParser =
  (containerDeclParser >> CtrlContainerDecl) ||
  (connectionParser >> ConnectionDecl) ||
  (((@{keyword "sref"} |-- name) -- (@{keyword "="} |-- name)) >> StmRefDecl) ||
  (((@{keyword "opref"} |-- name) -- (@{keyword "="} |-- name)) >> OpRefDecl)

val controllerParser =
  (name --
    (@{keyword "="} |--
      repeat1 controllerDeclParser
    )) >> mk_Controller;

val roboticPlatformParser =
  (name -- 
    (@{keyword "="} |--
      repeat1 containerDeclParser
    )) >> mk_Container;

val moduleDeclParser =
  (containerDeclParser >> RCModuleContainerDecl) ||
  (connectionParser >> ModConnectionDecl) ||
  (((@{keyword "cref"} |-- name) -- (@{keyword "="} |-- name)) >> CRefDecl) ||
  (((@{keyword "rref"} |-- name) -- (@{keyword "="} |-- name)) >> RRefDecl)

val moduleParser =
  (name --
    (@{keyword "="} |--
      repeat1 moduleDeclParser
    )) >> mk_RCModule;

val functionParser =
  (name -- parameterParser -- ($$$ "::" |-- typ) --
  repeat (@{keyword "precondition"} |-- term) --
  repeat1 (@{keyword "postcondition"} |-- term)) >> quint1 >> FuncDecl

end
\<close>

end