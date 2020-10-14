section \<open> RoboChart Parser Library \<close>

theory RoboChart_Parser
  imports RoboChart_AST "HOL.Real"
  keywords 
    "var" "const" "clock" "opdecl" "terminates" 
    "broadcast" "event" "precondition" "postcondition"
    "uses" "provides" "requires"
    "state" "entry" "during" "exit" "probabilistic" "initial" "final" "junction"
    "transition" "frm" "to" "trigger" "probability" "condition" "action" "!" "?" "]>" "<["
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

val containerParser =
  (intfKeyParser >> IntfDecl) || usesParser || provParser || reqParser;

val roboticPlatformParser =
  (name -- 
    (@{keyword "="} |--
      repeat1 containerParser
    )) >> mk_Container;
  
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

val eventParser = 
  ((name --| (@{keyword "?"} -- @{keyword "["})) -- name --| @{keyword "]"}) >> Input ||
  ((name --| (@{keyword "!"} -- @{keyword "["})) -- term --| @{keyword "]"}) >> Output

val triggerParser =
  (@{keyword "trigger"}) |--
  option ($$$ "[" |-- term --| $$$ "]>") --
  eventParser --
  option ($$$ "<[" |-- term --| $$$ "]")
  >> (fn ((bg, ev), ed) => Trigger_ext (bg, ev, NONE, [], ed, ()))

val transitionParser =
  (@{keyword "transition"} |-- name) --
    ($$$ "[" |--
      (@{keyword "frm"} |-- name) --
      (@{keyword "to"} |-- name) --
      option triggerParser --
      option (@{keyword "probability"} |-- term) --
      option (@{keyword "condition"} |-- term) --
      option (@{keyword "action"} |-- term)
     --| $$$ "]") >> (fn (n, (((((s, t), tr), p), c), a)) => Named_ext (n, Transition_ext (s, t, tr, p, c, a, ())));

val stateMachineBodyParser = 
  (containerParser >> StmContainerDecl) || (nodeParser >> NodeDecl) || (transitionParser >> TransitionDecl) ;


val stateMachineDefParser =
  (name --
    (@{keyword "="} |--
      repeat1 stateMachineBodyParser
    ));

val functionParser =
  (name -- parameterParser -- ($$$ "::" |-- typ) --
  optional (@{keyword "precondition"} |-- term) "True" --
  (@{keyword "postcondition"} |-- term)) >> quint1 >> FuncDecl

end
\<close>

end