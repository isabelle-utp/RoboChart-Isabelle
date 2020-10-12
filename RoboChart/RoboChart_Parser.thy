section \<open> RoboChart Parser Library \<close>

theory RoboChart_Parser
  imports RoboChart_AST
  keywords 
    "var" "const" "clock" "opdecl" "terminates" 
    "broadcast" "event" "precondition" "postcondition"
    "uses" "provides" "requires"
    "state" "entry" "during" "exit" "probabilistic" "initial" "final" "junction"
    "transition" "frm" "to" "trigger" "probability" "condition" "action" "!" "?" "]>" "<["
begin

text \<open> We define a set of parser combinators for the RoboChart commands. These simply produce 
  elements of the AST, but do no semantic processing. \<close>

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

fun typParser ctx = ((!!! typ) >> read_typ ctx);

fun termParser ctx = ((!!! typ) >> parse_term ctx);

fun nameParser ctx = name -- ($$$ "::" |-- typParser ctx);

fun variableParser ctx = 
  (nameParser ctx -- (option (@{keyword "="} |-- termParser ctx)))
  >> variable;

fun parameterParser ctx = 
  @{keyword "("} |-- repeat (nameParser ctx --| @{keyword ","}) -- nameParser ctx --| @{keyword ")"}
  >> (fn (xs, x) => xs @ [x])

fun varDeclParser ctx = 
  (@{keyword "var"} >> (fn _ => VAR) || @{keyword "const"} >> (fn _ => CNST)) 
    -- repeat1 (variableParser ctx) >> VarDecl;
  
fun clockDeclParser _ =
  (@{keyword "clock"} |-- name) >> ClockDecl;

val terminatesParser =
  optional (@{keyword "["} |-- (@{keyword "terminates"} >> (fn _ => true)) --| @{keyword "]"}) false;

fun operationSigParser ctx =
  @{keyword "opdecl"} |-- (name -- parameterParser ctx -- terminatesParser) >> triple1 >> OpDecl

fun eventDecl ctx =
  (Scan.optional (@{keyword "broadcast"} >> (fn _ => true)) false 
  -- (@{keyword "event"} |-- repeat1 (nameParser ctx))) >> EventDecl

fun intfKeyParser ctx =
  varDeclParser ctx || clockDeclParser ctx || operationSigParser ctx || eventDecl ctx

fun interfaceParser ctx = 
  (name -- 
    (@{keyword "="} |--
      repeat1 (intfKeyParser ctx)
    )) >> mk_Interface;

val usesParser = @{keyword uses} |-- name >> UsesDecl;
val provParser = @{keyword provides} |-- name >> ProvDecl;
val reqParser = @{keyword requires} |-- name >> ReqDecl;

fun containerParser ctx =
  (intfKeyParser ctx >> IntfDecl) || usesParser || provParser || reqParser;

fun roboticPlatformParser ctx =
  (name -- 
    (@{keyword "="} |--
      repeat1 (containerParser ctx)
    )) >> mk_Container;
  
fun actionParser ctx =
  (@{keyword "entry"} |-- name >> Entry) || 
  (@{keyword "during"} |-- name >> During) || 
  (@{keyword "exit"} |-- name >> Exit);

fun nodeParser ctx =
  (@{keyword "initial"} |-- name >> Initial) ||
  (@{keyword "junction"} |-- name >> Junction) ||
  (@{keyword "final"} |-- name >> Final) ||
  (@{keyword "probabilistic"} |-- name >> ProbabilisticJunction) ||
  (@{keyword "state"} |-- name -- 
    ($$$ "[" |-- repeat (actionParser ctx) --| $$$ "]") >> (fn (n, a) => State (n, [], [], a)))

fun eventParser ctx = 
  ((name --| (@{keyword "?"} -- @{keyword "["})) -- name --| @{keyword "]"}) >> Input ||
  ((name --| (@{keyword "!"} -- @{keyword "["})) -- termParser ctx --| @{keyword "]"}) >> Output

fun triggerParser ctx =
  (@{keyword "trigger"}) |--
  option ($$$ "[" |-- termParser ctx --| $$$ "]>") --
  eventParser ctx --
  option ($$$ "<[" |-- termParser ctx --| $$$ "]")
  >> (fn ((bg, ev), ed) => Trigger_ext (bg, ev, NONE, [], ed, ()))

fun transitionParser ctx =
  (@{keyword "transition"} |-- name) --
    ($$$ "[" |--
      (@{keyword "frm"} |-- name) --
      (@{keyword "to"} |-- name) --
      option (triggerParser ctx)
     --| $$$ "]") >> (fn (n, ((s, t), tr)) => Named_ext (n, Transition_ext (s, t, tr, NONE, NONE, NONE, ())));


fun stateMachineBodyParser ctx = 
  (containerParser ctx >> StmContainerDecl) || (nodeParser ctx >> NodeDecl) || (transitionParser ctx >> TransitionDecl) ;

fun stateMachineDefParser ctx =
  (name --
    (@{keyword "="} |--
      repeat1 (stateMachineBodyParser ctx)
    ));

fun functionParser ctx =
  (name -- parameterParser ctx -- ($$$ "::" |-- typParser ctx) --
  optional (@{keyword "precondition"} |-- termParser ctx) @{term True} --
  (@{keyword "postcondition"} |-- termParser ctx)) >> quint1 >> Func

end
\<close>

end