theory Term
  imports Main
begin

(*
code_printing
    type_constructor "int" \<rightharpoonup> (SML) "int"
  | type_constructor "nat" \<rightharpoonup> (SML) "int"
  | constant "nth" \<rightharpoonup> (SML) "nth"
  | constant "one_class.one :: int" \<rightharpoonup> (SML) "1"
  | constant "Nil" \<rightharpoonup> (SML) "[]"
*)

no_notation
  implies  (infixr "-->" 25)

type_synonym indexname = "String.literal * integer"
type_synonym "class" = String.literal
type_synonym sort = "class list"

datatype "typ" =
  Type  "String.literal" "typ list" |
  TFree "String.literal" "sort" |
  TVar  "indexname" "sort"

definition "dummyT = Type (STR ''dummy'') []"
definition funT :: "typ \<Rightarrow> typ \<Rightarrow> typ" (infixr "-->" 25) where
"funT S T = Type (STR ''fun'') [S,T]"

code_printing
    type_constructor "typ" \<rightharpoonup> (SML) "typ"
  | constant "Type" \<rightharpoonup> (SML) "Term.Type (_, _)"
  | constant "TFree" \<rightharpoonup> (SML) "TFree (_, _)"
  | constant "TVar" \<rightharpoonup> (SML) "TVar (_, _)"
  | constant "dummyT" \<rightharpoonup> (SML) "Term.dummyT"
  | constant "funT" \<rightharpoonup> (SML) "_ --> _"

datatype "term" =
  Const String.literal "typ" |
  Free String.literal "typ" |
  Var indexname "typ" |
  Bound "integer" |
  Abs String.literal "typ" "term" |
  App "term" "term" (infixl "$" 200 )

definition "propT = Type (STR ''prop'') []"

fun aconv :: "term \<Rightarrow> term \<Rightarrow> bool" (infix "aconv" 50) where
  "(t1 $ u1) aconv (t2 $ u2) = (t1 aconv t2 \<and> u1 aconv u2)"
| "Abs _ T1 t1 aconv Abs _ T2 t2 = (t1 aconv t2 \<and> T1 = T2)"
| "a1 aconv a2 = (a1 = a2)"

lemma aconv_refl: "x aconv x"
  by (induct x, simp_all)

fun fastype_of1 :: "typ list \<Rightarrow> term \<Rightarrow> typ" where
"fastype_of1 Ts (f $ u) = 
   (case fastype_of1 Ts f of
      Type n (_ # T # []) \<Rightarrow> (if (n = STR ''fun'') then T else undefined) |
      _ \<Rightarrow> undefined)" |
"fastype_of1 _ (Const _ T) = T" |
"fastype_of1 _ (Free _ T) = T" |
"fastype_of1 Ts (Bound i) = Ts ! (nat (int_of_integer i))" |
"fastype_of1 _ (Var _ T) = T" |
"fastype_of1 Ts (Abs _ T u) = funT T (fastype_of1 (T # Ts) u)"

definition [simp]: "fastype_of t = fastype_of1 [] t"

definition "const n = Const n dummyT"

definition "free n = Free n dummyT"

consts lambda :: "term \<Rightarrow> term \<Rightarrow> term"

consts subst_free :: "(term \<times> term) list \<Rightarrow> term \<Rightarrow> term"

subsection \<open> Code Generation Axioms \<close>

code_printing
  type_constructor "term" \<rightharpoonup> (SML) "term"
  | constant "Const" \<rightharpoonup> (SML) "Const (_, _)"
  | constant "Free" \<rightharpoonup> (SML) "Free (_, _)"
  | constant "Var" \<rightharpoonup> (SML) "Var (_, _)"
  | constant "Bound" \<rightharpoonup> (SML) "Bound _"
  | constant "Abs" \<rightharpoonup> (SML) "Abs (_, _, _)"
  | constant "App" \<rightharpoonup> (SML) "_ $ _"
  | constant "propT" \<rightharpoonup> (SML) "propT"
  | constant "fastype_of" \<rightharpoonup> (SML) "Term.fastype'_of"
  | constant "subst_free" \<rightharpoonup> (SML) "Term.subst'_free"
  | constant "lambda" \<rightharpoonup> (SML) "Term.lambda"
  | constant "const" \<rightharpoonup> (SML) "Syntax.const"
  | constant "free" \<rightharpoonup> (SML) "Syntax.free"

end