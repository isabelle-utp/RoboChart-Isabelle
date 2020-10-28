theory Logic
  imports Syntax 
begin

definition "mk_equals t u = 
  (let T = Term.fastype_of t
   in Const (STR ''Pure.eq'') (T --> T --> propT) $ t $ u)"

code_printing
  constant "mk_equals" \<rightharpoonup> (SML) "Logic.mk'_equals (_, _)"

end