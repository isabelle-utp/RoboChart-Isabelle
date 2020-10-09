theory Type
  imports Term
begin

definition "constraint T t = (if T = dummyT then t else Const (STR ''_type_constraint_'') (T --> T) $ t)"

code_printing
  constant "constraint" \<rightharpoonup> (SML) "Type.constraint"

end