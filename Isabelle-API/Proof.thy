theory Proof
  imports Term
begin

typedecl "context"

code_printing
  type_constructor "context" \<rightharpoonup> (SML) "Proof.context"

end