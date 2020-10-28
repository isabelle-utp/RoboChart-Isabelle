theory HOLogic
  imports Logic
begin

definition "boolN = STR ''HOL.bool''"
definition "boolT = Type boolN []"

definition "unitT = Type (STR ''Product_Type.unit'') []"

fun is_unitT :: "typ \<Rightarrow> bool" where
"is_unitT (Type t []) = (t = (STR ''Product_Type.unit''))" |
"is_unitT _ = False"

definition "unit = Const (STR ''Product_Type.Unity'') unitT"

fun is_unit :: "term \<Rightarrow> bool" where
"is_unit (Const c _) = (c = (STR ''Product_Type.Unity''))" |
"is_unit _ = False"

definition "mk_prodT T1 T2 = Type (STR ''Product_Type.prod'') [T1, T2]"

fun dest_prodT :: "typ \<Rightarrow> typ \<times> typ" where
"dest_prodT (Type n [T1, T2]) = (if (n = STR ''Product_Type.prod'') then (T1, T2) else undefined)" |
"dest_prodT _ = undefined"

definition "pair_const T1 T2 = Const (STR ''Product_Type.Pair'') (T1 --> T2 --> mk_prodT T1 T2)"

definition "mk_prod t1 t2 = 
  (let T1 = fastype_of t1; T2 = fastype_of t2 in pair_const T1 T2 $ t1 $ t2)"

fun dest_prod :: "term \<Rightarrow> term \<times> term" where
"dest_prod (Const n _ $ t1 $ t2) = (if (n = (STR ''Product_Type.Pair'')) then (t1, t2) else undefined)" |
"dest_prod _ = undefined"

definition mk_fst :: "term \<Rightarrow> term" where
  "mk_fst p =
   (let pT = fastype_of p in
     Const (STR ''Product_Type.prod.fst'') (funT pT (fst (dest_prodT pT))) $ p)"

definition mk_snd :: "term \<Rightarrow> term" where
  "mk_snd p =
   (let pT = fastype_of p in
     Const (STR ''Product_Type.prod.snd'') (funT pT (snd (dest_prodT pT))) $ p)"

definition case_prod_const :: "typ \<Rightarrow> typ \<Rightarrow> typ \<Rightarrow> term" where
  "case_prod_const A B C = 
   Const (STR ''Product_Type.prod.case_prod'') ((A --> B --> C) --> mk_prodT A B --> C)"

definition mk_case_prod :: "term \<Rightarrow> term" where
  "mk_case_prod t =
  (let T = Term.fastype_of t in
  case T of
    (Type f1 [A, Type f2 [B, C]]) =>
      if (f1 = STR ''fun'' \<and> f2 = STR ''fun'')
      then Const (STR ''Product_Type.prod.case_prod'') (T --> mk_prodT A B --> C) $ t
      else undefined
  | _ \<Rightarrow> undefined)" (* mk_case_prod: bad body type *)

(*Maps the type T1 * ... * Tn to [T1, ..., Tn], however nested*)

fun flatten_tupleT :: "typ \<Rightarrow> typ list" where
"flatten_tupleT (Type n [T1, T2]) = 
  (if (n = (STR ''Product_Type.prod'')) then flatten_tupleT T1 @ flatten_tupleT T2 else undefined)" |
"flatten_tupleT T = [T]"

consts tupled_lambda :: "term \<Rightarrow> term \<Rightarrow> term" (* TODO -- quite complex *)

definition "eq_const T = Const (STR ''HOL.eq'') (T --> T --> boolT)"

definition "mk_eq t u = eq_const (fastype_of t) $ t $ u"

consts mk_literal :: "String.literal \<Rightarrow> term"

consts mk_list :: "typ \<Rightarrow> term list \<Rightarrow> term"

definition "mk_None = const @{const_name None}"

definition "mk_Some t = const @{const_name Some} $ t"

fun mk_option :: "term option \<Rightarrow> term" where
"mk_option (Some t) = mk_Some t" | "mk_option None = mk_None"

(*
(*abstraction over nested tuples*)
fun tupled_lambda (x as Free _) b = lambda x b
  | tupled_lambda (x as Var _) b = lambda x b
  | tupled_lambda (Const ("Product_Type.Pair", _) $ u $ v) b =
      mk_case_prod (tupled_lambda u (tupled_lambda v b))
  | tupled_lambda (Const ("Product_Type.Unity", _)) b =
      Abs ("x", unitT, b)
  | tupled_lambda t _ = raise TERM ("tupled_lambda: bad tuple", [t]);
*)



(* tuples with right-fold structure *)

term last

fun mk_tupleT :: "typ list \<Rightarrow> typ" where
"mk_tupleT [] = unitT" |
"mk_tupleT Ts = foldr mk_prodT (butlast Ts) (last Ts)"

(*
fun strip_tupleT (Type ("Product_Type.unit", [])) = []
  | strip_tupleT (Type ("Product_Type.prod", [T1, T2])) = T1 :: strip_tupleT T2
  | strip_tupleT T = [T];
*)


fun mk_tuple :: "term list \<Rightarrow> term" where
"mk_tuple [] = unit" |
"mk_tuple ts = foldr mk_prod (butlast ts) (last ts)"



(*
fun strip_tuple (Const ("Product_Type.Unity", _)) = []
  | strip_tuple (Const ("Product_Type.Pair", _) $ t1 $ t2) = t1 :: strip_tuple t2
  | strip_tuple t = [t];

*)


subsection \<open> Tests \<close>

code_reflect MyHOLogic
  functions mk_fst mk_snd mk_tuple

ML \<open>
  MyHOLogic.mk_snd @{term "(x :: nat, y)"} = HOLogic.mk_snd @{term "(x :: nat, y)"};
  MyHOLogic.mk_tuple [@{term "x :: int"}, @{term "y :: string"}] = HOLogic.mk_tuple [@{term "x :: int"}, @{term "y :: string"}];
\<close>

subsection \<open> Code Generation Axioms \<close>

code_printing
  constant "tupled_lambda" \<rightharpoonup> (SML) "HOLogic.tupled'_lambda" |
  constant "mk_tuple" \<rightharpoonup> (SML) "HOLogic.mk'_tuple" |
  constant "mk_eq" \<rightharpoonup> (SML) "HOLogic.mk'_eq (_, _)" |
  constant "mk_literal" \<rightharpoonup> (SML) "HOLogic.mk'_literal" |
  constant "mk_list" \<rightharpoonup> (SML) "HOLogic.mk'_list"

end