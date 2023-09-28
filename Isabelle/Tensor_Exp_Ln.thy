theory Tensor_Exp_Ln
  imports Tensor_Unary_Op
begin


definition tensor_exp::"real tensor \<Rightarrow> real tensor" where
    "tensor_exp A = unop exp A"

(* using type class ln is a really bad idea *)
definition tensor_ln::"'a::ln tensor \<Rightarrow> 'a tensor" where
    "tensor_ln A = unop ln A"


end