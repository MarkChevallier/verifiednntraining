(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Scalar Power\<close>

theory Tensor_Pow
imports Tensor_Plus  Tensor_Unary_Op
begin


definition tensor_powr::"'a tensor \<Rightarrow> 'a::ln \<Rightarrow> 'a tensor" (infixl "**" 70) where
"tensor_powr A \<alpha> = unop (\<lambda>x. x powr \<alpha>) A"

lemma powr_subtensor:
assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "tensor_powr (subtensor A i) \<alpha> = subtensor (tensor_powr A \<alpha>) i"
  by (metis assms tensor_powr_def unop_subtensor)

lemma lookup_powr:
assumes "is \<lhd> dims A"
shows "lookup (tensor_powr A \<alpha>) is = (lookup A is) powr \<alpha>"
  using assms lookup_unop tensor_powr_def[where ?\<alpha>="\<alpha>"] by simp

definition tensor_sqr::"'a::semigroup_mult tensor \<Rightarrow> 'a tensor" where
"tensor_sqr A = unop (\<lambda>x. x*x) A"

(*
find_theorems "(powr)" 1

thm less_le
lemma tensor_sqr_tensor_pow:
  "tensor_sqr A = tensor_powr A 2"
proof -
  fix x::real assume "x>0"
  have "x*x = x powr 2"
    by (metis \<open>0 < x\<close> less_le power2_eq_square powr_numeral) 
qed
*)

end