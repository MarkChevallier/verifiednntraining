
section \<open>Tensor Subtraction\<close>

(* Tensor subtraction is equivalent to tensor addition where the second argument is negated.
However, an explicit subtraction operation is implemented to prevent additional computation.
*)
theory Tensor_Minus
imports Tensor_Subtensor Tensor_Binary_Op Tensor_Plus Tensor_Scalar_Mult
begin

(* Problem: typeclass plus only has one zero element. If this is the empty tensor, other zero tensors cannot be of rank 0.*)

definition "vec_minus a b = vec_binop minus a b"

definition "minus_base a b = binop_base minus a b"

(*
lemma minus_base_code_gen[code abstract]: "Rep_tensor (minus_base A B) = ((if length_2 (vec A) \<le> length_2 (vec B) then (dims A) else (dims B))
 ,(vec_minus (vec A) (vec B)))"
  by (simp add: binop_base_code_eq minus_base_def vec_minus_def)
  *)

(* Which group do we require ? *)
instantiation tensor:: (group_add) minus
begin
  definition minus_def: "A - B = binop minus A B"
  instance ..
end

lemma minus_dim1[simp]: "dims A = dims B \<Longrightarrow> dims (A - B) = dims A" by (simp add: minus_def) 
lemma minus_dim2[simp]: "dims A = dims B \<Longrightarrow> dims (A - B) = dims B" by (simp add: minus_def) 
lemma minus_base: "dims A = dims B \<Longrightarrow> A - B = minus_base A B" by (simp add: binop_base minus_base_def minus_def) 


lemma subtensor_minus:
fixes A::"'a::group_add tensor" and B::"'a::group_add tensor"
assumes "i < hd (dims A)"
and "dims A = dims B"
and "dims A \<noteq> []"
shows "subtensor (A - B) i = subtensor A i - subtensor B i"
  by (metis assms(1) assms(2) assms(3) minus_def subtensor_binop)


lemma lookup_minus[simp]:
assumes "dims A = dims B"
and "is \<lhd> dims A"
shows "lookup (A - B) is = lookup A is - lookup B is"
  by (metis assms(1) assms(2) lookup_binop minus_def)


(* This is a nice example to put in the paper *)
theorem minus_eq_plus_smult:
  fixes A :: "'a::ring_1 tensor" and B :: "'a::ring_1 tensor"
  assumes "dims A = dims B"
  shows "A - B = A + ((-1) \<cdot> B)"
proof -
  from assms have "A + ((-1) \<cdot> B) = binop (\<lambda>x y. x + ((-1) * y)) A B" using 
      unop_binop_composition[where ?g="\<lambda>x. x" and ?h="(*) (-1)"] plus_def smult_def
    by (metis unop_ident)
  thus ?thesis using assms minus_def by auto 
qed


(*
lemma dims_tensor0[simp]: "dims (tensor0 d) = d"
and   vec_tensor0[simp]:  "vec (tensor0 d) = vec0 (prod_list_2 d)"
  unfolding tensor0_def vec0_def by simp_all

lemma
fixes A::"'a::group_add tensor"
shows tensor_add_0_right[simp]: "A - tensor0 (dims A) = A"
  unfolding minus_def plus_base_def dims_tensor0
   apply (simp_all)
    apply (rule tensor_lookup_eqI)
   apply (metis (no_types, lifting) prod_list_connection dims_tensor dims_tensor0 length_vec plus_dim2 vec_plus vec_tensor0)
  by (metis add.right_neutral prod_list_connection dims_tensor0 lookup_plus lookup_tensor0 plus_dim2 tensor_from_vec_simp vec_plus vec_tensor0)

lemma
fixes A::"'a::monoid_add tensor"
shows tensor_add_0_left[simp]:  "tensor0 (dims A) + A = A"
  unfolding plus_def plus_base_def dims_tensor0
   apply (simp_all)
    apply (rule tensor_lookup_eqI)
   apply (metis (no_types, lifting) prod_list_connection dims_tensor dims_tensor0 length_vec plus_dim2 vec_plus vec_tensor0)
  by (metis add.left_neutral prod_list_connection dims_tensor0 lookup_plus lookup_tensor0 plus_dim2 tensor_from_vec_simp vec_plus vec_tensor0)
*)

end