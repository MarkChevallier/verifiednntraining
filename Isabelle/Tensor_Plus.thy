(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Addition\<close>

theory Tensor_Plus
imports Tensor_Subtensor Tensor_Binary_Op Tensor_Constants
begin

(* Problem: typeclass plus only has one zero element. If this is the empty tensor, other zero tensors cannot be of rank 0.*)


(* THIS IS SLOW *)
definition "vec_plus a b = vec_binop plus a b"


(* Need to define a valid tensor *)
definition plus_base::"'a::semigroup_add tensor \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor"
  where "plus_base A B = binop_base plus A B"


instantiation tensor:: (semigroup_add) plus
begin
  definition plus_def: "A + B = binop plus A B"
  instance ..
end


lemma vec_plus_equiv[simp]:
  "binop_base plus A B =
tensor_from_vec_list (if IArray.length (vec A) \<le> IArray.length (vec B) then dims A else dims B) (vec_plus (vec_list A) (vec_list B))"
  by (simp add: binop_base_def vec_plus_def)


(* This function relies on tensor_replicate_right_binop *)
(* This function demonstrates why the generalised formalisation makes some proofs easier *)
lemma
fixes A::"'a::monoid_add tensor"
shows tensor_add_0_right[simp]: "A + tensor0 (dims A) = A"
proof -
  have "A + tensor0 (dims A) = binop (\<lambda>a b. a + b) A (tensor0 (dims A))" by (simp add: binop_def plus_def)
  thus ?thesis by (simp add: tensor0_def)
qed

(*

lemma
fixes A::"'a::monoid_add tensor"
shows tensor_add_0_right[simp]: "A + tensor0 (dims A) = A"
  unfolding plus_def plus_base_def dims_tensor0
   apply (simp_all)
    apply (rule tensor_lookup_eqI)
   apply (metis (no_types, lifting) prod_list_connection dims_tensor dims_tensor0 length_vec plus_dim2 vec_plus vec_tensor0)
  by (metis add.right_neutral prod_list_connection dims_tensor0 lookup_plus lookup_tensor0 plus_dim2 tensor_from_vec_simp vec_plus vec_tensor0)


*)


lemma plus_dim1[simp]: "dims A = dims B \<Longrightarrow> dims (A + B) = dims A" unfolding plus_def binop_base_def
  by simp
lemma plus_dim2[simp]: "dims A = dims B \<Longrightarrow> dims (A + B) = dims B" using plus_dim1 by simp
lemma plus_base: "dims A = dims B \<Longrightarrow> A + B = binop_base plus A B" unfolding plus_def binop_def by simp

lemma fixed_length_sublist_plus:
assumes "length xs1 = c * l" "length xs2 = c * l" "i < c"
shows "fixed_length_sublist (vec_plus xs1 xs2) l i
          = vec_plus (fixed_length_sublist xs1 l i) (fixed_length_sublist xs2 l i)"
  using fixed_length_sublist_binop vec_plus_def by (metis assms(1) assms(2) assms(3)) 

lemma vec_plus[simp]:
assumes "dims A = dims B"
shows "vec_list (A+B) = vec_plus (vec_list A) (vec_list B)"
  by (simp add: assms plus_def vec_plus_def)

lemma subtensor_plus:
fixes A::"'a::semigroup_add tensor" and B::"'a::semigroup_add tensor"
assumes "i < hd (dims A)"
and "dims A = dims B"
and "dims A \<noteq> []"
shows "subtensor (A + B) i = subtensor A i + subtensor B i"
using assms subtensor_binop by (metis plus_def)

lemma lookup_plus[simp]:
assumes "dims A = dims B"
and "is \<lhd> dims A"
shows "lookup (A + B) is = lookup A is + lookup B is"
  using assms lookup_binop plus_def by metis

lemma plus_assoc:
assumes dimsA:"dims A = ds" and dimsB:"dims B = ds" and dimsC:"dims C = ds"
shows "(A + B) + C = A + (B + C)"
by (rule tensor_lookup_eqI; simp add: dimsA dimsB dimsC add.assoc)+

lemma tensor_comm[simp]:
fixes A::"'a::ab_semigroup_add tensor"
shows "A + B = B + A"
proof (cases "dims A = dims B")
  case True
  then show ?thesis unfolding plus_def binop_base_def
    using add.commute lookup_plus[OF True] plus_dim1[OF True] tensor_lookup_eqI[OF True] vec_plus[OF True]
    by (metis binop_dim1 lookup_binop tensor_lookup_eqI)
next
  case False
  then show ?thesis unfolding plus_def binop_def by simp
qed


(* Much shorter now *)
lemma
fixes A::"'a::monoid_add tensor"
shows tensor_add_0_left[simp]: "(tensor0 (dims A)) + A = A"
proof -
  have "tensor0 (dims A) + A = binop (\<lambda>a b. a + b) (tensor0 (dims A)) A" by (simp add: binop_def plus_def)
  thus ?thesis by (simp add: tensor0_def tensor_replicate_left_binop)
qed


definition listsum::"nat list \<Rightarrow> 'a::monoid_add tensor list \<Rightarrow> 'a tensor" where
"listsum ds As = foldr (+) As (tensor0 ds)"

definition listsum'::"'a::monoid_add tensor list \<Rightarrow> 'a tensor" where
"listsum' As = listsum (dims (hd As)) As"

lemma listsum_Nil: "listsum ds [] = tensor0 ds" by (simp add: Tensor_Plus.listsum_def)

lemma listsum_one: "listsum (dims A) [A] = A" unfolding listsum_def by simp

lemma listsum_Cons: "listsum ds (A # As) = A + listsum ds As"
  unfolding listsum_def by auto

lemma listsum_dims:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
shows "dims (listsum ds As) = ds"
using assms proof (induction As)
  case Nil
  then show ?case by (metis tensor0_def dims_tensor_replicate listsum_Nil)
next
  case (Cons A As)
  then show ?case using listsum_Cons
    by (metis list.set_intros(1) list.set_intros(2) plus_dim2)
qed


lemma subtensor_listsum:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
and "ds \<noteq> []" and "i<hd ds"
shows "subtensor (listsum ds As) i = listsum (tl ds) (map (\<lambda>A. subtensor A i) As)"
using assms proof (induction As)
  case Nil
  then show ?case using tensor0_def assms(2) assms(3) subtensor_tensor_replicate
    by (metis list.simps(8) listsum_Nil) 
next
  case (Cons A As)
  then show ?case
    by (smt (verit, best) list.set_intros(1) list.set_intros(2) list.simps(9) listsum_Cons listsum_dims subtensor_plus) 
qed


lemma listsum0:
assumes "\<And>A. A\<in>set As \<Longrightarrow> A = tensor0 ds"
shows "listsum ds As = tensor0 ds"
using assms proof (induction As)
  case Nil
  show ?case by (simp add: listsum_Nil)
next
  case Cons
  then show ?case using listsum_Cons
    by (metis dims_tensor_replicate tensor0_def list.set_intros(1) set_subset_Cons subsetCE tensor_add_0_right)
qed

lemma listsum_all_0_but_one:
assumes "\<And>i. i\<noteq>j \<Longrightarrow> i<length As \<Longrightarrow> As!i = tensor0 ds"
and "dims (As!j) = ds"
and "j < length As"
shows "listsum ds As = As!j"
using assms proof (induction As arbitrary:j)
  case Nil
  then show ?case by auto
next
  case (Cons A As j)
  then show ?case
  proof (cases j)
    case 0
    then have "\<And>i. i < length As \<Longrightarrow> As ! i = tensor0 ds" using Cons using Suc_less_eq length_Cons list.sel(3) nat.simps(3) nth_tl by fastforce
    then have "listsum ds As = tensor0 ds" using listsum0 by (metis in_set_conv_nth)
    then show ?thesis by (metis "0" Cons.prems(2) listsum_Cons nth_Cons_0 tensor_add_0_right)
  next
    case (Suc j')
    then have "listsum ds As = As!j'" by (metis (no_types, lifting) Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(3) Suc_less_eq length_Cons less_Suc_eq list.sel(3) not_less_eq nth_tl)
    then show ?thesis by (metis Cons.prems(1) Cons.prems(2) Suc length_greater_0_conv list.simps(3) listsum_Cons nat.simps(3) nth_Cons_0 nth_Cons_Suc tensor_add_0_left)
  qed
qed

lemma lookup_listsum:
assumes "is \<lhd> ds"
and "\<And>A. A \<in> set As \<Longrightarrow> dims A = ds"
shows "lookup (listsum ds As) is = (\<Sum>A\<leftarrow>As. lookup A is)"
using assms proof (induction As)
  case Nil
  then show ?case by (simp add: assms(1) listsum_Nil lookup_tensor_replicate tensor0_def)
next
  case (Cons A As)
  then show ?case by (simp add: listsum_Cons list.set_intros listsum_dims)
qed


end