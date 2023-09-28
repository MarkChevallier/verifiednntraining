(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Scalar Multiplication\<close>

theory Tensor_Scalar_Mult
imports Tensor_Plus Tensor_Subtensor
begin

definition vec_smult::"'a::ring \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"vec_smult \<alpha> xs = map ((*) \<alpha>) xs"

lemma vec_smult0: "vec_smult 0 as = vec0 (length as)"
  by (induction as; auto simp add:vec0_def vec_smult_def)

lemma vec_smult_distr_right:
shows "vec_smult (\<alpha> + \<beta>) as = vec_plus (vec_smult \<alpha> as) (vec_smult \<beta> as)"
  unfolding vec_smult_def vec_plus_def vec_binop_def
  by (induction as; simp add: distrib_right)

lemma vec_smult_Cons:
shows "vec_smult \<alpha> (a # as) = (\<alpha> * a) # vec_smult \<alpha> as" by (simp add: vec_smult_def)

lemma vec_plus_Cons:
shows "vec_plus (a # as) (b # bs) = (a+b) # vec_plus as bs" by (simp add: vec_plus_def vec_binop_def)

lemma vec_smult_distr_left:
assumes "length as = length bs"
shows "vec_smult \<alpha> (vec_plus as bs) = vec_plus (vec_smult \<alpha> as) (vec_smult \<alpha> bs)"
using assms proof (induction as arbitrary:bs)
  case Nil
  then show ?case unfolding vec_smult_def vec_plus_def vec_binop_def by simp
next
  case (Cons a as')
  then obtain b bs' where "bs = b # bs'" by (metis Suc_length_conv)
  then have 0:"vec_smult \<alpha> (vec_plus (a # as') bs) = (\<alpha>*(a+b)) # vec_smult \<alpha> (vec_plus as' bs')"
    unfolding vec_smult_def vec_plus_def vec_binop_def using Cons.IH[of bs'] by simp
  have "length bs' = length as'" using Cons.prems \<open>bs = b # bs'\<close> by auto
  then show ?case unfolding 0 unfolding  \<open>bs = b # bs'\<close> vec_smult_Cons vec_plus_Cons
    by (simp add: Cons.IH distrib_left)
qed

lemma length_vec_smult: "length (vec_smult \<alpha> v) = length v" unfolding vec_smult_def by simp

definition smult::"'a::ring \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor" (infixl "\<cdot>" 70) where
"smult \<alpha> A = unop ((*) \<alpha>) A"

lemma tensor_smult0: fixes A::"'a::ring tensor"
  shows "0 \<cdot> A = tensor0 (dims A)"
  by (metis (no_types, lifting) dims_tensor_replicate dims_unop lookup_tensor_replicate
      lookup_unop mult_zero_left smult_def tensor0_def tensor_lookup_eqI) 

lemma dims_smult[simp]:"dims (\<alpha> \<cdot> A) = dims A"
  by (simp add: smult_def unop_def unop_list_def)

lemma vec_smult[simp]: "vec_list (\<alpha> \<cdot> A) = map ((*) \<alpha>) (vec_list A)"
  by (simp add: smult_def unop_def unop_list_def)
  
lemma tensor_smult_distr_right: "(\<alpha> + \<beta>) \<cdot> A = \<alpha> \<cdot> A  + \<beta> \<cdot> A"
  unfolding plus_def binop_def
  by (smt (verit) dims_unop smult_def unop_def unop_list_def vec_plus_equiv vec_smult vec_smult_def vec_smult_distr_right) 

lemma tensor_smult_distr_left: "dims A = dims B \<Longrightarrow> \<alpha> \<cdot> (A + B) = \<alpha> \<cdot> A  + \<alpha> \<cdot> B"
proof -
  assume a1: "dims A = dims B"
  then have f2: "length (vec_plus (vec_list A) (vec_list B)) = length (vec_list A)"
    by (simp add: vec_plus_def)
  have f3: "dims (tensor_from_vec_list (dims B) (vec_smult \<alpha> (vec_list A))) = dims B"
    using a1 by (simp add: vec_smult_def)
  have f4: "vec_list (\<alpha> \<cdot> A) = vec_smult \<alpha> (vec_list A)"
    by (simp add: vec_smult_def)
  have "length (vec_smult \<alpha> (vec_list B)) = length (vec_list B)"
    by (simp add: vec_smult_def)
  then show ?thesis
    unfolding plus_def plus_base_def using f4 f3 f2 a1
    by (metis (no_types, lifting) binop_dim1 dims_smult tensor_dim_vec_list_invariant
        tensor_from_vec_list_simp vec_binop vec_plus_def vec_smult vec_smult_def vec_smult_distr_left) 
qed

lemma smult_fixed_length_sublist:
assumes "length xs = l * c" "i<c"
shows "fixed_length_sublist (vec_smult \<alpha> xs) l i = vec_smult \<alpha> (fixed_length_sublist xs l i)"
  using assms by (metis unop_fixed_length_sublist vec_smult_def) 


lemma smult_subtensor:
assumes "dims A \<noteq> []" "i < hd (dims A)"
shows "\<alpha> \<cdot> subtensor A i = subtensor (\<alpha> \<cdot> A) i"
  using assms by (metis smult_def unop_subtensor) 

lemma lookup_smult:
assumes "is \<lhd> dims A"
shows "lookup (\<alpha> \<cdot> A) is = \<alpha> * lookup A is"
  using assms by (metis smult_def lookup_unop)

lemma tensor_smult_assoc:
fixes A::"'a::ring tensor"
shows "\<alpha> \<cdot> (\<beta> \<cdot> A) = (\<alpha> * \<beta>) \<cdot> A"
  by (rule tensor_lookup_eqI, simp, metis lookup_smult dims_smult mult.assoc)


section \<open>Scalar Division\<close>

definition sdiv::"'a::division_ring tensor \<Rightarrow> 'a \<Rightarrow> 'a tensor" (infixl "\<div>" 70) where
    "sdiv A \<alpha> = unop (\<lambda>x. x / \<alpha>) A"


(* division_ring is needed for sdiv, and ab_semigroup_mult is needed for the commutative property of * *)
lemma sdiv_eq_smult:
  fixes A :: "'a::{ab_semigroup_mult,division_ring} tensor"
  shows "sdiv A \<alpha> = smult (1 / \<alpha>) A"
proof -
  have "sdiv A \<alpha> = unop (\<lambda>x. (1/\<alpha>) * x) A"
    by (simp add: mult.commute sdiv_def) 
  thus ?thesis
    by (simp add: smult_def)
qed

end