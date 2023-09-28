theory Lequal_Nequal
  imports Tensor_Plus Tensor_Exp_Ln Max_Min Lequal Tensor_Mul
  Tensor_Minus Tensor_Scalar_Mult

begin


definition tensor_Max_gamma :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor  \<Rightarrow> real tensor"
  where "tensor_Max_gamma \<gamma> A B = binop (Max_gamma \<gamma>) A B"

definition tensor_Min_gamma :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Min_gamma \<gamma> A B = binop (Min_gamma \<gamma>) A B"


definition tensor_Lequal_gamma :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Lequal_gamma \<gamma> A B = binop (Lequal_gamma \<gamma>) A B"


(*fun Max_gamma :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Max_gamma \<gamma> a b = (if \<gamma> \<le> 0 then max a b 
    else \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>)))" *)
definition tensor_Min_gamma_sep :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Min_gamma_sep \<gamma> A B = (if \<gamma>\<le>0 then (binop min A B) else ((-\<gamma>) \<cdot> tensor_ln (tensor_exp (A \<div> (-\<gamma>)) + tensor_exp (B \<div> (-\<gamma>)))))"

definition tensor_Max_gamma_sep :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Max_gamma_sep \<gamma> A B = (if \<gamma>\<le>0 then (binop max A B) else (\<gamma> \<cdot> tensor_ln (tensor_exp (A \<div> \<gamma>) + tensor_exp (B \<div> \<gamma>))))"

definition tensor_Lequal_gamma_sep :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Lequal_gamma_sep \<gamma> A B = tensor_Max_gamma_sep \<gamma> (A-B) (tensor0 (dims A))"


lemma tensor_Max_gamma_gt0[simp]:
  assumes "\<gamma> > 0"
  and "dims A = dims B"
shows "tensor_Max_gamma \<gamma> A B = binop (\<lambda>a b. \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>))) A B"
proof -
  from assms have "Max_gamma \<gamma> = (\<lambda>a b. \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>)))" by fastforce
  thus ?thesis using tensor_Max_gamma_def by fastforce 
qed

(* This was done using unop/binop composition theorems *)
lemma tensor_Max_gamma_sep_equiv:
  assumes "dims A = dims B"
  shows "tensor_Max_gamma \<gamma> A B = tensor_Max_gamma_sep \<gamma> A B"
proof (cases "\<gamma>\<le>0")
  case A: True
  hence "Max_gamma \<gamma> = (\<lambda>a b. max a b)" using Max_gamma.simps by presburger
  from this and A show ?thesis using tensor_Max_gamma_def tensor_Max_gamma_sep_def by presburger 
next
  case False
  hence B: "\<gamma> > 0" by simp
  have "\<And>C. tensor_exp (C \<div> \<gamma>) = unop (\<lambda>x. exp (x/\<gamma>)) C" using unop_composition
    by (simp add: comp_def tensor_exp_def sdiv_def)                   
  hence "binop (\<lambda>a b. exp (a/\<gamma>) + exp (b/\<gamma>)) A B = tensor_exp (A \<div> \<gamma>) + tensor_exp (B \<div> \<gamma>)" 
    using assms by (metis plus_def unop_binop_composition)
  moreover from assms have "\<gamma> \<cdot> (tensor_ln (binop (\<lambda>a b. exp (a/\<gamma>) + exp (b/\<gamma>)) A B)) = binop (\<lambda>a b. (\<gamma> * (ln (exp (a/\<gamma>) + exp (b/\<gamma>))))) A B"
    by (simp add: tensor_ln_def smult_def binop_unop_composition) 
  ultimately have "tensor_Max_gamma_sep \<gamma> A B = binop (\<lambda>a b. (\<gamma> * (ln (exp (a/\<gamma>) + exp (b/\<gamma>))))) A B" using B 
    by (simp add: tensor_Max_gamma_sep_def) 
  thus ?thesis using assms B by simp
qed


lemma tensor_Min_gamma_gt0[simp]:
  assumes "\<gamma> > 0"
  and "dims A = dims B"
shows "tensor_Min_gamma \<gamma> A B = binop (\<lambda>a b. (-\<gamma>) * ln (exp (-a/\<gamma>) + exp (-b/\<gamma>))) A B"
proof -
  from assms have "Min_gamma \<gamma> = (\<lambda>a b. (-\<gamma>) * ln (exp (-a/\<gamma>) + exp (-b/\<gamma>)))" by fastforce
  thus ?thesis using tensor_Min_gamma_def by fastforce 
qed

lemma tensor_Min_gamma_sep_equiv:
  assumes "dims A = dims B"
  shows "tensor_Min_gamma \<gamma> A B = tensor_Min_gamma_sep \<gamma> A B"
proof (cases "\<gamma>\<le>0")
  case A: True
  hence "Min_gamma \<gamma> = (\<lambda>a b. min a b)" using Min_gamma.simps by presburger
  from this and A show ?thesis using tensor_Min_gamma_def tensor_Min_gamma_sep_def by presburger 
next
  case False
  hence B: "\<gamma> > 0" by simp
  have "\<And>C. tensor_exp (C \<div> (-\<gamma>)) = unop (\<lambda>x. exp (-x/\<gamma>)) C" using unop_composition
    by (simp add: comp_def tensor_exp_def sdiv_def)                   
  hence "binop (\<lambda>a b. exp (-a/\<gamma>) + exp (-b/\<gamma>)) A B = tensor_exp (A \<div> (-\<gamma>)) + tensor_exp (B \<div> (-\<gamma>))" 
    using assms by (metis plus_def unop_binop_composition)
  moreover from assms have "(-\<gamma>) \<cdot> (tensor_ln (binop (\<lambda>a b. exp (-a/\<gamma>) + exp (-b/\<gamma>)) A B)) = binop (\<lambda>a b. (-\<gamma>)*(ln (exp (-a/\<gamma>) + exp (-b/\<gamma>)))) A B"
    by (simp add: tensor_ln_def smult_def binop_unop_composition) 
  ultimately have "tensor_Min_gamma_sep \<gamma> A B = binop (\<lambda>a b. ((-\<gamma>) * (ln (exp (-a/\<gamma>) + exp (-b/\<gamma>))))) A B" using B
    by (simp add: tensor_Min_gamma_sep_def algebra_simps)
  thus ?thesis using assms B by simp
qed


(* A pretty cool lemma *)
lemma tensor_Lequal_gamma_sep_equiv:
  assumes "dims A = dims B"
  shows "tensor_Lequal_gamma \<gamma> A B = tensor_Lequal_gamma_sep \<gamma> A B"
proof -
  have "tensor_Lequal_gamma \<gamma> A B = binop (\<lambda>a b. Max_gamma \<gamma> (a-b) 0) A B" using Lequal_gamma.simps Rect_gamma.simps
     tensor_Lequal_gamma_def by presburger
  hence "tensor_Lequal_gamma \<gamma> A B = unop (\<lambda>x. Max_gamma \<gamma> x 0) (A-B)"
    using assms minus_def[where ?A="A"] by (simp add: binop_unop_composition)
  hence "tensor_Lequal_gamma \<gamma> A B = binop (Max_gamma \<gamma>) (A-B) (tensor0 (dims (A-B)))" using
      tensor_replicate_right_binop tensor0_def by metis
  moreover have "dims (A - B) = dims (tensor0 (dims A))" using assms minus_def binop_dim1 tensor0_def dims_tensor_replicate by metis
  ultimately show ?thesis using assms minus_def binop_dim1 tensor_Max_gamma_def tensor_Max_gamma_sep_equiv
      tensor_Lequal_gamma_sep_def by metis
qed


(* This definition was done by performing the operation elementwise over the whole tensor *)
(* This should return the derivative of the element-wise loss w.r.t. the elements of the tensor *)
definition tensor_dLequal_gamma_ds :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_dLequal_gamma_ds \<gamma> A dA B dB = (binop (\<lambda>a b. dRect_gamma_dx \<gamma> (a-b)) A B) * (dA - dB)"


end