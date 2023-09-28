theory Tensor_Constants
  imports Complex_Main Tensor Tensor_Subtensor
begin


definition "vec0 n = replicate n 0"

definition "vec1 n = replicate n 1"


definition tensor_replicate::"nat list \<Rightarrow> 'a \<Rightarrow> 'a tensor" where
"tensor_replicate ds a = tensor_from_vec_list ds (replicate (prod_list ds) a)"

lemma tensor_replicate_valid[code]:
  "Rep_tensor (tensor_replicate ds a) = (ds, IArray (replicate (prod_list ds) a))"
  by (simp add: invertability_condition tensor_from_vec_list_def tensor_replicate_def)


lemma dims_tensor_replicate[simp]:
  shows "dims (tensor_replicate ds a) = ds"
  by (simp add: tensor_replicate_def)

lemma vec_list_tensor_replicate[simp]:
  shows "vec_list (tensor_replicate ds a) = replicate (prod_list ds) a"
  by (simp add: tensor_replicate_def)

lemma lookup_imp_tensor_replicate:
  assumes "is \<lhd> ds"
  shows "lookup_imp (tensor_replicate ds a) is = a"
  by (metis IArray.sub_def assms dims_tensor_replicate flattened_index_lt_prod_list lookup_imp_def
      nth_replicate vec_list_tensor_replicate vec_list_vec)

lemma lookup_tensor_replicate:
  assumes "is \<lhd> ds"
  shows "lookup (tensor_replicate ds a) is = a"
  by (simp add: assms lookup_equiv_lookup_imp lookup_imp_tensor_replicate)

lemma subtensor_tensor_replicate:
assumes "ds \<noteq> []" and "i<hd ds"
shows "subtensor (tensor_replicate ds a) i = tensor_replicate (tl ds) a"
proof (rule tensor_lookup_eqI)
  show 1:"dims (subtensor (tensor_replicate ds a) i) = dims (tensor_replicate (tl ds) a)"
    by (metis assms(1) assms(2) dims_subtensor dims_tensor_replicate) 
  fix "is" assume "is \<lhd> dims (subtensor (tensor_replicate ds a) i)"
  then have "i # is \<lhd> dims (tensor_replicate ds a)" using assms(1) assms(2) valid_index.Cons
    using "1" by fastforce 
  then show "lookup (subtensor (tensor_replicate ds a) i) is = lookup (tensor_replicate (tl ds) a) is"
    using lookup_subtensor1 1 \<open>is \<lhd> dims (subtensor (tensor_replicate ds a) i)\<close> dims_tensor_replicate lookup_tensor_replicate
    by metis
qed

definition tensor0::"nat list \<Rightarrow> 'a::zero tensor" where
"tensor0 d = tensor_replicate d 0"

definition tensor1::"nat list \<Rightarrow> 'a::{zero,one} tensor" where
"tensor1 d = tensor_replicate d 1"


lemma tensor1_lookup_imp:
  assumes "is \<lhd> ds"
  shows "lookup_imp (tensor1 ds) is = 1"
  by (simp add: assms tensor1_def lookup_imp_tensor_replicate)


lemma tensor0_lookup_imp:
  assumes "is \<lhd> ds"
  shows "lookup_imp (tensor0 ds) is = 0"
  by (simp add: assms tensor0_def lookup_imp_tensor_replicate)


end