(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Subtensors\<close>

theory Tensor_Subtensor
imports Tensor
begin

(* WHEN WRITING THE DISS *)

(*
It is important to talk about the edge cases for the subtensor function and where things break down.
In particular, what does it mean when a tensor has dims = [] or i is out of bounds.

Theorem proving makes sure that the equivalency of these functions is adequately established.

*)

(* Legacy definition *)
definition subtensor_legacy::"'a tensor \<Rightarrow> nat \<Rightarrow> 'a tensor" where
  "subtensor_legacy A i = tensor_from_vec_list (tl (dims A)) (fixed_length_sublist (vec_list A) (prod_list (tl (dims A))) i)"

(* Modified version to work with code generation *)
definition subtensor_base::"'a tensor \<Rightarrow> nat \<Rightarrow> 'a tensor" where
  "subtensor_base A i = (if (dims A) \<noteq> [] \<and> (i < hd (dims A)) then
  (tensor_from_vec_list (tl (dims A)) (fixed_length_sublist (vec_list A) (prod_list (tl (dims A))) i)) else A)"

definition subtensor_base_imp::"'a tensor \<Rightarrow> nat \<Rightarrow> 'a tensor" where
  "subtensor_base_imp A i = (if (dims A) \<noteq> [] \<and> (i < hd (dims A)) then
  (tensor_from_vec (tl (dims A)) (fixed_length_sublist_imp (vec A) (prod_list (tl (dims A))) i)) else A)"

definition subtensor::"'a tensor \<Rightarrow> nat \<Rightarrow> 'a tensor" where
  "subtensor A i = (if (dims A) \<noteq> [] \<and> (i < hd (dims A)) then subtensor_base A i else undefined)"

lemma subtensor_condition_fls_imp:
  assumes "(dims A) \<noteq> []" and "i < hd (dims A)"
  shows "(prod_list (tl (dims A))) * (i + 1) \<le> length (vec_list A)"
  by (metis Suc_leI add.left_commute add.right_neutral assms(1) assms(2) list.collapse mult.commute mult_le_cancel2 plus_1_eq_Suc prod_list_cons tensor_dim_vec_list_invariant)

lemma subtensor_base_imp_equiv[simp,code]:
"subtensor_base A i = subtensor_base_imp A i"
proof (cases "(dims A) \<noteq> []" and "i < hd (dims A)")
  case True
  then show ?thesis unfolding subtensor_base_def subtensor_base_imp_def 
    using subtensor_condition_fls_imp fixed_length_sublist_equiv
    by (metis tensor_from_vec_def tensor_from_vec_list_def vec_vec_list)
next
  case False
  then show ?thesis by (simp add: subtensor_base_def subtensor_base_imp_def) 
qed

lemma subtensor_equiv_subtensor_legacy[simp]:
  assumes "dims A \<noteq> []" and "i < hd (dims A)"
  shows "subtensor A i = subtensor_legacy A i"
  using assms 
  by (metis subtensor_base_def subtensor_def subtensor_legacy_def)

(* This function will not be efficient for code generation *)
definition subtensor_split :: "'a tensor \<Rightarrow> 'a tensor list" where
  "subtensor_split A = map (subtensor_base A) [0..< hd (dims A)]"

(* Added by Matt *)
definition subtensor_split_imp :: "'a tensor \<Rightarrow> 'a tensor list" where
  "subtensor_split_imp A = map (subtensor_base_imp A) [0..< hd (dims A)]"

lemma subtensor_split_imp_equiv[simp,code]:
"subtensor_split A = subtensor_split_imp A"
  by (simp add: subtensor_split_def subtensor_split_imp_def)

thm IArray.of_fun_def
(*
IArray.of_fun ?f ?n = IArray (map ?f [0..<?n])
*)



definition subtensor_combine::"nat list \<Rightarrow> 'a tensor list \<Rightarrow> 'a tensor" where
  "subtensor_combine ds As = tensor_from_vec_list (length As # ds) (concat (map vec_list As))"

definition subtensor_combine_2::"nat list \<Rightarrow> 'a tensor list \<Rightarrow> 'a tensor" where
  "subtensor_combine_2 ds As = tensor_from_vec_list (length As # ds) (concat (map (\<lambda>t. take (prod_list ds) (vec_list t)) As))"

lemma take_prod_list_redundant:
  assumes "dims A = ds"
  shows "take (prod_list ds) (vec_list A) = vec_list A"
  using assms by simp

lemma subtensor_combine_definition_equivalence:
  assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
  shows "subtensor_combine ds As = subtensor_combine_2 ds As"
  by (metis (no_types, lifting) assms map_ext subtensor_combine_2_def subtensor_combine_def take_prod_list_redundant)

lemma length_fixed_length_sublist[simp]:
assumes "(Suc i)*l \<le> length xs"
shows "length (fixed_length_sublist xs l i) = l"
  unfolding fixed_length_sublist_def
  by (metis assms diff_add_inverse2 length_drop length_take min.absorb2 mult.commute mult_Suc take_drop)

(* Modified *)
lemma vec_list_subtensor[simp]:
assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "vec_list (subtensor A i) = fixed_length_sublist (vec_list A) (prod_list (tl (dims A))) i"
  using assms
  by (metis fixed_length_sublist_length subtensor_base_def subtensor_condition_fls_imp subtensor_def vec_tensor_from_vec_list)
  
(* Added *)
lemma vec_subtensor[simp]:
assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "vec (subtensor A i) = IArray (fixed_length_sublist (vec_list A) (prod_list (tl (dims A))) i)"
  by (metis assms(1) assms(2) iarray.exhaust list_of.simps vec_def vec_list_def vec_list_subtensor)

lemma dims_subtensor[simp]:
assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "dims (subtensor A i) = tl (dims A)"
  using Suc_leI assms(1) assms(2) dims_tensor_from_vec_list  mult_le_mono1 subtensor_def
  by (metis fixed_length_sublist_length subtensor_condition_fls_imp subtensor_equiv_subtensor_legacy subtensor_legacy_def)

  

(* MATT'S CODE -------------------------------------------------------------- *)

lemma subtensor_codegen[simp]:
  assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "Rep_tensor (subtensor A i) = ((tl (dims A)), IArray (fixed_length_sublist (vec_list A) (prod_list (tl (dims A))) i))"
  using vec_subtensor dims_subtensor
  by (metis assms(1) assms(2) dims_def prod.exhaust_sel vec_def) 

lemma subtensor_base_codegen[simp]:
  assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "Rep_tensor (subtensor_base_imp A i) = ((tl (dims A)), (fixed_length_sublist_imp (vec A) (prod_list (tl (dims A))) i))"
  using assms
  by (metis fixed_length_sublist_imp.elims invertability_condition length_preserved subtensor_base_imp_def tensor_from_vec_def) 


lemma subtensor_base_imp_codegen[code abstract]:
  shows "Rep_tensor (subtensor_base A i) = (if (dims A) \<noteq> [] \<and> i < hd (dims A) then
  ((tl (dims A)), (fixed_length_sublist_imp (vec A) (prod_list (tl (dims A))) i))
else (dims A , vec A))" using subtensor_base_imp_equiv subtensor_base_codegen
  by (metis dims_def prod.collapse subtensor_base_def vec_def) 


(* -------------------------------------------------------------------------- *)

lemma subtensor_combine_subtensor[simp]:
assumes "dims A \<noteq> []"
shows "subtensor_combine (tl (dims A)) (map (subtensor A) [0..<hd (dims A)]) = A"
proof -
  have length_vec_A: "hd (dims A) * prod_list (tl (dims A)) = length (vec_list A)"
    by (metis assms list.exhaust_sel prod_list_cons tensor_dim_vec_list_invariant)
  let ?subtensor_vec = "fixed_length_sublist (vec_list A) (prod_list (tl (dims A)))"
  {
    fix i assume "i < hd (dims A)"
    then have "(Suc i)*(prod_list(tl (dims A))) \<le> length (vec_list A)"
      by (metis Suc_leI length_vec_A mult_le_mono1)
    then have "(vec_list \<circ> (\<lambda>i. tensor_from_vec_list (tl (dims A)) (?subtensor_vec i))) i = ?subtensor_vec i"
      by simp
  }
  then have 1:"map (Tensor.vec_list \<circ> (\<lambda>i. tensor_from_vec_list (tl (dims A)) (?subtensor_vec i))) [0..<hd (dims A)]
              = map ?subtensor_vec [0..<hd (dims A)]" by auto
  then have "subtensor_combine (tl (dims A)) (map (\<lambda>i. subtensor A i) [0..<hd (dims A)]) = A"
    unfolding subtensor_combine_def subtensor_def subtensor_equiv_subtensor_legacy using concat_parts_eq[OF length_vec_A]
    by (smt (verit, best) add_cancel_left_left assms diff_zero in_set_conv_nth length_map length_upt list.distinct(1)
      list.expand list.map_comp list.sel(1) list.sel(3) map_eq_conv nth_upt subtensor_base_def tensor_from_vec_list_simp)
  then show ?thesis by auto
qed

lemma
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
shows subtensor_combine_dims[simp]: "dims (subtensor_combine ds As) = length As # ds" (is ?D)
and subtensor_combine_vec[simp]: "vec_list (subtensor_combine ds As) = concat (map vec_list As)" (is ?V)
proof -
  have "\<And>v. v\<in>set (map Tensor.vec_list As) \<Longrightarrow> length v = prod_list ds" using assms tensor_dim_vec_invariant by fastforce
  then have "length As * prod_list ds = length (concat (map Tensor.vec_list As))" using concat_equal_length
    by (metis length_map)
  then show ?D ?V unfolding subtensor_combine_def by simp+
qed

lemma subtensor_subtensor_combine:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds" and "i < length As"
shows "subtensor (subtensor_combine ds As) i = As ! i"
proof -
  have "fixed_length_sublist (concat (map vec_list As)) (prod_list ds) i = vec_list (As ! i)"
    using concat_parts[of "map vec_list As" "prod_list ds" i] assms imageE length_map tensor_dim_vec_invariant
    nth_map set_map in_set_conv_nth by fastforce
  then show ?thesis
    unfolding subtensor_def using subtensor_combine_dims subtensor_combine_vec assms
    by (metis list.distinct(1) list.sel(1) list.sel(3) nth_mem subtensor_base_def tensor_from_vec_list_simp)
    
qed

lemma subtensor_induct[case_names order_0 order_step]:
assumes order_0: "\<And>A. dims A = [] \<Longrightarrow> P A"
and order_step: "\<And>A. dims A \<noteq> [] \<Longrightarrow> (\<And>i. i < hd (dims A) \<Longrightarrow> P (subtensor A i)) \<Longrightarrow> P A"
shows "P B"
using assms proof (induction "dims B" arbitrary:B)
  case Nil
  then show ?case by auto
next
  case Cons
  then show ?case by (metis dims_subtensor list.sel(3))
qed

lemma subtensor_combine_induct[case_names order_0 order_step]:
assumes order_0:"\<And>A. dims A = [] \<Longrightarrow> P A"
and order_step:"\<And>As ds. (\<And>A. A\<in>set As \<Longrightarrow> P A) \<Longrightarrow> (\<And>A. A\<in>set As \<Longrightarrow> dims A = ds) \<Longrightarrow> P (subtensor_combine ds As)"
shows "P A"
proof (induction A rule:subtensor_induct)
  case (order_0 A)
  then show ?case by (simp add: assms(1))
next
  case (order_step A)
  have "P (subtensor_combine (tl (dims A)) (map (subtensor A) [0..<hd (dims A)]))"
    apply (rule assms(2))
      using atLeastLessThan_iff dims_subtensor imageE set_map set_upt order_step
      apply auto[1]
      using dims_subtensor order_step.hyps by fastforce  
  then show ?case using subtensor_combine_subtensor[OF order_step.hyps] by metis
qed

lemma lookup_subtensor1[simp]:
assumes "i # is \<lhd> dims A"
shows "lookup (subtensor A i) is = lookup A (i # is)"
using assms
proof (induction A rule: subtensor_combine_induct)
  case order_0
  then show ?case by auto
next
  case (order_step As ds)
  have 0:"subtensor (subtensor_combine ds As) i = As ! i"
    by (metis list.discI list.sel(1) order_step.hyps order_step.prems subtensor_combine_dims subtensor_subtensor_combine valid_index_dimsE)
  have 1:"dims (subtensor_combine ds As) = length As # ds"
    using order_step subtensor_combine_def subtensor_combine_dims by force
  show ?case unfolding "0" lookup_def 1 unfolding lookup_base_Cons using order_step.prems
     dims_subtensor list.discI list.sel(1)
    list.sel(3)  valid_index_dimsE vec_list_subtensor
    by (metis (no_types, lifting) "0" "1" vec_list_def)
qed

lemma lookup_subtensor:
assumes "is \<lhd> dims A"
shows "lookup A is = hd (vec_list (fold (\<lambda>i A. subtensor A i) is A))"
using assms proof (induction "is" arbitrary: A)
  case Nil
  then show ?case
    by (metis Tensor.lookup_base_Nil fold_simps(1) list.discI lookup_def valid_index.cases) 
next
  case (Cons a "is" A)
  then show ?case
    using dims_subtensor lookup_subtensor1 fold_simps(2) list.discI list.sel(1) list.sel(3)
    valid_indexE by (metis (no_types, lifting))
qed

lemma subtensor_eqI:
assumes "dims A \<noteq> []"
and dims_eq:"dims A = dims B"
and "\<And>i. i < hd (dims A) \<Longrightarrow> subtensor A i = subtensor B i"
shows "A=B"
proof -
  {
    fix "is" assume "is \<lhd> dims A"
    then obtain i is' where is_Cons:"is = i # is'" using assms(1) by blast
    then have "lookup A is = lookup B is"
      using lookup_subtensor1 assms by (metis \<open>is \<lhd> dims A\<close> is_Cons list.sel(1) valid_index_dimsE)
  }
  then show ?thesis using tensor_lookup_eqI[OF dims_eq] by auto
qed


lemma lookup_is_in_vec: 
  "is \<lhd> (dims A) \<Longrightarrow> lookup A is \<in> set (vec_list A)"
proof (induction arbitrary:"is" rule:subtensor_induct)
  case order_0
  then show ?case unfolding lookup_def using lookup_base_Nil
    by (metis length_greater_0_conv list.set_sel(1) list.size(3) one_neq_zero prod_list_nil tensor_dim_vec_list_invariant
valid_index_length)
next
  case (order_step A "is")
  then obtain i is' where "is = i # is'" using valid_index_dimsE by blast
  then have 1:"i < hd (dims A)" using dims_def order_step.prems by auto
  have 2:"is' \<lhd> dims (subtensor A i)" using \<open>is = i # is'\<close> dims_subtensor order_step.prems "1" order_step.hyps by fastforce
  have "lookup A is \<in> set (vec_list (subtensor A i))" 
    using order_step.IH [OF 1 2] lookup_subtensor1 \<open>is = i # is'\<close> order_step.prems by auto
  then show ?case using vec_list_subtensor fixed_length_sublist_def by (metis "1" in_set_dropD in_set_takeD order_step.hyps)
qed


(* EXTENSION OF SUBTENSOR --------------------------------------------------------------------- *)

definition iterated_subtensor_lookup :: "'a tensor \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> 'a"
  where "iterated_subtensor_lookup A is is' = lookup_imp A (is@is')"

abbreviation iterated_subtensor_vec :: "'a tensor \<Rightarrow> nat list \<Rightarrow> 'a iarray"
  where "iterated_subtensor_vec A is \<equiv> IArray (tensor_vec_from_lookup (drop (length is) (dims A)) (iterated_subtensor_lookup A is))"

definition iterated_subtensor_base :: "'a tensor \<Rightarrow> nat list \<Rightarrow> 'a tensor"
  where "iterated_subtensor_base A is = (if length is \<le> length (dims A) then tensor_from_lookup (drop (length is) (dims A)) (iterated_subtensor_lookup A is) else A)"

definition iterated_subtensor :: "'a tensor \<Rightarrow> nat list \<Rightarrow> 'a tensor"
  where "iterated_subtensor A is = (if is \<lhd> take (length is) (dims A) then (iterated_subtensor_base A is) else undefined)"


definition iterated_subtensor_test :: "'a tensor \<Rightarrow> nat list \<Rightarrow> 'a tensor"
  where "iterated_subtensor_test A is = (if is \<lhd> take (length is) (dims A) then (tensor_from_lookup (drop (length is) (dims A)) (iterated_subtensor_lookup A is)) else undefined)"


(* NB : This is a very cool lemma that should go in the diss *)
(* It was particular difficult to formalise as subtensor_base has different behaviour based on size of dims A
and we have the added constraint that the index must be valid *)
lemma iterated_subtensor_dims_eq:
  shows "is \<lhd> take (length is) (dims A) \<Longrightarrow> dims (iterated_subtensor A is) = drop (length is) (dims A)"
  by (metis dims_tensor_from_lookup iterated_subtensor_base_def iterated_subtensor_def nat_le_linear take_all valid_index_length)

lemma iterated_subtensor_simp:
  assumes "length is \<le> length (dims A)"
  shows "iterated_subtensor_vec A is = subarray (vec A) (prod_list (drop (length is) (dims A))) (flattened_index (dims A) is)"
proof -
  let ?n = "length is"
  let ?ds' = "(drop (length is) (dims A))"
  let ?ds1 = "take (length is) (strides (dims A))"
  let ?ds2 = "drop (length is) (strides (dims A))"
  let ?lhs = "iterated_subtensor_vec A is"
  have "?lhs = IArray (map (\<lambda>j. iterated_subtensor_lookup A is (unflattened_index ?ds' j)) [0..<prod_list ?ds'])"
     using tensor_vec_from_lookup_imp_equiv by auto 
  hence "?lhs = IArray (map (\<lambda>j. (vec A) !! (flattened_index (dims A) (is@(unflattened_index_imp (strides ?ds') j)))) [0..<prod_list ?ds'])"
    by (simp add: iterated_subtensor_lookup_def lookup_imp_def lookup_equiv_lookup_imp)
  hence "?lhs = IArray (map (\<lambda>j. (vec A) !! (flattened_index_imp (strides (dims A)) (is@(unflattened_index_imp (strides ?ds') j)))) [0..<prod_list ?ds'])"
    using flattened_index_imp_works by presburger
  moreover from assms have A: "length is = length ?ds1" using strides_length by simp
  ultimately have "?lhs = IArray (map (\<lambda>j. (vec A) !! (
flattened_index_imp ?ds1 is + flattened_index_imp ?ds2 (unflattened_index_imp (strides ?ds') j))) [0..<prod_list ?ds'])"
    by (metis (mono_tags, lifting) append_take_drop_id flattened_index_imp_split map_eq_conv) 
  hence "?lhs = IArray (map (\<lambda>j. (vec A) !! (
flattened_index_imp ?ds1 is + flattened_index_imp ?ds2 (unflattened_index_imp ?ds2 j))) [0..<prod_list ?ds'])"
    using strides_drop by presburger
  moreover have "\<And>i. i < prod_list ?ds' \<Longrightarrow> flattened_index_imp ?ds2 (unflattened_index_imp ?ds2 i) = i"
    using unflattened_invertible by (simp add: strides_drop flattened_index_imp_works) 
  moreover have "flattened_index_imp (take (length is) (strides (dims A))) is = flattened_index (dims A) is"
     proof (cases "length is < length (dims A)")
    case True
    then show ?thesis using A by (smt (verit, ccfv_threshold) Tensor.flattened_index_Nil_1 Tensor.flattened_index_Nil_2_imp append.right_neutral
        append_take_drop_id assms strides.simps(1) strides_length flattened_index_imp_split flattened_index_imp_works
        id_take_nth_drop less_numeral_extra(1) list.size(3) map_nth nat_int_comparison(2) of_nat_0_less_iff of_nat_less_0_iff
        prod_list_nil unflattened_invertible valid_index.Nil) 
  next
    case False
    then show ?thesis by (simp add: strides_length flattened_index_imp_works)  
  qed
  ultimately show ?thesis by (simp add: add.commute subarray_def)
qed

fun iterated_subtensor_sep :: "'a tensor \<Rightarrow> nat list \<Rightarrow> 'a tensor" where
  iterated_subtensor_sep_Nil: "iterated_subtensor_sep A [] = A"
| iterated_subtensor_sep_Cons: "iterated_subtensor_sep A (i#is) = iterated_subtensor_sep (subtensor A i) is"


(*
lemma test:
  shows "is \<lhd> take (length is) (dims A) \<Longrightarrow> iterated_subtensor_sep A is = iterated_subtensor A is"
proof (induction "is")
  case Nil
  have "iterated_subtensor_lookup A [] = (\<lambda>is'. lookup_imp A ([]@is'))" using iterated_subtensor_lookup_def by blast 
  hence "iterated_subtensor_lookup A [] = lookup_imp A" by simp
  moreover have "[] \<lhd> (take (length []) (dims A))" by (simp add: valid_index.Nil)
  ultimately show ?case
    by (simp add:  iterated_subtensor_base_def iterated_subtensor_def lookup_equiv_lookup_imp tensor_lookup) 
next
  case (Cons i "is")
  hence "i < hd (dims A)"
    by (metis hd_take length_greater_0_conv list.distinct(1) list.rel_sel list.sel(1) valid_index_list_all2_iff) 
  hence "subtensor A i = tensor_from_vec (tl (dims A)) (fixed_length_sublist_imp (vec A) (prod_list (tl (dims A))) i)"
    by (metis Cons.prems Rep_tensor_inverse length_0_conv list.distinct(1) subtensor_base_imp_codegen subtensor_def take_Nil tensor_from_vec_def valid_index_length)
  thus ?case 
qed*)


(* This shows that iterated subtensor is valid *)
lemma iterated_subensor_lookup:
  assumes "is@is' \<lhd> dims A"
  shows "lookup (iterated_subtensor A is) is' = lookup A (is@is')"
proof -
  from assms have A: "is \<lhd> take (length is) (dims A)" using valid_index_take by force
  hence "iterated_subtensor A is = tensor_from_lookup (drop (length is) (dims A)) (iterated_subtensor_lookup A is)"
    by (metis add.commute assms iterated_subtensor_base_def iterated_subtensor_def length_append
        linorder_not_le not_add_less2 valid_index_length)
  thus ?thesis
    by (metis A append_take_drop_id assms iterated_subtensor_lookup_def list_all2_append lookup_equiv_lookup_imp
        lookup_tensor_from_lookup valid_index_length valid_index_list_all2_iff) 
qed



thm tensor_lookup_codegen

lemma iterated_subtensor_codegen[code abstract]:
"Rep_tensor (iterated_subtensor_base A is) = 
(if length is \<le> length (dims A) then (drop (length is) (dims A), subarray (vec A) (prod_list (drop (length is) (dims A))) (flattened_index (dims A) is)) else (dims A, vec A))"
  using tensor_lookup_codegen iterated_subtensor_simp iterated_subtensor_base_def
  by (metis (mono_tags) dims_def prod.exhaust_sel tensor_vec_from_lookup_imp_equiv vec_def)


(* Need a function that represents the backwards function of this operation *)

(* Currently, this naive implementation is inefficient as there are repeated calls to flattened/unflattened_index*)
(* A better approach would be to exploit the fact that iterated subtensor selection from the leading dimension
is equivalent to selecting a contiguous span of elements from the flattened tensor. *)


(* This is probably slow in practice as we are essentially representing a sparse tensor as a dense one *)

fun iterated_subtensor_backward_lookup :: "nat list \<Rightarrow> nat list \<Rightarrow> real"
  where "iterated_subtensor_backward_lookup is js = (if take (length is) js = is then 1 else 0)"

definition iterated_subtensor_backward :: "'a tensor \<Rightarrow> nat list \<Rightarrow> real tensor"
  where "iterated_subtensor_backward A is = tensor_from_lookup_imp (dims A) (iterated_subtensor_backward_lookup is)"




definition repeat_subtensor :: "'a tensor \<Rightarrow> nat list \<Rightarrow> 'a tensor" where
"repeat_subtensor A ds = tensor_from_vec (ds@(dims A)) (IArray (map (\<lambda>i. (vec A) !! (i mod (prod_list (dims A)))) [0..<(prod_list ds)*(prod_list (dims A))]))"

lemma repeat_subtensor_codegen[code]:
  "Rep_tensor (repeat_subtensor A ds) = (ds@(dims A), IArray (map (\<lambda>i. (vec A) !! (i mod (prod_list (dims A)))) [0..<(prod_list ds)*(prod_list (dims A))]))"
  by (simp add: invertability_condition repeat_subtensor_def tensor_from_vec_def)

(* Proofs of correctness needed here *)

(* VERY NB ! ! ! ! ! ! ! *)


(* Need some proof here that shows an iterated subtensor boils down to a fixed length sublist *)


(* EXTENSION WORK ----------------------------------------------------------------------------- *)

(* Place_at is a very intuitive definition *)
definition place_at :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"place_at y i xs = (take i xs) @ (y # (drop i xs))"

(* Basic properties of place_at *)
lemma place_at_before[simp]:
  assumes "i \<le> length xs"
  shows "take i (place_at y i xs) = take i xs"
  by (simp add: assms place_at_def)

lemma place_at_after[simp]:
  assumes "i \<le> length xs"
  shows "drop (i+1) (place_at y i xs) = drop i xs"
  by (simp add: assms place_at_def)

lemma place_at_insert[simp]:
  assumes "i \<le> length xs"
  shows "(place_at y i xs) ! i = y"
  by (simp add: assms nth_append place_at_def)

lemma place_at_zero[simp]:
  shows "(place_at y 0 xs) = y # xs"
  by (simp add: place_at_def)

fun place_at_imp :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"place_at_imp y i [] = [y]"
| place_at_imp_Cons: "place_at_imp y i (x#xs) = (if i > 0 then x # (place_at_imp y (i-1) xs) else ((y#(x#xs))))"

(* Prove equivalence and set up code equation *)
lemma place_at_imp_equiv[code]:
  shows "place_at z i xs = place_at_imp z i xs"
proof (induction i arbitrary: xs)
  case 0
  then show ?case
    by (metis append.simps(1) append_eq_conv_conj less_numeral_extra(3) list.size(3) place_at_imp.elims place_at_def)
next
  case S: (Suc i)
  then show ?case proof (cases "xs = []")
    case True
    then show ?thesis
      by (simp add: place_at_def)
  next
    case False
    then show ?thesis using list.exhaust_sel place_at_imp_Cons place_at_def
      by (metis S append.simps(2) diff_Suc_1 drop_Suc_Cons take_Suc_Cons zero_less_Suc)
  qed
qed

definition list_without :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"list_without xs i = (take i xs) @ (drop (i+1) xs)"

fun list_without_imp :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"list_without_imp [] i = []" | list_without_Cons: "list_without_imp (x#xs) i = (if i = 0 then xs else x # list_without_imp xs (i-1))"

lemma without_imp_equiv[code]:
  shows "list_without xs i = list_without_imp xs i"
proof (induction i arbitrary: xs)
  case 0
  then show ?case
    by (metis add.commute append.simps(1) drop.simps(1) drop0 drop_Suc_Cons list_without_imp.elims list_without_def plus_1_eq_Suc take0)
next
  case S: (Suc i)
  then show ?case proof (cases "xs = []")
    case True
    then show ?thesis
      by (simp add: list_without_def)
      
  next
    case False
    then show ?thesis using list.exhaust_sel list_without_Cons list_without_def
      by (metis S Suc_eq_plus1 append_Cons diff_Suc_1 drop_Suc_Cons nat.distinct(1) take_Suc_Cons)
  qed
qed

(* list_without reverses place_at *)
lemma place_at_without_inversion:
  assumes "i \<le> length xs"
  shows "list_without (place_at y i xs) i = xs"
  using assms list_without_def place_at_after by fastforce


fun prod_list_without :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"prod_list_without xs i = prod_list (list_without xs i)"


definition select_dimension_lookup :: "'a tensor \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a"
  where "select_dimension_lookup A d i is = lookup_imp A (place_at i d is)"


definition select_dimension::"'a tensor \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tensor" where
  "select_dimension A d i = tensor_from_lookup (list_without (dims A) d) (select_dimension_lookup A d i)"



end