(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Unary Operation\<close>

theory Tensor_Unary_Op
imports Tensor_Subtensor
begin

(*

MAJOR ISSUE: There is a cost that is undergone for every conversion between array and list in the 
target language

experiments indicate that unop and unop_imp_vec have the same performance.

- unop uses Array.to_list and Array.of_list

- unop_imp_vec uses Array.of_list only but the use of nat's for incrementing is slow

SOLUTION:

Code equation to rewrite IArray (map... ) as IArray.of_fun



NB :: The fundamental concept is to continue with a list-based definition for theorem proving, but
implement iarray-based definitions 
*)

definition unop_list::"('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"unop_list f xs = map f xs"

(* This form matches what is rewritten to the efficient IArray.of_fun *)
definition unop_array::"('a \<Rightarrow> 'b) \<Rightarrow> 'a iarray \<Rightarrow> 'b iarray" where
"unop_array f axs = IArray (map (\<lambda>i. f (axs !! i)) [0..<(IArray.length axs)])"

lemma unop_array_length[simp]:
  "IArray.length (unop_array f axs) = IArray.length axs"
  by (simp add: unop_array_def)

lemma unop_list_length[simp]:
  "length (unop_list f xs) = length xs"
  by (simp add: unop_list_def)

lemma unop_list_array_equiv:
"IArray (unop_list f xs) = unop_array f (IArray xs)"
proof -
  have "unop_list f xs = map (\<lambda>i. f ((IArray xs) !! i)) [0..<(IArray.length (IArray xs))]"
    by (smt (verit, ccfv_threshold) length_map list_of.simps list_of_code nth_equalityI nth_map unop_list_def)
  thus ?thesis by (simp add: unop_array_def) 
qed

(* This is the basic definition in terms of lists, i.e. easier to use for theorem proving *)
definition unop::"('a \<Rightarrow> 'b) \<Rightarrow> 'a tensor \<Rightarrow> 'b tensor" where
"unop f A = tensor_from_vec_list (dims A) (unop_list f (vec_list A))"

(* More efficient version based off of iarray accessing *)
definition unop_imp::"('a \<Rightarrow> 'b) \<Rightarrow> 'a tensor \<Rightarrow> 'b tensor" where
"unop_imp f A = tensor_from_vec (dims A) (unop_array f (vec A))"

(* Code equation rewriting unop to faster implementation version *)
lemma unop_imp_equiv[code]:
  "unop f A = unop_imp f A"
  by (metis iarray.exhaust list_of.simps tensor_from_vec_def tensor_from_vec_list_def unop_def unop_imp_def
unop_list_array_equiv vec_def vec_list_def)

lemma iarray_map_length[simp]:
  "IArray.length (map_iarray f (IArray xs)) = IArray.length (IArray xs)"
  by simp

lemma unop_valid[simp]:
  shows "prod_list (dims A) = IArray.length (unop_array f (vec A))"
  by (metis tensor_dim_vec_invariant unop_array_length)

(* Matt's Contribution *)

lemma unop_list_composition[simp]:
  "unop_list g (unop_list f xs) = unop_list (g \<circ> f) xs"
  by (simp add: unop_list_def)

lemma unop_composition[simp]:
  "unop g (unop f A) = unop (g \<circ> f) A"
  by (simp add: unop_def unop_list_def)

lemma unop_composition2[simp]:
  "unop g (unop f A) = unop (\<lambda>x. g (f x)) A"
proof -
  have "unop g (unop f A) = unop (g \<circ> f) A" by simp
  moreover have "(g \<circ> f) = (\<lambda>x. g (f x))" using comp_apply by metis
  ultimately show ?thesis by simp
qed

lemma unop_ident[simp]:
  "unop (\<lambda>x. x) A = A" using unop_def unop_list_def
  by (metis map_ident tensor_from_vec_list_simp) 
  
(* -----------------------------*)



(* Unary Operation Code Generation *) (* Turning things into an IArray made this proof uglier *)
lemma unop_codegen[code abstract]: "Rep_tensor (unop f A) = ((dims A),(unop_array f (vec A)))"
  by (metis invertability_condition tensor_from_vec_def unop_imp_def unop_imp_equiv unop_valid)

lemma dims_unop[simp]:"dims (unop f A) = dims A"
  unfolding unop_def by (simp add: unop_list_def) 

lemma vec_unop[simp]: "vec (unop f A) = unop_array f (vec A)"
  unfolding unop_def by (metis snd_conv unop_codegen unop_def vec_def) 

lemma unop_fixed_length_sublist:
assumes "length xs = l * c" "i<c"
shows "fixed_length_sublist (map op xs) l i = map op (fixed_length_sublist xs l i)"
unfolding fixed_length_sublist_def by (simp add: drop_map take_map)

lemma unop_subtensor:
assumes "dims A \<noteq> []" "i < hd (dims A)"
shows "unop f (subtensor A i) = subtensor (unop f A) i"
proof (rule tensor_eqI)
  show "dims (unop f (subtensor A i)) = dims (subtensor (unop f A) i)"
    using dims_unop dims_subtensor assms(1) assms(2) by metis 
  show "vec (unop f (subtensor A i)) = vec (subtensor (unop f A) i)"
    unfolding vec_unop
    unfolding vec_subtensor[OF \<open>dims A \<noteq> []\<close> \<open>i < hd (dims A)\<close>]
    using vec_subtensor[of "unop f A" i]
    by (metis (no_types, lifting) assms(1) assms(2) dims_unop length_map list.exhaust_sel mult.commute
        prod_list.Cons tensor_dim_vec_list_invariant unop_def unop_fixed_length_sublist
        unop_list_array_equiv unop_list_def vec_tensor_from_vec_list)
qed

lemma lookup_unop:
assumes "is \<lhd> dims A"
shows "lookup (unop f A) is = f (lookup A is)"
using assms proof (induction A arbitrary:"is" rule:subtensor_induct)
  case (order_0 A "is")
  then have "length (vec_list A) = 1" by simp
  then have "hd (unop_list f (vec_list A)) = f (hd (vec_list  A))" unfolding unop_list_def by (metis list.map_sel(1) list.size(3) zero_neq_one)
  moreover have "is = []" using order_0 by auto
  moreover have "prod_list [] = 1" by simp
  ultimately show ?case unfolding unop_def unop_list_def 
    by (auto simp add: \<open>length (Tensor.vec_list A) = 1\<close> lookup_def order_0.hyps)
next
  case (order_step A "is")
  then obtain i is' where "is = i # is'" by blast
  then have "lookup (unop f (subtensor A i)) is' = f (lookup (subtensor A i) is')"
    by (metis (no_types, lifting) dims_subtensor list.sel(1) list.sel(3) order_step.IH order_step.hyps order_step.prems valid_index_dimsE)
  then show ?case using unop_subtensor \<open>is = i # is'\<close> dims_unop lookup_subtensor1
    list.sel(1) order_step.hyps order_step.prems valid_index_dimsE
    by metis
qed


(* Added by Matt *)

lemma valid_index_unop:
  shows "is \<lhd> (dims A) = (is \<lhd> dims (unop f A))"
  by force
  
end