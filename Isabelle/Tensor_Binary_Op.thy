(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Binary Operation\<close>

theory Tensor_Binary_Op
imports Tensor_Subtensor Tensor_Unary_Op Tensor_Constants
begin


(* Problem: typeclass plus only has one zero element. If this is the empty tensor, other zero tensors cannot be of rank 0.*)


(* vec_binop is the same form as what Bentkamp et al originally used *)
definition vec_binop::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where "vec_binop f a b = map (\<lambda>(x,y). f x y) (zip a b)"

(* vec_binop using nth function *)
definition vec_binop_nth::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"vec_binop_nth f a b = map (\<lambda>i. f (a ! i) (b ! i)) [0..<(min (length a) (length b))]"

(* iarray equivalent - more efficient *)
definition vec_binop_iarray::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'b iarray" where
"vec_binop_iarray f a b = IArray (map (\<lambda>i. f (a !! i) (b !! i)) [0..<(min (IArray.length a) (IArray.length b))])"


(* We proceed to prove that Bentkamp et al.'s formulation is equivalent to an array-based version *)
(* Proof proceeds by showing that the nth element of both lists are equal *)
lemma vec_binop_equiv:
  shows "map (\<lambda>(x,y). f x y) (zip xs ys) = map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<(min (length xs) (length ys))]"
  (is "?lhs=?rhs")
  using nth_equalityI
proof -
  let ?l = "min (length xs) (length ys)"
  have A: "length ?lhs = length ?rhs" by simp
  have B: "length ?rhs = ?l" by simp
  {
  fix i
  assume bounded: "i < ?l"
  hence "?rhs ! i = f (xs ! i) (ys ! i)" by auto
  moreover from bounded B have "(map (\<lambda>(x,y). f x y) (zip xs ys)) ! i = (\<lambda>(x,y). f x y) ((zip xs ys) ! i)"
    using List.nth_map[where ?xs="zip xs ys" and ?f="(\<lambda>(x,y). f x y)" and ?n="i"] by fastforce
  moreover from bounded B have "(\<lambda>(x,y). f x y) ((zip xs ys) ! i) = f (xs ! i) (ys ! i)" by auto
  ultimately have "?lhs ! i = ?rhs ! i" by presburger 
  }
  from this A B show ?thesis using List.nth_equalityI by (metis (no_types, lifting))
qed


lemma vec_binop_iarray_equiv:
  shows "IArray (vec_binop f xs ys) = vec_binop_iarray f (IArray xs) (IArray ys)"
  by (simp add: vec_binop_def vec_binop_equiv vec_binop_iarray_def)
  

lemma smallest_list[simp]:
  shows "length (vec_binop op a b) = (if length a \<le> length b then (length a) else (length b))"
  by (simp add: vec_binop_def)

(* Adjusted from plus_base, uses vec_binop to stay true to Bentkamp et al. *)
definition binop_base::"('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor \<Rightarrow> 'b tensor"
  where "binop_base op A B = (tensor_from_vec_list (if IArray.length (vec A) \<le> IArray.length (vec B) then (dims A) else (dims B))
 (vec_binop op (vec_list A) (vec_list B)))"

(* However, for code generation, the vec_binop_iarray version is used through the following code equation: *)
lemma binop_base_code_eq[code abstract]: "Rep_tensor (binop_base op A B) = 
((if IArray.length (vec A) \<le> IArray.length (vec B) then (dims A) else (dims B)), (vec_binop_iarray op (vec A) (vec B)))"
  by (smt (verit, best) IArray.length_def binop_base_def invertability_condition list_of.simps smallest_list snd_conv tensor_dim_vec_list_invariant tensor_from_vec_list_def tensor_from_vec_list_simp vec_binop_iarray_equiv vec_def)


(* General binary operation *)
definition binop :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor \<Rightarrow> 'b tensor"
  where "binop op A B = (if (dims A = dims B) then binop_base op A B else undefined)"


(* Simplification rules *) (* From Tensor_Plus *)
lemma binop_dim1[simp]: "dims A = dims B \<Longrightarrow> dims (binop op A B) = dims A" unfolding binop_def binop_base_def
  using dims_tensor tensor_dim_vec_invariant length_map map_fst_zip vec_binop_def by simp 
lemma binop_dim2[simp]: "dims A = dims B \<Longrightarrow> dims (binop op A B) = dims B" using binop_dim1 by metis
lemma binop_base: "dims A = dims B \<Longrightarrow> binop op A B = binop_base op A B" unfolding binop_def by metis

(* From Tensor_Plus *)
lemma fixed_length_sublist_binop:
assumes "length xs1 = c * l" "length xs2 = c * l" "i < c"
shows "fixed_length_sublist (vec_binop op xs1 xs2) l i
          = vec_binop op (fixed_length_sublist xs1 l i) (fixed_length_sublist xs2 l i)"
unfolding vec_binop_def fixed_length_sublist_def using drop_map drop_zip take_map take_zip by metis

(* From Tensor_Plus *)
lemma vec_binop[simp]:
assumes "dims A = dims B"
shows "vec_list (binop op A B) = vec_binop op (vec_list A) (vec_list B)"
  unfolding binop_def binop_base_def vec_binop_def using assms
  by (auto; metis (no_types, lifting) length_map length_tensor_vec_from_lookup map_fst_zip tensor_lookup tensor_from_lookup_def vec_tensor)

(* Added by matt *)
lemma rep_binop[simp]:
  assumes "dims A = dims B"
  shows "Rep_tensor (binop op A B) = (dims A, vec_binop_iarray op (vec A) (vec B))"
  by (simp add: assms binop_base_code_eq binop_def)


(* From Tensor_Plus *)
lemma subtensor_binop:
fixes A::"'a tensor" and B::"'a tensor"
assumes "i < hd (dims A)"
and "dims A = dims B"
and "dims A \<noteq> []"
shows "subtensor (binop op A B) i = binop op (subtensor A i) (subtensor B i)"
proof -
   have "length (vec_list A) =  hd (dims A) * prod_list (tl (dims A))"
     using prod_list_cons assms by (metis list.exhaust_sel tensor_dim_vec_list_invariant) 
   then show ?thesis
     using Tensor_Binary_Op.vec_binop assms fixed_length_sublist_binop vec_subtensor tensor_eqI
     dims_subtensor binop_dim1
     by (smt (verit, best) tensor_dim_vec_list_invariant tensor_from_vec_list_simp vec_list_subtensor) 
qed


(* From Tensor_Plus *)
lemma lookup_binop[simp]:
assumes "dims A = dims B"
and "is \<lhd> dims A"
shows "lookup (binop op A B) is = op (lookup A is) (lookup B is)"
using assms proof (induction "binop op A B" arbitrary:A B "is" rule: subtensor_induct)
  case (order_0 A B "is")
  then have "is = []" by auto
  have 1:"[] \<lhd> dims A" using order_0 \<open>is = []\<close> by auto
  have 2:"[] \<lhd> dims B" using order_0 \<open>is = []\<close> by auto
  have 3:"[] \<lhd> dims (binop op A B)" using order_0 \<open>is = []\<close> by auto
  from assms have "length (vec_list A) = 1" "length (vec_list B) = 1"
    using order_0.hyps order_0.prems(1) apply fastforce
    using "1" order_0.prems(1) by force
  then show ?case unfolding lookup_subtensor[OF 1] lookup_subtensor[OF 2] lookup_subtensor[OF 3] \<open>is = []\<close>
    fold_simps(1) vec_binop[OF order_0.prems(1)] unfolding vec_binop_def using  order_0.prems  length_map
    list.map_sel(1) list.size(3)  map_fst_zip map_snd_zip order_0.hyps
    zero_neq_one case_prod_unfold by metis
next
  case (order_step A B "is")
  then obtain i is' where "is = i # is'" by auto
  have 1:"is \<lhd> dims A" using order_step by auto
  have 2:"is \<lhd> dims B" using order_step by auto
  have 3:"is \<lhd> dims (binop op A B)" using order_step by auto
  have "lookup (binop op (subtensor A i) (subtensor B i)) is' = op (lookup (subtensor A i) is') (lookup (subtensor B i) is')"
     apply (rule order_step.hyps(2)[of i])
        using \<open>is = i # is'\<close> 3 hd_conv_nth length_greater_0_conv nth_Cons_0 order_step.hyps(1) valid_index_lt
        apply auto[1]
       apply (metis "2" \<open>is = i # is'\<close> list.inject list.sel(1) list.simps(3) order_step.prems(1) subtensor_binop valid_index.cases)
      using "1" \<open>is = i # is'\<close> order_step.prems(1) binop_dim1 apply auto[1]
     using "1" \<open>is = i # is'\<close> binop_dim1
     apply (smt (verit) dims_subtensor list.discI list.sel(1) valid_index_dimsE)
     by (metis "3" \<open>is = i # is'\<close> binop_dim2 dims_subtensor list.rel_sel list.sel(1) list.sel(3) list.simps(3) order_step.prems(1) valid_index_list_all2_iff)  
  then show ?case using lookup_subtensor[OF 1] lookup_subtensor[OF 2] lookup_subtensor[OF 3]
    using order_step \<open>is = i # is'\<close> binop_dim1 lookup_subtensor1 list.sel(1) subtensor_binop valid_index_dimsE by metis
qed


(* Matt's Contribution *)


lemma vec_binop_unop_composition:
  "unop_list g (vec_binop f xs ys) = vec_binop (\<lambda>x y. g (f x y)) xs ys"
  by (simp add: unop_list_def vec_binop_def vec_binop_equiv)

lemma binop_base_unop_composition:
  assumes "dims A = dims B"
  shows "unop g (binop_base f A B) = binop_base (\<lambda>x y. g (f x y)) A B"
  by (simp add: assms binop_base_def unop_def vec_binop_unop_composition)

lemma binop_unop_composition:
  assumes "dims A = dims B"
  shows "unop g (binop f A B) = binop (\<lambda>x y. g (f x y)) A B"
  by (simp add: assms binop_base binop_base_unop_composition)

lemma unop_binop_composition:
  assumes "dims A = dims B"
  shows "(binop f (unop g A) (unop h B)) = binop (\<lambda>x y. f (g x) (h y)) A B"
proof -
  from assms have "dims (unop g A) = dims (unop h B)" by simp 
  thus ?thesis
    by (smt (verit, best) binop_dim1 dims_unop lookup_binop lookup_unop tensor_lookup_eqI) 
qed

(* This is a generalisation of tensor_add_0_right from Bentkamp et al.  *)
lemma tensor_replicate_right_binop[simp]:
  "binop f A (tensor_replicate (dims A) x) = unop (\<lambda>a. f a x) A"
  by (smt (verit, ccfv_SIG) binop_dim1 dims_unop lookup_binop lookup_unop tensor_lookup_eqI dims_tensor_replicate lookup_tensor_replicate)

(* Code abbreviation required to do code gen *)
definition tensor_replicate_right_binop_abbrev :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a tensor \<Rightarrow> 'a \<Rightarrow> 'a tensor"
  where [code_abbrev]: "tensor_replicate_right_binop_abbrev f A x = binop f A (tensor_replicate (dims A) x)"

lemma tensor_replicate_right_binop_abbrev_codegen[code]:
  "tensor_replicate_right_binop_abbrev f A x = unop (\<lambda>a. f a x) A"
  by (simp add: tensor_replicate_right_binop_abbrev_def)

lemma tensor_replicate_left_binop[simp]:
  "binop f (tensor_replicate (dims B) x) B = unop (\<lambda>b. f x b) B"
  by (smt (verit, ccfv_SIG) binop_dim1 dims_unop lookup_binop lookup_unop tensor_lookup_eqI dims_tensor_replicate lookup_tensor_replicate)

definition tensor_replicate_left_binop_abbrev :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor"
  where [code_abbrev]: "tensor_replicate_left_binop_abbrev f x A = binop f (tensor_replicate (dims A) x) A"

lemma tensor_replicate_left_binop_abbrev_codegen[code]:
  "tensor_replicate_left_binop_abbrev f x A = unop (\<lambda>b. f x b) A"
  by (simp add: tensor_replicate_left_binop_abbrev_def)

(* -----------------------------*)


end