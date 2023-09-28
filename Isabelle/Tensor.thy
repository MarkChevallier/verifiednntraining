(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor\<close>

theory Tensor
imports Complex_Main "HOL-Library.IArray"
begin

(*
When it comes to code generation, the 'resting' of the elements of a tensor will be an
array in ocaml, so it is important to, where possible, prevent unnecessary conversions 
between list and array
*)
typedef 'a tensor = "{t::nat list \<times> 'a iarray. IArray.length (snd t) = prod_list (fst t)}"
  by (smt (z3) IArray.length_def fst_conv length_replicate list_of.simps mem_Collect_eq snd_conv)
  

definition dims::"'a tensor \<Rightarrow> nat list" where
  "dims A = fst (Rep_tensor A)"

definition vec::"'a tensor \<Rightarrow> 'a iarray" where
  "vec A = snd (Rep_tensor A)"

(* Possible way of working with tensors *)
typedef 'a tensor_view = "{t::nat list \<times> (nat \<Rightarrow> 'a). (\<forall>n. n \<ge> prod_list (fst t) \<longrightarrow> (snd t) n = undefined)}"
  morphisms Rep_tensorview Abs_tensorview by auto 

definition view :: "'a tensor \<Rightarrow> 'a tensor_view" where
"view A = Abs_tensorview (dims A, IArray.sub (vec A))"

(* -------------------------------------------------- *)


definition vec_list::"'a tensor \<Rightarrow> 'a list" where
  "vec_list A = IArray.list_of (snd (Rep_tensor A))"

lemma vec_list_vec:
  "vec_list A = IArray.list_of (vec A)" by (simp add: vec_list_def vec_def)

lemma vec_vec_list:
  "vec A = IArray (vec_list A)"
  by (metis iarray.exhaust list_of.simps vec_list_vec) 

definition tensor_from_vec::"nat list \<Rightarrow> 'a iarray \<Rightarrow> 'a tensor" where
  "tensor_from_vec d v = Abs_tensor (d,v)"

definition tensor_from_vec_list::"nat list \<Rightarrow> 'a list \<Rightarrow> 'a tensor" where
  "tensor_from_vec_list d l = Abs_tensor (d, (IArray l))"


lemma tensor_dim_vec_invariant[simp]: "IArray.length (vec A) = prod_list (dims A)"
  by (metis (mono_tags, lifting) Rep_tensor dims_def mem_Collect_eq vec_def)

lemma tensor_dim_vec_list_invariant[simp]: "length (vec_list A) = prod_list (dims A)"
  by (metis IArray.length_def tensor_dim_vec_invariant vec_def vec_list_def) 


(* NOT MINE, BUT INCLUDE IN DISSERTATION *)
(* If the fundamental requirement holds, then the constructed tensor is valid *)
lemma
assumes "IArray.length v = prod_list d"
shows dims_tensor[simp]: "dims (tensor_from_vec d v) = d"
and   vec_tensor[simp]:  "vec (tensor_from_vec d v) = v"
  using assms Abs_tensor_inverse[where ?y="(d,v)"] 
  by (simp add: dims_def tensor_from_vec_def vec_def)+

(* Additional stuff added by Matt *)
lemma
  assumes "length v = prod_list d"
shows dims_tensor_from_vec_list[simp]: "dims (tensor_from_vec_list d v) = d"
and vec_tensor_from_vec_list[simp]: "vec_list (tensor_from_vec_list d v) = v"
  using assms Abs_tensor_inverse[where ?y="(d, IArray v)"] 
  by (simp add: dims_def tensor_from_vec_list_def vec_list_def vec_def)+

(* Include this maybe *)
lemma invertability_condition:
  assumes "IArray.length v = prod_list d"
  shows "Rep_tensor (Abs_tensor (d,v)) = (d,v)"
  using assms Abs_tensor_inverse[where ?y="(d,v)"] by simp

lemma equal_dim_vec_implies_equal_tensor:
  assumes "v = v'" and "d = d'"
  shows "tensor_from_vec d v = tensor_from_vec d' v'"
  using assms by force 

(* Needed for code gen *)

lemma tensor_from_vec_simp[simp,code]: "tensor_from_vec (dims A) (vec A) = A"
  by (simp add: Rep_tensor_inverse Tensor.vec_def dims_def tensor_from_vec_def)

lemma tensor_from_vec_list_simp[simp,code]: "tensor_from_vec_list (dims A) (vec_list A) = A"
  by (metis Rep_tensor_inverse dims_def iarray.exhaust list_of.simps prod.exhaust_sel tensor_from_vec_list_def vec_list_def)


(* INCLUDE IN CODE GENERATION SECTION *)
lemma tensor_rep_invertible[simp,code abstype]:
  "Abs_tensor (Rep_tensor A) = A"
  by (simp add: Rep_tensor_inverse)


definition tensor_from_list :: "'a list \<Rightarrow> 'a tensor" where
  "tensor_from_list xs = tensor_from_vec [length xs] (IArray xs)"


lemma tensor_from_list_simp[simp, code abstract]:
  "Rep_tensor (tensor_from_list v) = ([length v], IArray v)"
  by (simp add: Abs_tensor_inverse tensor_from_list_def tensor_from_vec_def) 


(* End *)


(* Useful lemmas for prod_list *)
lemma prod_list_cons:
  "prod_list(x # xs) = x * (prod_list xs)"
  by simp

lemma prod_list_nil:
  "prod_list [] = 1"
  by simp

lemma prod_list_one:
  "prod_list[i] = i"
  by simp

(**
by (metis (mono_tags, lifting) Rep_tensor Tensor.vec_def dims_def mem_Collect_eq)
**)

lemma tensor_eqI[intro]:
assumes "dims A = dims B" and "vec A = vec B"
shows "A=B"
by (metis assms tensor_from_vec_simp)

(* 3D tensor \<Rightarrow> order 3 *)
abbreviation order::"'a tensor \<Rightarrow> nat" where
  "order t == length (dims t)"

(* Checks that indices are within range *)
inductive valid_index::"nat list \<Rightarrow> nat list \<Rightarrow> bool" (infix "\<lhd>" 50) where
  Nil: "[] \<lhd> []" |
  Cons: "is \<lhd> ds \<Longrightarrow> i<d \<Longrightarrow> i#is \<lhd> d#ds"

(* No idea what these are used for*)
inductive_cases valid_indexE[elim]: "is \<lhd> ds"
inductive_cases valid_index_dimsE[elim]: "is \<lhd> dims A"

(* Valid indices \<Rightarrow> same order *)
lemma valid_index_length: "is \<lhd> ds \<Longrightarrow> length is = length ds"
  by (induction rule:valid_index.induct; auto)

(* Valid indices \<Rightarrow> any index valid *)
lemma valid_index_lt: "is \<lhd> ds \<Longrightarrow> m<length ds \<Longrightarrow> is!m < ds!m"
proof (induction arbitrary:m rule:valid_index.induct)
  case Nil
  then show ?case by auto
next
  case Cons
  then show ?case by (metis gr0_conv_Suc length_Cons linorder_neqE_nat not_less_eq nth_Cons' nth_Cons_Suc)
qed


(* Construct valid index from conditions *)
lemma valid_indexI:
assumes "length is = length ds" and "\<And>m. m<length ds \<Longrightarrow> is!m < ds!m"
shows "is \<lhd> ds"
using assms proof (induction "is" arbitrary:ds)
  case Nil
  then show ?case by (metis length_0_conv valid_index.simps)
next
  case (Cons a "is" ds)
  then obtain d ds' where "ds = d # ds'" by (metis length_Suc_conv)
  then have "is \<lhd> ds'" using Cons by (metis length_Cons less_irrefl linorder_neqE_nat not_less_eq nth_Cons_Suc)
  then show ?case using Cons.prems(2) \<open>ds = d # ds'\<close> valid_index.Cons by fastforce
qed


lemma valid_index_append:
assumes is1_valid:"is1 \<lhd> ds1" and is2_valid:"is2 \<lhd> ds2"
shows "is1 @ is2 \<lhd> ds1 @ ds2"
  apply (rule valid_indexI[of "is1 @ is2" "ds1 @ ds2"])
  unfolding nth_append
  using valid_index_lt[OF is2_valid] valid_index_lt[OF is1_valid] valid_index_length[OF is1_valid] valid_index_length[OF is2_valid] length_append
  by (auto simp add: \<open>length is1 = length ds1\<close>)

lemma valid_index_list_all2_iff: "is \<lhd> ds \<longleftrightarrow> list_all2 (<) is ds"
by (metis list_all2_conv_all_nth list_all2_nthD valid_indexI valid_index_length valid_index_lt)

(* Added by Matt *)
(* Added by Matt - very useful for when indices must be split *)
lemma valid_index_take:
  assumes "is@is' \<lhd> ds"
  shows "is \<lhd> take (length is) ds"
  using assms
  by (metis append_eq_conv_conj list_all2_takeI valid_index_list_all2_iff) 


(* Needed to enable code generation for valid index *)
fun valid_index_imp_base :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "valid_index_imp_base [] ds = True"
| "valid_index_imp_base is [] = True"
| valid_index_imp_base_Cons: "valid_index_imp_base (i#is) (d#ds) = (if i < d then valid_index_imp_base is ds else False)"

(* Needed to enable code generation for valid index *)
definition valid_index_imp :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
 "valid_index_imp is ds = (if length is = length ds then valid_index_imp_base is ds else False)"

(* Needed to enable code generation for valid index *)
lemma valid_index_base_bounded:
shows "length is = length ds \<Longrightarrow> (valid_index_imp_base is ds) \<Longrightarrow> (\<And>m. m<min (length is) (length ds) \<Longrightarrow> is!m < ds!m)"
proof (induction "is" arbitrary: ds)
  case Nil
  thus ?case by auto  
next
  case (Cons i "is")
  then obtain d ds' where "ds = d # ds'" by (metis length_Suc_conv)
  thus ?case
    by (metis Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(3) Tensor.valid_index_imp_base_Cons add_diff_cancel_left'
        length_Cons less_Suc_eq_0_disj min.idem nth_Cons' plus_1_eq_Suc) 
qed

(* Needed to enable code generation for valid index *)
lemma valid_index_implies_valid_index_imp:
  shows "is \<lhd> ds \<Longrightarrow> valid_index_imp is ds"
proof (induction "is" arbitrary: ds)
  case Nil
  hence "ds = []" by auto
  thus ?case by (simp add: valid_index_imp_def)  
next
  case (Cons i "is")
  then show ?case proof (induction ds)
    case Nil
    then show ?case by blast 
  next
    case (Cons d ds)
    hence "i < d" by blast 
    moreover have "valid_index_imp is ds" using Cons.prems(1) Cons.prems(2) by blast 
    ultimately show ?case using valid_index_imp_base_Cons Cons.prems(2) valid_index_length valid_index_imp_def
      by fastforce 
  qed
qed

(* Needed to enable code generation for valid index *)
lemma valid_index_imp_equiv[code]:
  shows "(is \<lhd> ds) = valid_index_imp is ds"
proof (cases "is = [] \<and> ds = []")
  case True
  then show ?thesis by (simp add: valid_index.Nil valid_index_imp_def) 
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) min_less_iff_conj valid_indexI valid_index_base_bounded valid_index_imp_def
        valid_index_implies_valid_index_imp) 
qed


(* Take slice from list *)
definition fixed_length_sublist::"'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"fixed_length_sublist xs l i = (take l (drop (l*i) xs))"


(* By Matt, additional lemmas to clarify behaviour of above definition *)
lemma fixed_length_sublist_length[simp]:
  assumes "l*(i+1) \<le> length xs"
  shows "length (fixed_length_sublist xs l i) = l"
proof -
  from assms have "length (drop (l*i) xs) \<ge> l" by simp
  thus ?thesis by (simp add: fixed_length_sublist_def) 
qed

lemma take_drop_nth[simp]:
  assumes "j+l \<le> length xs"
    and "k < l"
  shows "xs ! (j + k) = take l (drop j xs) ! k"
  using assms(1) assms(2) by force

lemma fixed_length_sublist_nth[simp]:
  assumes "l*(i+1) \<le> length xs"
    and "k < l"
  shows "xs ! (l*i + k) = (fixed_length_sublist xs l i) ! k"
  using assms fixed_length_sublist_def take_drop_nth
  by (metis distrib_left nat_mult_1_right)


(* Implementation verion of fixed_length_sublist *)
definition subarray::"'a iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a iarray" where
"subarray xs l j = IArray (map (\<lambda>i. xs !! (i+j)) [0..<l])"

lemma subarray_take_drop_equiv[simp]:
  assumes "l+j \<le> IArray.length axs"
  shows "subarray axs l j = IArray (take l (drop j (IArray.list_of axs)))"
proof -
  have "map (\<lambda>i. axs !! (i+j)) [0..<l] = map (\<lambda>i. axs !! i) [j..<(j+l)]" using add.commute nth_equalityI
    by (smt (verit, del_insts) add_diff_cancel_left' diff_zero length_map length_upt nth_map_upt) 
  thus ?thesis using assms
    by (metis add.commute drop_map drop_upt list_of_code plus_nat.add_0 subarray_def take_map take_upt) 
qed

lemma length_preserved[simp]:
  shows "IArray.length (subarray axs l j) = l"
  by (simp add: subarray_def)

(* Optimised version of fixed_length_sublist based on array access *)
fun fixed_length_sublist_imp::"'a iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a iarray" where
"fixed_length_sublist_imp xs l i = subarray xs l (l*i)"

lemma fixed_length_sublist_equiv:
  assumes "l*(i+1) \<le> length xs"
  shows "IArray (fixed_length_sublist xs l i) = fixed_length_sublist_imp (IArray xs) l i"
  using assms by (simp add: fixed_length_sublist_def)


(* This lookup definition is costly due to the use of fixed_length_sublist *)
fun lookup_base::"nat list \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> 'a" where
  "lookup_base (v # va) b [] = undefined" |
  "lookup_base [] b (v # va) = undefined" |
  lookup_base_Nil: "lookup_base [] v [] = hd v" |
  lookup_base_Cons: "lookup_base (d # ds) v (i # is) =
    lookup_base ds (fixed_length_sublist v (prod_list ds) i) is"


lemma lookup_base_single:
  assumes "d = length xs"
  and "i<d"
  shows "lookup_base [d] xs [i] = xs ! i"
  using assms
  by (simp add: fixed_length_sublist_def hd_drop_conv_nth) 

lemma lookup_base_double:
  assumes "d = length xs"
  and "i<d"
  shows "lookup_base [d] xs [i] = xs ! i"
  using assms
  by (simp add: fixed_length_sublist_def hd_drop_conv_nth) 


(* This result gives clarity but is not used in any proofs *)
lemma fls_induct_step:
  assumes "l*(i+1) \<le> length xs"
  and "l' * (i' + 1) \<le> l"
shows "fixed_length_sublist (fixed_length_sublist xs l i) l' i' = take l' (drop (l*i + l'*i') xs)"
  by (smt (verit, ccfv_threshold) ab_semigroup_add_class.add_ac(1) add.commute append_eq_conv_conj 
assms(2) distrib_left drop_drop fixed_length_sublist_def le_iff_add length_take linorder_linear
  min.absorb2 mult.comm_neutral take_add take_all)


fun flattened_index:: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
 flattened_index_Nil_1: "flattened_index [] is = 0"
| flattened_index_Nil_2: "flattened_index ds [] = 0"
| flattened_index_Cons: "flattened_index (d#ds) (i#is) = (i * prod_list ds) + (flattened_index ds is)"


lemma flattened_index_lt_prod_list[simp]:
  assumes "is \<lhd> ds"
  shows "flattened_index ds is < prod_list ds"
  using assms proof (induction rule:valid_index.induct)
  case Nil
  then show ?case by simp 
next
  case A: (Cons "is" ds i d)
  hence "flattened_index (d#ds) (i#is) \<le> (i + 1) * (prod_list ds)" by simp 
  from this and A show ?case using prod_list_cons
    by (smt (verit, best) Tensor.flattened_index_Cons add_left_cancel add_mult_distrib discrete
        leD mult_1 mult_le_mono1 nat_neq_iff order.strict_trans1) 
qed

fun unflattened_index:: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  unflattened_index_Nil: "unflattened_index [] j = []"
| unflattened_index_Cons: "unflattened_index (d#ds) j = (j div (prod_list ds)) # unflattened_index ds (j mod (prod_list ds))"

fun unflattened_index_imp:: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  unflattened_index_imp_Nil: "unflattened_index_imp [] j = []"
| unflattened_index_imp_Cons: "unflattened_index_imp (s#ss) j = (j div s) # unflattened_index_imp ss (j mod s)"

fun strides :: "nat list \<Rightarrow> nat list" where
"strides [] = []"
| "strides (d#ds) = (prod_list ds) # (strides ds)"

lemma strides_length:
  "length (strides ds) = length ds"
  by (induction ds; auto)

lemma strides_drop:
  "drop i (strides ds) = (strides (drop i ds))"
proof (induction i arbitrary: ds)
  case 0
  then show ?case by simp 
next
  case (Suc i)
  then show ?case by (metis strides.elims drop_Nil drop_Suc list.sel(3)) 
qed

lemma unflattened_index_imp_works[simp]:
  "unflattened_index ds' i = unflattened_index_imp (strides ds') i"
  by (induction ds' arbitrary: i; auto)

fun flattened_index_imp:: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  flattened_index_Nil_1_imp: "flattened_index_imp [] is = 0"
| flattened_index_Nil_2_imp: "flattened_index_imp ss [] = 0"
| flattened_index_Cons_imp: "flattened_index_imp (s#ss) (i#is) = (i * s) + (flattened_index_imp ss is)"

lemma flattened_index_imp_map2:
  "flattened_index_imp ss is = sum_list (map2 (*) ss is)"
proof (induction ss arbitrary: "is")
  case Nil
  then show ?case
    by simp 
next
  case (Cons a ss)
  then show ?case by (induction "is"; simp)
qed


lemma flattened_index_imp_split:
  assumes "length ss = length is"
  shows "flattened_index_imp (ss@ss') (is@is') = flattened_index_imp ss is + flattened_index_imp ss' is'"
  by (simp add: assms flattened_index_imp_map2)


(* This is very useful as it will allow flattened_index to be split *)
lemma flattened_index_imp_works:
  "flattened_index ds' is' = flattened_index_imp (strides ds') is'"
proof (induction ds' arbitrary: "is'")
  case Nil
  then show ?case
    by simp 
next
  case A: (Cons d ds)
  then show ?case proof (induction "is'")
    case Nil
    then show ?case by simp
  next
    case B: (Cons i "is")
    then have "strides (d#ds) = (prod_list ds) # strides ds" by simp
    from this have "flattened_index_imp (strides (d#ds)) (i#is) = i * (prod_list ds) + flattened_index_imp (strides ds) is"
      by simp 
    moreover have "flattened_index (d#ds) (i#is) = i * prod_list ds + flattened_index ds is" by simp
    ultimately show ?case using A B by presburger 
  qed
qed

lemma flattened_invertible[simp]:
  assumes "is \<lhd> ds"
  shows "unflattened_index ds (flattened_index ds is) = is"
using assms proof (induction rule:valid_index.induct)
  case Nil
  then show ?case  by simp 
next
  case (Cons "is" ds i d)
  have A: "flattened_index (d#ds) (i#is) = (i * prod_list ds) + (flattened_index ds is)" by simp
  moreover have B: "flattened_index ds is < prod_list ds" using Cons.hyps(1) flattened_index_lt_prod_list by blast
  ultimately have "(flattened_index (d#ds) (i#is)) div (prod_list ds) = i" by simp
  moreover have "(flattened_index (d#ds) (i#is)) mod (prod_list ds) = (flattened_index ds is)" using A B by auto
  ultimately show ?case using Cons.IH Tensor.unflattened_index_Cons by presburger 
qed

lemma unflattened_valid[simp]:
   "j < prod_list ds \<Longrightarrow> (unflattened_index ds j) \<lhd> ds"
proof (induction "ds" arbitrary: "j")
  case Nil
  then show ?case by (simp add: valid_index.Nil) 
next
  case (Cons a ds)
  then show ?case
    by (metis Tensor.unflattened_index_Cons add_lessD1 gr_zeroI mod_less_divisor mult.commute mult_0_right mult_div_mod_eq nat_mult_less_cancel1 prod_list_cons valid_index.Cons) 
qed

lemma unflattened_invertible[simp]:
  shows "j < prod_list ds \<Longrightarrow> flattened_index ds (unflattened_index ds j) = j"
 proof (induction "ds" arbitrary: "j")
  case Nil
  then show ?case by simp
next
  case (Cons a ds)
  then have "unflattened_index (a#ds) j = (j div (prod_list ds)) # unflattened_index ds (j mod (prod_list ds))" by simp
  then show ?case
    by (metis Cons.IH Cons.prems flattened_index_Cons div_mod_decomp gr_zeroI mod_by_0 mod_less_divisor mult_is_0 prod_list_cons) 
qed

lemma prod_list_nneg[simp]:
  fixes ds :: "nat list"
  assumes "prod_list (d#ds) > 0"
  shows "prod_list ds > 0"
  using assms by force 

lemma valid_index_nonneg:
  assumes "is \<lhd> ds"
  shows "prod_list ds > 0"
  using assms flattened_index_lt_prod_list gr_implies_not_zero by blast 

(* Important result relating lookup_base and flattened_index access *)
theorem lookup_index:
  assumes A: "is \<lhd> ds"
  shows "(length xs = prod_list ds) \<Longrightarrow> lookup_base ds xs is = xs ! (flattened_index ds is)"
using A proof (induction arbitrary: "xs" rule:valid_index.induct)
  case Nil
  thus ?case using hd_conv_nth A
    by (metis Tensor.flattened_index_Nil_1 Tensor.lookup_base_Nil list.size(3) one_neq_zero prod_list_nil) 
next
  case I: (Cons "is" ds i d)
  have B: "flattened_index (d # ds) (i # is) = (i * prod_list ds) + (flattened_index ds is)"
    by simp
  let ?sub_xs = "fixed_length_sublist xs (prod_list ds) i"
  from I have "length ?sub_xs = (prod_list ds)"
    by (metis Suc_leI add.commute fixed_length_sublist_length mult.commute mult_le_cancel2 plus_1_eq_Suc prod_list_cons) 
  from this I have "lookup_base ds ?sub_xs is = ?sub_xs ! flattened_index ds is" by simp
  hence "lookup_base (d#ds) xs (i#is) = ?sub_xs ! flattened_index ds is" using lookup_base_Cons by simp
  thus ?case using I B by (metis (no_types, lifting) discrete fixed_length_sublist_nth
        flattened_index_lt_prod_list mult.commute mult_le_mono2 prod_list_cons)
qed


definition lookup::"'a tensor \<Rightarrow> nat list \<Rightarrow> 'a" where
  "lookup A = lookup_base (dims A) (vec_list A)"

definition lookup_imp::"'a tensor \<Rightarrow> nat list \<Rightarrow> 'a" where
  "lookup_imp A is = (vec A) !! flattened_index (dims A) is"


(* Very important equivalence *)
theorem lookup_equiv_lookup_imp:
  assumes "is \<lhd> (dims A)"
  shows "lookup A is = lookup_imp A is"
  using lookup_index lookup_def lookup_imp_def
  by (metis IArray.sub_def assms tensor_dim_vec_list_invariant vec_list_vec)
  


lemma flatten_unflatten_1:
  assumes "j < prod_list ds"
  and "a < d"
  shows "flattened_index (d#ds) (a#(unflattened_index ds j)) = j + a*(prod_list ds)"
  using assms(1)
  using unflattened_invertible by force 


lemma flatten_unflatten_2:
  assumes "j < ds"
  and "a < d"
shows "flattened_index ([ds,d]) [j,a] = (j*d + a)"
  by simp


theorem lookup_imp_unflattened_equivalence:
  assumes "j < prod_list (dims A)"
  shows "(vec A) !! j = lookup_imp A (unflattened_index (dims A) j)"
  unfolding lookup_imp_def using assms unflattened_invertible by auto 

theorem lookup_unflattened_equivalence:
  assumes "j < prod_list (dims A)"
  shows "(vec A) !! j = lookup A (unflattened_index (dims A) j)"
  using assms by (metis lookup_imp_unflattened_equivalence lookup_equiv_lookup_imp unflattened_valid) 


(* [0..<] prevents conversion to integers *)
(* This is really useful but the concat's will definitely be slow, worth an optimisation *)
fun tensor_vec_from_lookup::"nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  tensor_vec_from_lookup_Nil: "tensor_vec_from_lookup [] e = [e []]" |
  tensor_vec_from_lookup_Cons: "tensor_vec_from_lookup (d # ds) e = concat (map (\<lambda>i. tensor_vec_from_lookup ds (\<lambda>is. e (i # is))) [0..<d])"


(* This is incredibly useful *)
abbreviation tensor_vec_from_lookup_imp::"nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a iarray" where
 "tensor_vec_from_lookup_imp ds e \<equiv> IArray (map (\<lambda>i. e (unflattened_index ds i)) [0..<(prod_list ds)])"


lemma tensor_vec_from_lookup_imp_elem:
  assumes "j < prod_list ds"
  shows "(tensor_vec_from_lookup_imp ds e) !! j = e (unflattened_index ds j)"
  by (simp add: assms)

lemma unflattened_index_leading_dim:
  assumes  "i \<ge> k * (prod_list ds)"
and "i < (k+1) * (prod_list ds)"
shows "hd (unflattened_index (d#ds) i) = k"
  by (smt (verit, del_insts) Tensor.unflattened_index_Cons add.commute add.right_neutral
add_less_cancel_right assms(1) assms(2) div_less div_mult_self3 le_iff_add linorder_not_le list.sel(1) mult_Suc plus_1_eq_Suc)


definition tensor_from_lookup_imp::"nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a tensor" where
  "tensor_from_lookup_imp ds e = tensor_from_vec ds (tensor_vec_from_lookup_imp ds e)"


definition tensor_from_lookup::"nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a tensor" where
  "tensor_from_lookup ds e = tensor_from_vec ds (IArray (tensor_vec_from_lookup ds e))"


(* THIS IS A FUNDAMENTAL THEOREM *)
(*
The proof relies on the fact that, for valid indices, \texttt{lookup} and \texttt{lookup_imp} are equivalent.
Moreover, \texttt{lookup_imp} extracts an element from its flattened index. Therefore, the left-hand side of 
the equation involves the composition of \texttt{unflattened_index} and \texttt{flattened_index}, which cancel one another out.
*)
theorem lookup_inverts_tensor_from_lookup_imp:
  assumes valid_index: "is \<lhd> ds"
shows "lookup (tensor_from_lookup_imp ds e) is = e is" 
proof -
  let ?A = "tensor_from_lookup_imp ds e"
  from assms have "ds = dims ?A" by (simp add: tensor_from_lookup_imp_def)
  from this valid_index lookup_equiv_lookup_imp have "lookup ?A is = (vec ?A) !! flattened_index (dims ?A) is"
    using lookup_imp_def by metis 
  moreover from valid_index have "flattened_index (dims ?A) is < prod_list ds" using \<open>ds = dims ?A\<close> flattened_index_lt_prod_list by simp
  ultimately have "lookup ?A is = e (unflattened_index ds (flattened_index ds is))"
    by (simp add: assms(1) tensor_from_lookup_imp_def)
  thus ?thesis using valid_index flattened_invertible by simp
qed


lemma concat_parts_leq:
assumes "a * d \<le> length v"
shows "concat (map (fixed_length_sublist v d) [0..<a]) = take (a*d) v"
using assms proof (induction a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  then have "concat (map (fixed_length_sublist v d) [0..<a]) = take (a * d) v" by auto
  then have "concat (map (fixed_length_sublist v d) [0..<Suc a]) =
        take (a * d) v @ fixed_length_sublist v d a" using fixed_length_sublist_def by auto
  then show ?case using Suc by (metis add.commute mult.commute mult_Suc take_add fixed_length_sublist_def)
qed


(* VERY USEFUL *)
lemma concat_parts_eq:
assumes "a * d = length v"
shows "concat (map (fixed_length_sublist v d) [0..<a]) = v"
by (simp add: concat_parts_leq assms)

lemma tensor_lookup_base:
assumes "length v = prod_list ds"
and "\<And>is. is \<lhd> ds \<Longrightarrow> lookup_base ds v is = e is"
shows "tensor_vec_from_lookup ds e = v"
using assms proof (induction ds arbitrary:v e)
  case Nil
  then show ?case unfolding tensor_vec_from_lookup.simps
    by (metis One_nat_def Tensor.lookup_base_Nil length_0_conv length_Suc_conv list.sel(1) prod_list_nil valid_index.Nil)
next
  case (Cons a ds)
  then have "a * prod_list ds = length v" by auto
  {
    fix i assume "i<a"
    then have "prod_list ds * (i+1) \<le> length v" using \<open>a * prod_list ds = length v\<close> using discrete mult.commute mult_le_mono1 by metis
    have "\<And>is'. is' \<lhd> ds \<Longrightarrow> e (i # is') = lookup_base ds (fixed_length_sublist v (prod_list ds) i) is'"
      using \<open>i<a\<close> by (metis Cons.prems(2) Tensor.lookup_base_Cons valid_index.simps)
    then have "tensor_vec_from_lookup ds (\<lambda>is'. e (i # is')) = fixed_length_sublist v (prod_list ds) i"
      using Cons using \<open>prod_list ds * (i + 1) \<le> length v\<close> by (simp add: Cons.IH fixed_length_sublist_def)
  }
  then show ?case unfolding tensor_vec_from_lookup_Cons lookup_base_Cons
    using   concat_parts_eq[OF \<open>a * prod_list ds = length v\<close>]
     atLeastLessThan_iff map_eq_conv set_upt Cons by (metis (no_types, lifting))
qed

(* MATT'S CODE *)

lemma tensor_from_lookup_flattened_index:
assumes "length v = prod_list ds"
shows "tensor_vec_from_lookup ds (\<lambda>is. v ! (flattened_index ds is)) = v"
  by (simp add: assms lookup_index tensor_lookup_base)

(* ----------- *)

lemma tensor_lookup:
assumes "\<And>is. is \<lhd> dims A \<Longrightarrow> lookup A is = e is"
shows "tensor_from_lookup (dims A) e = A"
  using tensor_lookup_base lookup_def tensor_from_lookup_def
  by (metis assms tensor_dim_vec_list_invariant tensor_from_vec_simp vec_vec_list)

(* MATT'S CODE *)
lemma tensor_lookup_flattened_index:
shows "tensor_from_lookup (dims A) (\<lambda>is. (vec_list A) ! (flattened_index (dims A) is)) = A"
  by (metis IArray.length_def lookup_def lookup_index tensor_dim_vec_invariant tensor_lookup vec_def vec_list_def)

(* This is also very signficant as tensor_from_lookup_imp will be much more efficient in practice *)
lemma tensor_lookup_imp_flattened_index:
  shows "tensor_from_lookup_imp (dims A) (\<lambda>is. (vec_list A) ! (flattened_index (dims A) is)) = A"
  by (metis (no_types, lifting) IArray.length_def dims_tensor length_map list_of.simps map_nth tensor_dim_vec_list_invariant tensor_from_lookup_imp_def lookup_inverts_tensor_from_lookup_imp tensor_lookup tensor_lookup_flattened_index)

(* Very significant result *)
theorem tensor_from_lookup_imp_equiv[code]:
  shows "tensor_from_lookup ds e = tensor_from_lookup_imp ds e"
  using lookup_inverts_tensor_from_lookup_imp tensor_lookup
  by (metis (no_types, lifting) IArray.length_def diff_zero dims_tensor length_map length_upt list_of.simps tensor_from_lookup_imp_def) 

(* ----------- *)

lemma concat_equal_length:
assumes "\<And>xs. xs\<in>set xss \<Longrightarrow> length xs = l"
shows "length (concat xss) = length xss*l"
using assms by (induction xss;auto)

lemma concat_equal_length_map:
assumes "\<And>i. i<a \<Longrightarrow> length (f i) = d"
shows "length (concat (map (\<lambda>i. f i) [0..<a])) = a*d"
using assms by (induction a;auto)

lemma concat_parts:
assumes "\<And>xs. xs\<in>set xss \<Longrightarrow> length xs = d" and "i<length xss"
shows "fixed_length_sublist (concat xss) d i = xss ! i"
using assms proof (induction xss arbitrary:i)
  case Nil
  then show ?case by simp
next
  case (Cons xs xss)
  then have "length (concat xss) = length xss * d" by (simp add: Cons.prems(1) concat_equal_length)
  show ?case
  proof (cases i)
    case 0
    then have "fixed_length_sublist (concat (xs # xss)) d i = xs"
      unfolding fixed_length_sublist_def by (simp add: Cons.prems(1))
    then show ?thesis using 0 by auto
  next
    case (Suc i')
    then have "fixed_length_sublist (concat xss) d i' = xss ! i'" using Cons by auto
    then show ?thesis unfolding fixed_length_sublist_def using Suc Cons.prems(1) by auto
  qed
qed

lemma concat_parts':
assumes "\<And>i. i<a \<Longrightarrow> length (f i) = d"
and "i<a"
shows "fixed_length_sublist (concat (map (\<lambda>i. f i) [0..<a])) d i = f i"
using assms proof (induction a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  then have "(\<And>i. i < a \<Longrightarrow> length (f i) = d)" by auto
  then have "length (concat (map f [0..<a])) = a*d" using concat_equal_length_map by auto
  show ?case
  proof (cases "i=a")
    assume "i=a"
    then have "fixed_length_sublist (concat (map f [0..<Suc a])) d i = f a"
      by (simp add: Suc.prems(1) \<open>length (concat (map f [0..<a])) = a * d\<close> fixed_length_sublist_def)
    then show ?case using \<open>i=a\<close> by auto
  next
    assume "i\<noteq>a"
    then have "fixed_length_sublist (concat (map f [0..<a])) d i = f i"
      "concat (map f [0..<Suc a]) = concat (map f [0..<a]) @ f a" using Suc by auto
    show ?case unfolding \<open>concat (map f [0..<Suc a]) = concat (map f [0..<a]) @ f a\<close>
      unfolding fixed_length_sublist_def drop_append
      using  \<open>length (concat (map f [0..<a])) = a * d\<close>  \<open>fixed_length_sublist (concat (map f [0..<a])) d i = f i\<close>
      using append_assoc append_eq_conv_conj append_take_drop_id assms(1) assms(2)  fixed_length_sublist_def
      by metis
  qed
qed

lemma length_tensor_vec_from_lookup:
"length (tensor_vec_from_lookup ds e) = prod_list ds"
  by (induction ds arbitrary:e; auto simp add: concat_equal_length_map)

lemma lookup_tensor_vec:
assumes "is\<lhd>ds"
shows "lookup_base ds (tensor_vec_from_lookup ds e) is = e is"
using assms proof (induction arbitrary:e rule:valid_index.induct)
  case Nil
  then show ?case by simp
next
  case (Cons "is" ds i d e)
  then show ?case unfolding tensor_vec_from_lookup_Cons lookup_base_Cons
    by (simp add: concat_parts' length_tensor_vec_from_lookup)
qed

lemma lookup_tensor_from_lookup:
assumes "is\<lhd>ds"
shows "lookup (tensor_from_lookup ds e) is = e is"
  unfolding lookup_def tensor_from_lookup_def
  by (simp add: assms length_tensor_vec_from_lookup lookup_tensor_vec vec_list_vec)

(* MATT'S CODE *)

lemma lookup_tensor_from_lookup_imp:
assumes "is\<lhd>ds"
shows "lookup_imp (tensor_from_lookup_imp ds e) is = e is"
  unfolding lookup_imp_def tensor_from_lookup_imp_def
  using assms flattened_index_lt_prod_list
  using flattened_invertible by auto 

(*--------------------------------------------------------------*)

lemma dims_tensor_from_lookup: "dims (tensor_from_lookup ds e) = ds"
  unfolding tensor_from_lookup_def
  by (simp add: length_tensor_vec_from_lookup)

lemma vec_tensor_from_lookup: "vec (tensor_from_lookup ds e) = IArray (tensor_vec_from_lookup ds e)"
  unfolding tensor_from_lookup_def
  by (simp add: length_tensor_vec_from_lookup)

lemma tensor_lookup_cong:
assumes "tensor_from_lookup ds e\<^sub>1 = tensor_from_lookup ds e\<^sub>2"
and "is\<lhd>ds"
shows "e\<^sub>1 is = e\<^sub>2 is" using assms lookup_tensor_from_lookup by metis

lemma tensor_from_lookup_eqI:
assumes "\<And>is. is\<lhd>ds \<Longrightarrow> e\<^sub>1 is = e\<^sub>2 is"
shows "tensor_from_lookup ds e\<^sub>1 = tensor_from_lookup ds e\<^sub>2"
by (metis assms lookup_tensor_vec length_tensor_vec_from_lookup tensor_lookup_base tensor_from_lookup_def)

lemma tensor_lookup_eqI:
assumes "dims A = dims B" and "\<And>is. is\<lhd>(dims A) \<Longrightarrow> lookup A is = lookup B is"
shows "A = B" by (metis assms(1) assms(2) tensor_lookup)


(* Very useful theorem *)
theorem tensor_vec_from_lookup_imp_equiv:
  shows "IArray (tensor_vec_from_lookup ds e) = tensor_vec_from_lookup_imp ds e"
proof -
  have "vec (tensor_from_lookup ds e) = tensor_vec_from_lookup_imp ds e" by (simp add: tensor_from_lookup_imp_equiv tensor_from_lookup_imp_def) 
  thus ?thesis by (simp add: vec_tensor_from_lookup)
qed

definition tensor_vec_from_lookup_imp'::"nat \<Rightarrow> nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a iarray" where
 "tensor_vec_from_lookup_imp' k ss e \<equiv> IArray (map (\<lambda>i. e (unflattened_index_imp ss i)) [0..<k])"
                                                                
lemma tensor_vec_from_lookup_imp'_equiv:
  "tensor_vec_from_lookup_imp ds e = tensor_vec_from_lookup_imp' (prod_list ds) (strides ds) e"
  by (simp add: tensor_vec_from_lookup_imp'_def)


lemma tensor_lookup_codegen[simp, code abstract]:
  "Rep_tensor (tensor_from_lookup ds e) = (ds, tensor_vec_from_lookup_imp ds e)"
  by (simp add: invertability_condition tensor_from_lookup_def tensor_from_vec_def tensor_vec_from_lookup_imp_equiv)

(* Required to enable codegen *)
lemma tensor_lookup_imp_codegen[simp, code abstract]:
  "Rep_tensor (tensor_from_lookup_imp ds e) = (ds, tensor_vec_from_lookup_imp' (prod_list ds) (strides ds) e)"
  using tensor_vec_from_lookup_imp'_equiv by (simp add: invertability_condition tensor_from_lookup_imp_def tensor_from_vec_def)

end