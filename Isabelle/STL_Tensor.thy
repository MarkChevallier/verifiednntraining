theory STL_Tensor

imports Complex_Main Tensor Lequal_Nequal Nequal Tensor_Constants STL HOL.Divides
begin

(*
tensor dimensions:
time x state x batch

- could change to:

TENSOR
1st subtensor: time
2nd subtensor: 1st state variable
3rd subtensor: 2nd state variable
etc etc
*)

lemma nonempty_tensor_dims_not_0:
  fixes A :: "'a tensor" and n m :: nat
  assumes "length (dims A) = n" "m<n" "length (vec_list A) > 0"
  shows "dims A!m > 0"
proof -
  have "prod_list (dims A) > 0"
    using assms(3)
    by simp
  {
    assume "\<not>dims A!m > 0"
    then have "dims A!m = 0"
      by fast
    then have "0 \<in> set (dims A)"
      by (metis assms(1) assms(2) list_update_id set_update_memI)
    then have "prod_list (dims A) = 0"
      by (simp add: prod_list_zero_iff)
    then have False
      using \<open>prod_list (dims A) > 0\<close>
      by presburger}
  then show ?thesis
    by argo
qed

definition valid_signal_tensor :: "real tensor \<Rightarrow> bool" where
"valid_signal_tensor A = 
  (length (dims A) = 2 \<and> length (vec_list A) > 0
  \<and> (\<forall>m n. m < dims A!0 \<and> n < dims A!0 \<and> m<n \<longrightarrow> lookup_imp A [m,0] < lookup_imp A [n,0]))"

(* if you use tensor_1d_binary_search_n starting with L = 0 and R = dims A!0-1, this should return
(Suc n) where the lookup for n-1 \<le> a and for n \<ge> a; it returns (Suc 0) if lookup for 0 \<ge> a. 
It should return 0 if no such n exists. *) 

definition interval_start_1d :: "'a::linorder tensor \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"interval_start_1d A a X n = (n \<ge> X \<and> lookup_imp A [n] \<ge> a \<and> (lookup_imp A [n-1] \<le> a \<or> n=X))"

definition interval_start_2d :: "'a::linorder tensor \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"interval_start_2d A a X n = (n \<ge> X \<and> lookup_imp A [n,0] \<ge> a \<and> (lookup_imp A [n-1,0] \<le> a \<or> n=X))"

(*
  Offset is initial starting index
  Start+offset is the current iteration's starting index
  Width is number of *extra* steps to go beyond the start

  Output is index of the first element (i.e. with least index) in (first dimension of) A greater than
  or equal to the sought threshold a, such that it is within width steps of start+offset.

  If width is zero (window of just one element):
  - Check if element at start+offset is geq to sought a:
    - If so, check if there is previous element (if start+offset > 0):
      (looking for witness of threshold, so okay to look outside our area)
      - If so, check if it is less than sought a:
        - If so, return start+offset index
        - Otherwise, return nothing (this element is not eligible threshold)
      - Otherwise, return start+offset index (assume time before observations is less than every time)
    - Otherwise, return nothing (this element does not meet the threshold)
  In general:
  - Check if midpoint (start+offset + width div 2) is geq to sought a:
    - If so, recurse with same start and half width (left part including midpoint)
    - Otherwise, recurse with midpoint+1 as start and half width-1, so even width gives 1 less (right part excluding midpoint - it's less so not a candidate)

  Assumes:
  - A is sorted (along its first dimension)
  - A is not empty, otherwise not even with start and offset 0 will lookups work
  - offset+start+width < length of A's first dimension

  Could short-circuit in some situations of general case (check if midpoint is exactly what we want by chance).
  May be better as another definition refining this one just for code-generation purposes?
*)
function (sequential) first_above_threshold_1D :: "('a::linorder) tensor \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option"
  where
    "first_above_threshold_1D A a offset start 0 =
      ( if lookup_imp A [offset + start] < a then None
        else if start = 0 then Some offset
        else if lookup_imp A [nat.pred (offset + start)] < a then Some (offset + start)
        else None)"
  | "first_above_threshold_1D A a offset start width =
      ( if a \<le> lookup_imp A [offset + start + (width div 2)]
          then first_above_threshold_1D A a offset start (width div 2)
          else first_above_threshold_1D A a offset (Suc (start + (width div 2))) ((nat.pred width) div 2))"
  by pat_completeness auto
termination first_above_threshold_1D
  by (relation "Wellfounded.measure (\<lambda>(A, a, offset, start, width). width)") auto

lemma even_div2_add:
  "even n \<Longrightarrow> n div 2 + n div 2 = n"
  by (metis add_cancel_right_right mult_2 mult_div_mod_eq parity_cases)

lemma odd_div2_add:
  "odd n \<Longrightarrow> n div 2 + n div 2 = nat.pred n"
  by (cases n ; simp add: even_div2_add)

lemma plus_nat_pred:
  "y \<noteq> 0 \<Longrightarrow> x + nat.pred y = nat.pred (x + y)"
  by (cases y ; simp)

lemma nat_pred_Suc: (* Nat.nat.sel(2) is inaccessible for direct use *)
  "nat.pred (Suc v) = v"
  by simp

lemma nat_pred_less:
  "n \<noteq> 0 \<Longrightarrow> nat.pred n < n"
  by (cases n ; simp)

lemma first_above_threshold_1D_lower_bound:
  assumes "first_above_threshold_1D A a offset start width = Some n"
      and "length (dims A) = 1"
      and "length (vec_list A) > 0"
      and "offset + start + width < dims A ! 0"
      and "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
    shows "offset + start \<le> n"
  using assms
proof (induct A a offset start width arbitrary: n rule: first_above_threshold_1D.induct)
  case (1 A a offset start)
  then have "\<not>(lookup_imp A [offset + start] < a)"
    by fastforce
  then show ?case
    using nle_le not_None_eq option.inject 1
    by (metis add.right_neutral first_above_threshold_1D.simps(1))
next
  case (2 A a offset start v)
  then show ?case
  proof (cases "a \<le> lookup_imp A [offset + start + Suc v div 2]")
    case True
    then show ?thesis using 2(1,3-7) by simp
  next
    case False
    moreover have "offset + Suc (start + Suc v div 2) + nat.pred (Suc v) div 2 < dims A ! 0"
    proof (cases "even v")
      case True
      then show ?thesis using 2(6) by (simp add: add.assoc even_div2_add)
    next
      case False
      then show ?thesis using 2(6) by (simp only: add.assoc plus_nat.simps nat_pred_Suc)
    qed
    ultimately have "offset + Suc (start + Suc v div 2) \<le> n"
      using 2 by (metis first_above_threshold_1D.simps(2))
    then show ?thesis
      by simp
  qed
qed

lemma first_above_threshold_1D_upper_bound:
  assumes "first_above_threshold_1D A a offset start width = Some n"
      and "length (dims A) = 1"
      and "length (vec_list A) > 0"
      and "offset + start + width < dims A ! 0"
      and "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
    shows "n \<le> offset + start + width"
  using assms
proof (induct A a offset start width arbitrary: n rule: first_above_threshold_1D.induct)
  case (1 A a offset start)
  then have "\<not>(lookup_imp A [offset + start] < a)"
    by fastforce
  then show ?case
    using nle_le not_None_eq option.inject 1
    by (metis add.right_neutral first_above_threshold_1D.simps(1))
next
  case (2 A a offset start v)
  then show ?case
  proof (cases "a \<le> lookup_imp A [offset + start + Suc v div 2]")
    case True
    then show ?thesis using 2 by simp linarith
  next
    case False
    then show ?thesis using 2 by simp linarith
  qed
qed

lemma first_above_threshold_1D_geq_threshold:
  assumes "first_above_threshold_1D A a offset start width = Some n"
      and "length (dims A) = 1"
      and "length (vec_list A) > 0"
      and "offset + start + width < dims A ! 0"
      and "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
    shows "a \<le> lookup_imp A [n]"
  using assms
proof (induct A a offset start width arbitrary: n rule: first_above_threshold_1D.induct)
  case (1 A a offset start)
  then have "\<not>(lookup_imp A [offset + start] < a)"
    by fastforce
  then show ?case
    using linorder_not_less option.inject option.simps(3) 1
    by (metis add.right_neutral first_above_threshold_1D.simps(1))
next
  case (2 A a offset start v)
  then show ?case
    by (cases "a \<le> lookup_imp A [offset + start + Suc v div 2]") simp_all
qed

lemma
  assumes "first_above_threshold_1D A a offset start width = Some n"
      and "length (dims A) = 1"
      and "length (vec_list A) > 0"
      and "offset + start + width < dims A ! 0"
      and "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
    shows "\<And>m. \<lbrakk>offset \<le> m; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] < a"
  using assms
proof (induct A a offset start width arbitrary: n rule: first_above_threshold_1D.induct)
  case (1 A a offset start)

  have c1: "\<not> (lookup_imp A [offset + start] < a)"
    using 1(3) first_above_threshold_1D_geq_threshold by fastforce

  show ?case
  proof (cases "offset + start = 0")
    case True
    then show ?thesis using 1 c1 by simp
  next
    case c2: False

    have c3: "lookup_imp A [nat.pred (offset + start)] < a"
      using 1(3) c1 c2
      by (metis "1.prems"(1) "1.prems"(2) first_above_threshold_1D.simps(1) linorder_not_less option.inject option.simps(3))
    have n_neq_0: "n \<noteq> 0"
      using 1(2) c2 by linarith

    have "lookup_imp A [m] \<le> lookup_imp A [nat.pred n]"
    proof (cases "m = nat.pred n")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (intro 1(7))
        show "m < dims A ! 0"
          using 1(2-7) first_above_threshold_1D_upper_bound by (meson order_less_imp_le order_less_le_trans)
        show "nat.pred n < dims A ! 0"
          using 1(3-7) n_neq_0 nat_pred_less first_above_threshold_1D_upper_bound by (meson order_less_imp_le order_less_le_trans)
        show "m < nat.pred n"
          using 1(2) False by (metis Suc_lessI n_neq_0 nat_pred_Suc not0_implies_Suc not_less_eq)
      qed
    qed
    moreover have "lookup_imp A [nat.pred n] < a"
      using 1(3) c3 c1 
      by (metis add_cancel_right_right first_above_threshold_1D.simps(1) option.inject)
    ultimately show ?thesis
      by simp
  qed
next
  case (2 A a offset start v)
  then show ?case
  proof (cases "a \<le> lookup_imp A [offset + start + Suc v div 2]")
    case True
    then show ?thesis
      using 2(1,3-9) by simp
  next
    case False
    then show ?thesis
      using 2(2-9) by simp
  qed
qed

text\<open>Proofs that using @{const less_eq} instead of @{const less} in the sorting assumption is admissible\<close>
experiment begin
lemma
  fixes A :: "('a :: linorder) tensor"
  assumes "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
  shows "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m \<le> n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
  using assms by (case_tac "m = n" ; simp)
lemma
  fixes A :: "('a :: linorder) tensor"
  assumes "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m \<le> n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
  shows "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
  using assms by (case_tac "m = n" ; simp)
end

lemma
  assumes "length (dims A) = 1"
      and "length (vec_list A) > 0"
      and "offset + start + width < dims A ! 0"
      and "\<And>m n. \<lbrakk>m < dims A ! 0; n < dims A ! 0; m \<le> n\<rbrakk> \<Longrightarrow> lookup_imp A [m] \<le> lookup_imp A [n]"
      and "offset + start \<le> n"
      and "n \<le> offset + start + width"
      and "a \<le> lookup_imp A [n]"
      and "\<And>m. \<lbrakk>offset \<le> m; m < n\<rbrakk> \<Longrightarrow> lookup_imp A [m] < a"
    shows "first_above_threshold_1D A a offset start width = Some n"
  using assms(3,5,6)
proof (induct width arbitrary: start rule: less_induct)
  case (less width)
  then show ?case
  proof (cases width)
    case 0
    then show ?thesis
    apply simp
    apply safe
    apply simp_all
      using assms(7) less.prems(2,3) apply fastforce
    using less.prems(2,3) apply linarith
    using assms(7) less.prems(2,3) apply fastforce
    using less.prems apply fastforce
    using assms(7) less.prems(2,3) apply auto[1]
    using less.prems apply auto[1]
    using assms(8) less.prems(2,3) by (metis add.right_neutral add_is_0 le_add1 nat_pred_less order_antisym plus_nat_pred)
  next
    case (Suc w)
    then show ?thesis
    proof (cases "a \<le> lookup_imp A [offset + start + Suc w div 2]")
      case True

      have "first_above_threshold_1D A a offset start (Suc w div 2) = Some n"
      proof (rule less.hyps)
        show "Suc w div 2 < width"
          using Suc by simp
        show "offset + start + Suc w div 2 < dims A ! 0"
          using Suc less.prems by simp
        show "offset + start \<le> n"
          using less.prems by (meson leD le_add1 le_trans not_le_imp_less)
        show "n \<le> offset + start + Suc w div 2"
        using Suc True assms(8) by (metis ab_semigroup_add_class.add_ac(1) leD le_add1 not_le_imp_less)
      qed
      then show ?thesis
        using Suc True by simp
    next
      case False

      have "first_above_threshold_1D A a offset (Suc (start + Suc w div 2)) (w div 2) = Some n"
      proof (rule less.hyps)
        show "w div 2 < width"
          using Suc by simp
        show "offset + Suc (start + Suc w div 2) + w div 2 < dims A ! 0"
          using Suc less.prems by simp
        show "offset + Suc (start + Suc w div 2) \<le> n"
        proof (rule ccontr)
          assume "\<not> offset + Suc (start + Suc w div 2) \<le> n"
          then have "n < offset + Suc (start + Suc w div 2)"
            by simp
          then have "n \<le> offset + start + Suc w div 2"
            by simp
          then have "lookup_imp A [n] \<le> lookup_imp A [offset + start + Suc w div 2]"
            using assms(4) Suc less.prems(1) by force
          then have "a \<le> lookup_imp A [offset + start + Suc w div 2]"
            using assms(7) by simp
          moreover have "lookup_imp A [offset + start + Suc w div 2] < a"
            using False by simp
          ultimately show False
            by simp
        qed
        show "n \<le> offset + Suc (start + Suc w div 2) + w div 2"
          using Suc less.prems(3) by linarith
      qed
      then show ?thesis
        using Suc False by simp
    qed
  qed
qed

datatype ctermt = Get nat | Const real | Add ctermt ctermt | Mult ctermt ctermt | Uminus ctermt | Divide ctermt ctermt

fun Teval :: "ctermt \<Rightarrow> real tensor \<Rightarrow> real tensor" where
"Teval (Get m) A = iterated_subtensor A [m]"
| "Teval (Const r) A = (unop (\<lambda>x. r) A)"
| "Teval (Add c1 c2) A = (binop (+) (Teval c1 A) (Teval c2 A))"
| "Teval (Mult c1 c2) A = (binop (*) (Teval c1 A) (Teval c2 A))"
| "Teval (Uminus c) A = (unop (\<lambda>x. -1 * x) (Teval c A))"
| "Teval (Divide c1 c2) A = (binop (/) (Teval c1 A) (Teval c2 A))"

datatype constraintt = ctMu "ctermt \<Rightarrow> real tensor \<Rightarrow> real tensor" ctermt real | ctNot constraintt 
  | ctAnd constraintt constraintt | ctUntil real real constraintt constraintt

function evalt :: "real tensor \<Rightarrow> nat \<Rightarrow> constraintt \<Rightarrow> bool tensor" where
"evalt A n (ctMu f ct r) = (unop (\<lambda>x. (>) x r) (f ct (iterated_subtensor A [n])))"
| "evalt A n (ctNot c) = unop (Not) (evalt A n c)"
| "evalt A n (ctAnd c1 c2) = binop (\<and>) (evalt A n c1) (evalt A n c2)"
| "evalt A n (ctUntil x y c1 c2) 
  = (if n \<ge> (dims A!0) \<or> (y < 0 then False 
     else (x > 0 \<and> evalt A (n+1) (ctUntil (x+lookup_imp A [n,0]-lookup_imp A [n+1,0]) (y+lookup_imp A [n,0]-lookup_imp A [n+1,0]) c1 c2))
       \<or> (x \<le> 0 \<and> y \<ge> 0 \<and> evalt A n c1 \<and> evalt A n c2)
       \<or> (x \<le> 0 \<and> y \<ge> 0 \<and> evalt A n c1 
         \<and> evalt A (n+1) (ctUntil (x+lookup_imp A [n,0]-lookup_imp A [n+1,0]) (y+lookup_imp A [n,0]-lookup_imp A [n+1,0]) c1 c2)))"
  by pat_completeness auto
termination by (relation "Wellfounded.measure (\<lambda>(A,n,c). size c + (dims A!0 - n))") auto 

lemma evalt_Until_works:
  assumes "valid_signal_tensor A"
  shows "evalt A m (ctUntil x y c1 c2) = 
    (\<exists>n\<ge>m. n<dims A!0 \<and> evalt A n c1 \<and> evalt A n c2
      \<and> x+lookup_imp A [m,0] \<le> lookup_imp A [n,0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n,0]
      \<and> (\<forall>n'\<le>n. n'\<ge>m \<longrightarrow> x+lookup_imp A [m,0] > lookup_imp A [n',0]
        \<or> (x+lookup_imp A [m,0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n',0]
          \<and> evalt A n' c1)))"
proof -
  obtain dA where dA_defn:"dA = dims A!0"
    by simp
  then show ?thesis
  proof (induction "dA - 1 - m")
    case 0
    then have "m\<ge>dA - 1"
      by simp
    then show ?case
    proof -
      {assume ass1:"evalt A m (ctUntil x y c1 c2)"
        have "\<And>x y c1 c2. \<not>(evalt A (m+1) (ctUntil x y c1 c2))"
          using \<open>dA - 1 \<le> m\<close> le_diff_conv dA_defn 
          by auto
        then have b:"x \<le> 0 \<and> y \<ge> 0 \<and> evalt A m c1 \<and> evalt A m c2"
          using ass1 evalt.simps(4)
          by metis
        then have "\<exists>n\<ge>m. n<dA \<and> evalt A n c1 \<and> evalt A n c2
        \<and> x+lookup_imp A [m,0] \<le> lookup_imp A [n,0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n,0]
          \<and> (\<forall>n'\<le>n. n'\<ge>m \<longrightarrow> x+lookup_imp A [m,0] > lookup_imp A [n',0]
            \<or> (x+lookup_imp A [m,0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n',0]
              \<and> evalt A n' c1))"
          using ass1 evalt.simps(4) leI le_antisym le_refl dA_defn
          by (smt (verit))}
      then have oneway:"evalt A m (ctUntil x y c1 c2) \<Longrightarrow> (\<exists>n\<ge>m. n<dims A!0 \<and> evalt A n c1 \<and> evalt A n c2
        \<and> x+lookup_imp A [m,0] \<le> lookup_imp A [n,0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n,0]
          \<and> (\<forall>n'\<le>n. n'\<ge>m \<longrightarrow> x+lookup_imp A [m,0] > lookup_imp A [n',0]
            \<or> (x+lookup_imp A [m,0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n',0]
              \<and> evalt A n' c1)))"
        using dA_defn
        by blast
      {assume ass2:"\<exists>n\<ge>m. n<dA \<and> evalt A n c1 \<and> evalt A n c2
        \<and> x+lookup_imp A [m,0] \<le> lookup_imp A [n,0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n,0]
          \<and> (\<forall>n'\<le>n. n'\<ge>m \<longrightarrow> x+lookup_imp A [m,0] > lookup_imp A [n',0]
            \<or> (x+lookup_imp A [m,0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n',0]
              \<and> evalt A n' c1))"
        then obtain n where n_defn:"n\<ge>m \<and> n<dA \<and> evalt A n c1 \<and> evalt A n c2
        \<and> x+lookup_imp A [m,0] \<le> lookup_imp A [n,0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n,0]
          \<and> (\<forall>n'\<le>n. n'\<ge>m \<longrightarrow> x+lookup_imp A [m,0] > lookup_imp A [n',0]
            \<or> (x+lookup_imp A [m,0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n',0]
              \<and> evalt A n' c1))"
          by blast
        then have "n=m"
          using \<open>dA - 1 \<le> m\<close>
          by linarith
        then have "m<dA \<and> evalt A m c1 \<and> evalt A m c2
        \<and> x+lookup_imp A [m,0] \<le> lookup_imp A [m,0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [m,0]
          \<and> (\<forall>n'\<le>m. n'\<ge>m \<longrightarrow> x+lookup_imp A [m,0] > lookup_imp A [n',0]
            \<or> (x+lookup_imp A [m,0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [m,0] \<ge> lookup_imp A [n',0]
              \<and> evalt A n' c1))"
          using n_defn 
          by blast
        then have "m<dA \<and> x\<le>0 \<and> y\<ge> 0 \<and> evalt A m c1 \<and> evalt A m c2"
          by argo
        then have "evalt A m (ctUntil x y c1 c2)"
          using evalt.simps(4) dA_defn
          by force}
      then show ?thesis
        using oneway dA_defn
        by blast
    qed
    next
      case (Suc k)
      have "k = (dA - 1 - m) = (m = (dA - 1 - k))"
        by (metis Suc.hyps(2) Suc_leD diff_diff_cancel diff_le_self n_not_Suc_n)
      then have "evalt A (dA - 1 - k) (ctUntil x y c1 c2) = 
      (\<exists>n\<ge>(dA - 1 - k). n<dA \<and> evalt A n c1 \<and> evalt A n c2
        \<and> x+lookup_imp A [(dA - 1 - k),0] \<le> lookup_imp A [n,0] \<and> y+lookup_imp A [(dA - 1 - k),0] \<ge> lookup_imp A [n,0]
        \<and> (\<forall>n'\<le>n. n'\<ge>(dA - 1 - k) \<longrightarrow> x+lookup_imp A [(dA - 1 - k),0] > lookup_imp A [n',0]
          \<or> (x+lookup_imp A [(dA - 1 - k),0] \<le> lookup_imp A [n',0] \<and> y+lookup_imp A [(dA - 1 - k),0] \<ge> lookup_imp A [n',0]
            \<and> evalt A n' c1)))"
        using Suc
        sledgehammer




(*
definition time_tensor :: "real tensor \<Rightarrow> real tensor" where
"time_tensor A = select_dimension A 1 0"

lemma time_tensor_def2:
  fixes A :: "real tensor"
  assumes "length (dims A) = 2"  
  shows "time_tensor A = Abs_tensor ([(dims A)!0], 
      (IArray (tensor_vec_from_lookup ([(dims A)!0]) (select_dimension_lookup A 1 0))))"
proof -
have "time_tensor A = select_dimension A 1 0"
    using time_tensor_def
    by fast
  then have "time_tensor A = tensor_from_lookup (list_without (dims A) 1) (select_dimension_lookup A 1 0)"
    using select_dimension_def
    by auto
  then have "time_tensor A = tensor_from_vec (list_without (dims A) 1) 
      (IArray (tensor_vec_from_lookup (list_without (dims A) 1) (select_dimension_lookup A 1 0)))"
    using tensor_from_lookup_def
    by auto
  then have "time_tensor A = Abs_tensor ((list_without (dims A) 1), 
      (IArray (tensor_vec_from_lookup (list_without (dims A) 1) (select_dimension_lookup A 1 0))))"
    using tensor_from_vec_def
    by auto
  then have "time_tensor A = Abs_tensor (take 1 (dims A)@drop 2 (dims A), 
      (IArray (tensor_vec_from_lookup (take 1 (dims A)@drop 2 (dims A)) (select_dimension_lookup A 1 0))))"
    using list_without_def nat_1_add_1
    by presburger
  then have "time_tensor A = Abs_tensor (take 1 (dims A)@[], 
      (IArray (tensor_vec_from_lookup (take 1 (dims A)@[]) (select_dimension_lookup A 1 0))))"
    using assms
    by fastforce
  then show "time_tensor A = Abs_tensor ([(dims A)!0], 
      (IArray (tensor_vec_from_lookup ([(dims A)!0]) (select_dimension_lookup A 1 0))))"
    using assms
    by (simp add: take_Suc_conv_app_nth)
qed

lemma time_tensor_dims:
  fixes A :: "real tensor"
  assumes "length (dims A) = 2"  
  shows "dims (time_tensor A) = [dims A!0]"
  using assms time_tensor_def2 dims_tensor_from_lookup tensor_from_lookup_def tensor_from_vec_def
  by metis

lemma time_tensor_vec:
  fixes A :: "real tensor"
  assumes "length (dims A) = 2"  
  shows "Tensor.vec (time_tensor A) = (IArray (tensor_vec_from_lookup ([(dims A)!0]) (select_dimension_lookup A 1 0)))"
  using assms time_tensor_def2 vec_tensor_from_lookup tensor_from_lookup_def tensor_from_vec_def
  by metis

lemma time_tensor_lookup:
  fixes A :: "real tensor" and i :: nat
  assumes "length (dims A) = 2" "valid_index [i] [dims A!0]" "length (vec_list A) > 0"
  shows "lookup (time_tensor A) [i] = lookup A [i,0]"
proof -
  have 0:"\<And>A. length A = 2 \<Longrightarrow> A=A!0#[A!1]"
    by (metis (no_types, opaque_lifting) One_nat_def Suc_1 Suc_inject length_Cons list.size(3) nat.distinct(1) neq_Nil_conv nth_Cons_0 nth_Cons_Suc)
  have "lookup (time_tensor A) [i] = lookup_imp (time_tensor A) [i]"
    using assms lookup_equiv_lookup_imp time_tensor_dims
    by metis
  then have "lookup (time_tensor A) [i] = Tensor.vec (time_tensor A) !! flattened_index [dims A!0] [i]"
    using lookup_imp_def assms(1) time_tensor_dims
    by metis
  then have "lookup (time_tensor A) [i] 
    = (IArray (tensor_vec_from_lookup ([(dims A)!0]) (select_dimension_lookup A 1 0))) 
      !! flattened_index [dims A!0] [i]"
    using assms(1) time_tensor_vec
    by presburger
  then have "lookup (time_tensor A) [i] 
    = (tensor_vec_from_lookup ([(dims A)!0]) (select_dimension_lookup A 1 0))
      ! flattened_index [dims A!0] [i]"
    by simp
  then have "lookup (time_tensor A) [i]
    = (tensor_vec_from_lookup ([(dims A)!0]) (\<lambda>is. lookup_imp A (place_at 0 1 is)))
      ! flattened_index [dims A!0] [i]"
    by (simp add: select_dimension_lookup_def)
  then have "lookup (time_tensor A) [i]
    = concat (map (\<lambda>i. [lookup_imp A (place_at 0 1 [i])] ) [0..<dims A!0])
    ! flattened_index [dims A!0] [i]"
    by simp
  then have "lookup (time_tensor A) [i]
    = concat (map (\<lambda>i. [lookup_imp A ((take 1 [i]) @ (0 # (drop 1 [i])))] ) [0..<dims A!0])
    ! flattened_index [dims A!0] [i]"
    by (simp add: place_at_def)
  then have "lookup (time_tensor A) [i]
    = concat (map (\<lambda>i. [lookup_imp A [i, 0]]) [0..<dims A!0])
    ! flattened_index [dims A!0] [i]"
    by simp
  then have "lookup (time_tensor A) [i]
    = concat (map (\<lambda>i. [Tensor.vec A !! flattened_index (dims A) [i,0]]) [0..<dims A!0])
    ! flattened_index [dims A!0] [i]"
    by (simp add: lookup_imp_def)
  then have "lookup (time_tensor A) [i]
    = concat (map (\<lambda>i. [lookup_imp A [i,0]]) [0..<dims A!0])!flattened_index [dims A!0] [i]"
    by (simp add: lookup_imp_def)
  then have "lookup (time_tensor A) [i]
    = concat (map (\<lambda>i. [lookup_imp A [i,0]]) [0..<dims A!0])!i"
    by fastforce
  then have 1:"lookup (time_tensor A) [i]
    = lookup_imp A [i,0]"
    using assms(2)
    by auto
  have "dims A!1 > 0"
    using assms(1,3) nonempty_tensor_dims_not_0 one_less_numeral_iff semiring_norm(76) 
    by blast
  then have 2:"[0] \<lhd> [dims A!1]"
    using valid_index.simps
    by metis
  then have "dims A = dims A!0 # [dims A!1]"
    using assms(1) 0
    by auto
  then have "[i,0] = i # [0] \<and> dims A = dims A!0 # [dims A!1] \<and> [0] \<lhd> [dims A!1] \<and> i < dims A!0"
    using 2 assms(2) 
    by auto
  then have "valid_index [i,0] (dims A)"
    by (metis valid_index.Cons)
  then show ?thesis 
    using 1 lookup_equiv_lookup_imp
    by fastforce
qed

definition valid_signal_tensor :: "real tensor \<Rightarrow> bool" where
"valid_signal_tensor A = ((length (dims A) = 2) \<and> (sorted_wrt (<) (vec_list (time_tensor A))))"

fun find_1d_tensor :: "'a tensor \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  "find_1d_tensor A r 0 = 0"
| "find_1d_tensor A r (Suc n) = (if (Suc n) > dims A!0 \<or> length (dims A) > 1 then 0 else
    (if lookup_imp A [n] = r then Suc n else find_1d_tensor A r n))"

lemma find_1d_tensor_pos_imp_exists:
  assumes "find_1d_tensor A r (dims A!0) > 0"
  shows "\<exists>n. n < dims A!0 \<and> lookup_imp A [n] = r"
proof (rule ccontr)
  assume "\<not>(\<exists>n. n < dims A!0 \<and> lookup_imp A [n] = r)"
  then have "\<forall>n\<ge>0. n\<ge>dims A!0 \<or> lookup_imp A [n] \<noteq> r"
    using leI 
    by auto
  then have "\<And>n. n\<ge>0 \<longrightarrow> (n\<ge>dims A!0 \<or> lookup_imp A [n] \<noteq> r)"
    by blast
  then have "find_1d_tensor A r (dims A!0) = 0"
  proof -
    have "\<And>m. m>0 \<and> m<dims A!0 \<longrightarrow> find_1d_tensor A r m = find_1d_tensor A r (m-1)"
      by (smt (verit, best) Suc_eq_plus1_left Suc_le_D Zero_not_Suc assms
          \<open>\<not> (\<exists>n. n < dims A ! 0 \<and> lookup_imp A [n] = r)\<close> add_Suc_right add_eq_self_zero 
          diff_Suc_1 diff_Suc_Suc diff_add_0 diff_is_0_eq diff_is_0_eq' diff_le_self 
          dual_order.order_iff_strict find_1d_tensor.simps(2) less_eq_Suc_le less_eq_nat.simps(1) 
          less_natE list_decode.cases minus_nat.diff_0 not_less_eq_eq old.nat.exhaust zero_neq_one)
    {fix m :: nat
      assume "m>0 \<and> m<dims A!0"
      have "find_1d_tensor A r m = find_1d_tensor A r 0"
      proof (induction m)
        case 0
        then show ?case 
          by simp
      next
        case (Suc m)
        then show ?case 
          using \<open>\<not>(\<exists>n<dims A!0. lookup_imp A [n] = r)\<close> 
          by force
      qed}
    then show ?thesis
      using \<open>\<not>(\<exists>n<dims A!0. lookup_imp A [n] = r)\<close> find_1d_tensor.elims less_Suc_eq_0_disj 
        not_less_eq
      by (smt (verit, ccfv_SIG) )
  qed
  then show False
    using assms
    by simp
qed

lemma find_1d_tensor_works:
  assumes "find_1d_tensor A r (dims A!0) > 0" "length (dims A) = 1"
  shows "lookup_imp A [(find_1d_tensor A r (dims A!0)) - 1] = r"
proof -
  obtain N where "N\<noteq>{} \<and> N = {n. n<dims A!0 \<and> lookup_imp A [n] = r}"
    using assms find_1d_tensor_pos_imp_exists empty_Collect_eq not_Cons_self2
    by (smt (verit, del_insts))
  then have N_defn:"finite N \<and> N\<noteq>{} \<and> N = {n. n<dims A!0 \<and> lookup_imp A [n] = r}"
    by auto
  then obtain nmax where nmax_defn:"nmax = Max N \<and> nmax \<in> N \<and> nmax < dims A!0"
    using Max_in 
    by auto
  then have "\<forall>n\<in>N. n\<le>nmax"
    using eq_Max_iff N_defn
    by blast
  then have "\<forall>n>nmax. n\<notin>N"
    by auto
  then have "\<forall>n>nmax. n<dims A!0 \<longrightarrow> lookup_imp A [n] \<noteq> r"
    using N_defn 
    by blast
  then have "\<forall>n>nmax. n\<ge>dims A!0 \<or> lookup_imp A [n] \<noteq> r"
    by auto
  then have "\<forall>n>nmax. n\<ge>dims A!0 \<or> find_1d_tensor A r (Suc n) = find_1d_tensor A r n"
    using assms(2) 
    by auto
  then have "\<forall>n. Suc (n+nmax)\<ge>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc (n+nmax))"
    using less_add_Suc2 
    by blast
  {fix n :: nat
    have "Suc (n+nmax)\<ge>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc nmax)"
    proof (induction n)
      case 0
      then show ?case
        using \<open>\<forall>n. Suc (n+nmax)\<ge>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc (n+nmax))\<close>
        by fastforce
    next
      case (Suc k)
      then show ?case
        using \<open>\<forall>n. Suc (n+nmax)\<ge>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc (n+nmax))\<close>
        by fastforce
    qed}
  then have "\<forall>n. Suc (n+nmax)\<ge>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc nmax)"
    by simp
  then have "\<forall>n. Suc (Suc (n+nmax))>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc nmax)"
    by force
  then have "(\<exists>n. Suc (Suc (n+nmax)) = dims A!0) \<or> Suc nmax = dims A!0"
    using nmax_defn N_defn add.commute add.right_neutral add_Suc_right less_imp_Suc_add 
      list_decode.cases less_natE not0_implies_Suc
    by metis
  then have "find_1d_tensor A r (dims A!0) = find_1d_tensor A r (Suc nmax)"
    using \<open>\<forall>n. Suc (Suc (n+nmax))>dims A!0 \<or> find_1d_tensor A r (Suc (Suc (n+nmax))) = find_1d_tensor A r (Suc nmax)\<close>
    by (metis dual_order.strict_iff_not)
  then have "find_1d_tensor A r (dims A!0) = Suc nmax"
    using assms(2) nmax_defn N_defn
    by auto
  then show ?thesis
    using nmax_defn N_defn
    by auto
qed

definition find_time_tensor :: "real tensor \<Rightarrow> real \<Rightarrow> nat" where
"find_time_tensor A r = find_1d_tensor (time_tensor A) r (dims (time_tensor A)!0)"

lemma find_time_tensor_works:
  assumes "find_time_tensor A r > 0" "length (dims A) = 2"
  shows "lookup_imp (time_tensor A) [(find_time_tensor A r) - 1] = r"
  using find_time_tensor_def find_1d_tensor_works assms 
  by (metis One_nat_def length_Cons list.size(3) time_tensor_dims)

fun Teval :: "cterm \<Rightarrow> real tensor \<Rightarrow> real" where
"Teval (Get n) A = lookup_imp A [(nat n)]"
| "Teval (Const r) A = r"
| "Teval (Add c1 c2) A = Teval c1 A + Teval c2 A"
| "Teval (Mult c1 c2) A = Teval c1 A * Teval c2 A"
| "Teval (Uminus c) A = -1 * (Teval c A)"
| "Teval (Divide c1 c2) A = Teval c1 A / Teval c2 A"

fun evalst :: "real \<Rightarrow> real tensor \<Rightarrow> (real tensor) constraint \<Rightarrow> bool" where
"evalst p A (cMu f ct r) = (if (find_time_tensor A p > 0) 
  then (f ct (select_dimension A 0 (find_time_tensor A p - 1)) > r) else False)"
| "evalst p A (cNot c) = (\<not>(evalst p A c))"
| "evalst p A (cAnd c1 c2) = ((evalst p A c1) \<and> (evalst p A c2))"
| "evalst p A (cUntil x y c1 c2) = False"
*)

(*
fun flattened_index:: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
 flattened_index_Nil_1: "flattened_index [] is = 0"
| flattened_index_Nil_2: "flattened_index ds [] = 0"
| flattened_index_Cons: "flattened_index (d#ds) (i#is) = (i * prod_list ds) + (flattened_index ds is)"

definition valid_signal_tensor :: "real tensor \<Rightarrow> bool" where
"valid_signal_tensor s = sorted_wrt (<) (s)"
*)

end