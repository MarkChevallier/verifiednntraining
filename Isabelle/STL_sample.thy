theory STL_sample
  imports STL Code_Real_Approx_By_Float_2

begin

fun valid_constraints :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"valid_constraints p t (cMu f r) = (p\<in>set (map fst t))"
| "valid_constraints p t (cNot c) = (valid_constraints p t c)"
| "valid_constraints p t (cAnd c1 c2) = (valid_constraints p t c1 \<and> valid_constraints p t c2)"
| "valid_constraints p t (cUntil x y c1 c2) = (x \<ge> 0 \<and> y \<ge> 0)"

definition valid_signal :: "(real \<times> 'v::real_vector) list \<Rightarrow> bool" where
"valid_signal xs = distinct (map fst xs)"

(*
definition first_time :: "(real \<times> 'v::real_vector) list \<Rightarrow> real" where
"first_time xs = Min (set (map fst xs))"

definition at_time :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> real" where
"at_time p xs = Min (set (filter (\<lambda>x. x\<ge>p) (map fst xs)))"

definition next_time :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> real" where
"next_time p xs = Min (set (filter (\<lambda>x. x>p) (map fst xs)))"
*)

definition find_time :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> 'v" where
"find_time xs r = (snd (the (find (\<lambda>x. fst x = r) xs)))"

(*
lemma signal_induct: 
  "P (first_time xs) \<Longrightarrow> (\<And>p. P p \<Longrightarrow> P (next_time p xs)) \<Longrightarrow> (\<And>p. p\<in>set(map fst xs) \<Longrightarrow> P p)"
proof (induct xs rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "fst x = first_time (x#xs)")
    case True
    then have "P (first_time (x#xs))"
      using Cons 
      by blast
    then have "\<And>p. p\<in>set(map fst xs) \<Longrightarrow> P p"
      using Cons 
*)    

fun evals :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"evals p t (cMu f r) = (if (p\<in>set (map fst t)) then (f (find_time t p) > r) else False)"
| "evals p t (cNot c) = (\<not>(evals p t c))"
| "evals p t (cAnd c1 c2) = ((evals p t c1) \<and> (evals p t c2))"
| "evals p t (cUntil x y c1 c2) = ((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1)))"

lemma cTrue_valid_constraints:
  "valid_constraints p t cTrue = (p\<in>set (map fst t))"
  using cTrue_def valid_constraints.simps(1)
  by metis

lemma cTrue_evals:"evals p t cTrue = (p\<in>set (map fst t))"
  using cTrue_def evals.simps(1) zero_less_one
  by metis

lemma cOr_valid_constraints:
  "valid_constraints p t (cOr c1 c2) = (valid_constraints p t c1 \<and> valid_constraints p t c2)"
  using cOr_def valid_constraints.simps(2,3)
  by metis

lemma cOr_evals:"evals p t (cOr c1 c2) = (evals p t c1 \<or> evals p t c2)"
  using cOr_def evals.simps(2,3)
  by metis

lemma cEventually_valid_constraints:
  "valid_constraints p t (cEventually x y c) = (x\<ge>0 \<and> y\<ge>0)"
  using cEventually_def valid_constraints.simps(4)
  by metis

lemma cEventually_evals: "evals p t (cEventually x y c) = (\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c)"
  using evals.simps(4) cTrue_evals cEventually_def length_map nth_map nth_mem
  by (smt (verit))

lemma cAlways_valid_constraints: "valid_constraints p t (cAlways x y c) = (x\<ge>0 \<and> y\<ge>0)"
  using cAlways_def valid_constraints.simps(2) cEventually_valid_constraints
  by metis

lemma cAlways_evals: "evals p t (cAlways x y c) = 
  (\<forall>p'. p'\<ge>p+x\<and>p'\<le>p+y\<and> (\<exists>n<length t. fst (t!n) = p') \<longrightarrow> evals p' t c)"
proof -
  have "evals p t (cAlways x y c) = evals p t (cNot (cEventually x y (cNot c)))"
    using cAlways_def
    by metis
  then have "evals p t (cAlways x y c) = (\<not>(\<exists>p'\<ge>p + x. p' \<le> p + y \<and> (\<exists>n<length t. fst (t ! n) = p') \<and> evals p' t (cNot c)))"
    using cEventually_evals evals.simps(2)
    by metis
  then have "evals p t (cAlways x y c) = (\<forall>p'\<ge>p + x. \<not>(p' \<le> p + y \<and> (\<exists>n<length t. fst (t ! n) = p') \<and> evals p' t (cNot c)))"
    by blast
  then have "evals p t (cAlways x y c) = (\<forall>p'\<ge>p + x. \<not>(p' \<le> p + y \<and> (\<exists>n<length t. fst (t ! n) = p') \<and> \<not>(evals p' t c)))"
    using evals.simps(2) 
    by simp
  then show ?thesis
    by blast
qed

(* definition clip_timeline :: "real \<Rightarrow> real \<Rightarrow> (real\<times>'v::real_vector) list \<Rightarrow> (real\<times>'v::real_vector) list" where
"clip_timeline x y t = sort_key (\<lambda>z. fst z) (filter (\<lambda>z. fst z \<ge> x \<and> fst z \<le> y) t)"

lemma tst:"length t > 0 \<longrightarrow> (sort_key id t)!0 = Min (set t)"
proof -
  {assume "length t > 0"
    then have fin:"finite (set t) \<and> set t \<noteq> {}"
      by blast
    have "sorted (sort_key id t)"
      by (metis list.map_id sorted_sort_key)
    have "(sort_key id t)!0 = Min (set t)"
    proof (rule ccontr)
      assume "(sort_key id t)!0 \<noteq> Min (set t)"
      then have "\<exists>n\<in>(set t). n < (sort_key id t)!0"
        using fin Min_in Min_le \<open>0 < length t\<close> finite_has_minimal length_sort linorder_not_le 
          nth_mem set_sort
        by metis
      then show False
        using \<open>sorted (sort_key id t)\<close> in_set_conv_nth linorder_not_le not_less_zero set_sort 
          sorted_nth_mono 
        by metis
    qed}
  then show ?thesis
    by simp
qed
        

lemma clip_timeline_0:
  assumes "\<exists>n<length t. fst (t!n) \<ge> x \<and> fst (t!n) \<le> y"
  shows "fst ((clip_timeline x y t)!0) = Min (set (filter (\<lambda>z. z\<ge>x \<and> z\<le>y) (map fst t)))"
proof -
  have "set (filter (\<lambda>z. z\<ge>x \<and> z\<le>y) (map fst t)) = {r. r \<in> set (map fst t) \<and> r\<ge>x \<and> r\<le>y}"
    by force
  then have "finite (set (filter (\<lambda>z. z\<ge>x \<and> z\<le>y) (map fst t))) 
      \<and> (set (filter (\<lambda>z. z\<ge>x \<and> z\<le>y) (map fst t))) \<noteq> {}"
    using assms 
    by fastforce
  then have "Min (set (filter (\<lambda>z. z\<ge>x \<and> z\<le>y) (map fst t))) \<in> set (filter (\<lambda>z. z\<ge>x \<and> z\<le>y) (map fst t))"
    using Min_in
    by blast
  then have "\<forall>n<length (clip_timeline x y t). fst ((clip_timeline x y t)!0) \<le> fst ((clip_timeline x y t)!n)"
    using clip_timeline_def sort_key_def
    oops
*)

lemma cUntil_recurs:
  fixes p x y :: real and t :: "(real\<times>'v::real_vector) list" and c1 c2 :: "'v constraint"
  assumes "valid_signal t" "x\<ge>0" "y\<ge>0"
  shows "evals p t (cUntil x y c1 c2) = (if x<0 \<or> y<0 \<or> card {z \<in> fst ` set t. p+x \<le> z} = 0 then False
      else (if card {z \<in> fst ` set t. p+x \<le> z} = 1 then 
        evals p t c2
      else ((evals (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c2) \<or>
          ((evals (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c1) \<and>
            (evals (Min (((set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) - {Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))})) t 
              (cUntil 0 (y-p-x) c1 c2))))))"
proof -
  {assume onew:"evals p t (cUntil x y c1 c2)"
    have "(if x<0 \<or> y<0 \<or> card {z \<in> fst ` set t. p+x \<le> z} = 0 then False
      else (if card {z \<in> fst ` set t. p+x \<le> z} = 1 then 
        evals p t c2
      else ((evals (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c2) \<or>
          ((evals (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c1) \<and>
            (evals (Min (((set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) - {Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))})) t 
              (cUntil 0 (y-p-x) c1 c2))))))"
    proof (insert onew, induct t)
      case Nil
      then show ?case 
        by force
    next
      case (Cons z zs)
      then obtain p' where "(p'\<ge>p+x \<and> p'\<le>p+y \<and> (\<exists>n<length (z#zs). fst ((z#zs)!n) = p') \<and> evals p' (z#zs) c2 
        \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length (z#zs). fst ((z#zs)!n) = p'') \<longrightarrow> evals p'' (z#zs) c1))"
        using eval.simps(4) 
        by fastforce
      then show ?case
      proof (cases "fst z < p \<or> fst z > p'")
        case True
        have "evals p zs (cUntil x y c1 c2)"
        proof -
        show ?thesis
          oops

function robust :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> real \<Rightarrow> real" where
"robust p t (cMu f r) \<gamma> = (if (\<exists>n<length t. fst (t!n) = p) then f (find_time t p) - r else -1)"
| "robust p t (cNot c) \<gamma> = - (robust p t c \<gamma>)"
| "robust p t (cAnd c1 c2) \<gamma> = Min_gamma_comp \<gamma> (robust p t c1 \<gamma>) (robust p t c2 \<gamma>)"
| "robust p t (cUntil x y c1 c2) \<gamma> = (if x<0 \<or> y<0 \<or> card {z \<in> fst ` set t. p+x \<le> z} = 0 then -1 
      else (if card {z \<in> fst ` set t. p+x \<le> z} = 1 then 
        (robust (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c2 \<gamma>)
      else (Max_gamma_comp \<gamma>
          (robust (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c2 \<gamma>)
          (Min_gamma_comp \<gamma> 
            (robust (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c1 \<gamma>)
            (robust (Min (((set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) - {Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))})) t 
              (cUntil 0 (y-p-x) c1 c2) \<gamma>)))))"
  by pat_completeness auto
termination 
  apply (relation 
      "Wellfounded.measure (\<lambda>(p,t,c,\<gamma>). card (set (filter (\<lambda>z. z \<ge> p) (map fst t))) + size c)")
         apply simp+
proof -
  have filter_real_list_card:"\<And>x y::real. \<And>A::real list. x < y \<Longrightarrow>
   x \<in> set A \<Longrightarrow> card (set (filter ((\<le>) y) A)) < card (set (filter ((\<le>) x) A))"
  proof -
    have "\<And>x y::real. \<And>A::real list. x < y \<Longrightarrow>
   x \<in> set A \<Longrightarrow> x\<notin>(set (filter ((\<le>) y) A)) \<and> x\<in>(set (filter ((\<le>) x) A))"
      by simp
    then have "\<And>x y::real. \<And>A::real list. x < y \<Longrightarrow>
   x \<in> set A \<Longrightarrow> (set (filter ((\<le>) y) A))\<subset>(set (filter ((\<le>) x) A))"
      using dual_order.strict_iff_order filter_set member_filter subset_code(1)
      by (smt (verit, del_insts))
    then show "\<And>x y::real. \<And>A::real list. x < y \<Longrightarrow>
   x \<in> set A \<Longrightarrow> card (set (filter ((\<le>) y) A)) < card (set (filter ((\<le>) x) A))"
      using List.finite_set psubset_card_mono
      by meson
  qed
  {fix p x y \<gamma> :: real and t :: "(real \<times> ('v::real_vector)) list" and c1 c2 :: "('v::real_vector) constraint"
    have fin:"finite {z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z}
      \<and> finite {z\<in>fst ` set t. p \<le> z}"
      by simp
    assume assms1:"\<not> x<0 \<and> \<not> y<0 \<and> card {z \<in> fst ` set t. p + x \<le> z} = Suc 0"
    then have "\<exists>xa\<in>fst ` set t.  p+x\<le>xa"
      using Collect_empty_eq List.finite_set One_nat_def card_0_eq less_irrefl list.set(1) 
        zero_less_one 
      by (metis (no_types, lifting))
    then have "Min {xa\<in>fst ` set t. p+x \<le> xa} \<ge> p" 
      using assms1 
      by auto
    then have "\<forall>z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z \<longrightarrow>
      p \<le> z"
      by auto
    then have "\<And>za. za\<in>{z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z} \<longrightarrow> 
        za\<in>{z\<in>fst ` set t. p \<le> z}"
      by blast
    then have "card {z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z} \<le>
      card {z\<in>fst ` set t. p \<le> z}"
      using fin card_mono subsetI
      by meson
    then have "card {xa \<in> fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> xa}
       < Suc (card {x \<in> fst ` set t. p \<le> x} + size c1)"
      by linarith}
  then show "\<And>p x y::real. \<And>t::(real\<times>'v::real_vector) list. \<And>c1::'v constraint.
       \<not> x < 0 \<and> \<not> y < 0 \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} = Suc 0 \<Longrightarrow>
       card {xa \<in> fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> xa}
       < Suc (card {x \<in> fst ` set t. p \<le> x} + size c1)"
    by blast
  then show "\<And>p x y \<gamma>::real. \<And>t::(real\<times>('v::real_vector)) list. \<And>c1 c2::('v::real_vector) constraint.
      \<not> (x < 0 \<or> y < 0 \<or> card {z \<in> fst ` set t. p + x \<le> z} = 0) \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} \<noteq> 1 \<Longrightarrow>
      ((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c2, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      "\<And>p x y \<gamma>::real. \<And>t::(real\<times>('v::real_vector)) list. \<And>c1 c2::('v::real_vector) constraint.
      \<not> (x < 0 \<or> y < 0 \<or> card {z \<in> fst ` set t. p + x \<le> z} = 0) \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} \<noteq> 1 \<Longrightarrow>((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c1, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      "\<And>p x y \<gamma>::real. \<And>t::(real\<times>('v::real_vector)) list. \<And>c1 c2::('v::real_vector) constraint.
      \<not> (x < 0 \<or> y < 0 \<or> card {z \<in> fst ` set t. p + x \<le> z} = 0) \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} \<noteq> 1 \<Longrightarrow>((Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}),
         t, cUntil 0 (y - p - x) c1 c2, \<gamma>),
        p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
  proof -
  {fix p x y \<gamma> :: real and t :: "(real \<times> ('v::real_vector)) list" and c1 c2 :: "('v::real_vector) constraint"
    have fin:"finite {z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z}
      \<and> finite {z\<in>fst ` set t. p \<le> z}"
      by simp
    assume assms2:"\<not>(x<0 \<or> y<0 \<or> card {z\<in>fst ` set t. p+x\<le>z} = 0)"
      and assms3:"card {z\<in>fst ` set t. p+x\<le>z} \<noteq> 1"
    then have "Min {xa\<in>fst ` set t. p+x \<le> xa} \<ge> p" 
      using assms2 
      by auto
    then have "\<forall>z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z \<longrightarrow>
      p \<le> z"
      by auto
    then have "\<And>za. za\<in>{z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z} \<longrightarrow> 
        za\<in>{z\<in>fst ` set t. p \<le> z}"
      by blast
    then have "card {z\<in>fst ` set t. Min {xa \<in> fst ` set t. p + x \<le> xa} \<le> z} \<le>
      card {z\<in>fst ` set t. p \<le> z}"
      using fin card_mono subsetI
      by meson
    then have "card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t))))) (map fst t)))
      \<le> card (set (filter ((\<le>) p) (map fst t)))"
      by auto
    then have "card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t))))) (map fst t))) + size c2
      < card (set (filter ((\<le>) p) (map fst t))) + size (cUntil x y c1 c2)"
      by force
    then have 1:"((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c2, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      by force
    then have "card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t))))) (map fst t))) + size c1
      < card (set (filter ((\<le>) p) (map fst t))) + size (cUntil x y c1 c2)"
      using \<open>card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t))))) (map fst t)))
      \<le> card (set (filter ((\<le>) p) (map fst t)))\<close>
      by auto
    then have 2:"((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c1, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      by auto
    have fin2:"finite (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))})"
      by blast
    have "card (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}) =
          card (set (filter ((\<le>) (p + x)) (map fst t))) - 1"
      using List.finite_set Min_in card.empty card_Diff_singleton_if diff_is_0_eq 
        linorder_linear not_one_le_zero
      by (metis (no_types, lifting))
    then have "card (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}) > 0"
      using assms2 assms3 
      by fastforce
    then have "set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))} \<noteq> {}"
      using card_gt_0_iff 
      by blast
    then have "Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}) >
               Min (set (filter ((\<le>) (p + x)) (map fst t)))"
      using fin2 Diff_subset Min_antimono infinite_remove Min_in dual_order.refl 
        linorder_not_less order_antisym subset_Diff_insert
      by metis
    then have "Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}) 
              \<in> set (map fst t)
              \<and> Min (set (filter ((\<le>) (p + x)) (map fst t))) \<in> set (map fst t)"
      using Diff_iff Min_in 
        \<open>set (filter ((\<le>) (p + x)) (map fst t)) - {Min (set (filter ((\<le>) (p + x)) (map fst t)))} \<noteq> {}\<close> 
        fin2 mem_Collect_eq set_filter Diff_subset List.finite_set subset_empty
      by (metis (mono_tags, lifting))
    then have "card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}))) (map fst t)))
            < card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t))))) (map fst t)))"
      using \<open>Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}) >
               Min (set (filter ((\<le>) (p + x)) (map fst t)))\<close> filter_real_list_card
      by blast
    then have "card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}))) (map fst t)))
            < card (set (filter ((\<le>) p) (map fst t)))"
      using \<open>card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t))))) (map fst t))) 
        \<le> card (set (filter ((\<le>) p) (map fst t)))\<close> order_less_le_trans 
      by blast
    then have "card (set (filter ((\<le>) (Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}))) (map fst t))) + size (cUntil 0 (y - p - x) c1 c2)
            < card (set (filter ((\<le>) p) (map fst t))) + size (cUntil x y c1 c2)"
      by auto
    then have "((Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}),
         t, cUntil 0 (y - p - x) c1 c2, \<gamma>),
        p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      by force
    then have "((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c2, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      "((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c1, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      "((Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}),
         t, cUntil 0 (y - p - x) c1 c2, \<gamma>),
        p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      using 1 2
      by blast+}
    then show "\<And>p x y \<gamma>::real. \<And>t::(real\<times>('v::real_vector)) list. \<And>c1 c2::('v::real_vector) constraint.
      \<not> (x < 0 \<or> y < 0 \<or> card {z \<in> fst ` set t. p + x \<le> z} = 0) \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} \<noteq> 1 \<Longrightarrow>
      ((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c2, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      "\<And>p x y \<gamma>::real. \<And>t::(real\<times>('v::real_vector)) list. \<And>c1 c2::('v::real_vector) constraint.
      \<not> (x < 0 \<or> y < 0 \<or> card {z \<in> fst ` set t. p + x \<le> z} = 0) \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} \<noteq> 1 \<Longrightarrow>((Min (set (filter ((\<le>) (p + x)) (map fst t))), t, c1, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      "\<And>p x y \<gamma>::real. \<And>t::(real\<times>('v::real_vector)) list. \<And>c1 c2::('v::real_vector) constraint.
      \<not> (x < 0 \<or> y < 0 \<or> card {z \<in> fst ` set t. p + x \<le> z} = 0) \<Longrightarrow>
       card {z \<in> fst ` set t. p + x \<le> z} \<noteq> 1 \<Longrightarrow>((Min (set (filter ((\<le>) (p + x)) (map fst t)) -
              {Min (set (filter ((\<le>) (p + x)) (map fst t)))}),
         t, cUntil 0 (y - p - x) c1 c2, \<gamma>),
        p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(p, t, c, \<gamma>). card (set (filter ((\<le>) p) (map fst t))) + size c)"
      by presburger+
  qed
qed    

export_code robust
 in OCaml
  module_name STLLoss

end
