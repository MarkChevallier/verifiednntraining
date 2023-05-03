theory STL_sample
  imports STL "List-Index.List_Index"

begin

definition valid_signal :: "(real \<times> 'v::real_vector) list \<Rightarrow> bool" where
"valid_signal xs = (distinct (map fst xs) \<and> (\<forall>n<length xs. fst (xs!n) \<ge> 0)
  \<and> fst (xs!0) = 0 \<and> sorted (map fst xs))"

definition find_time :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> 'v" where
"find_time xs r = (if (find (\<lambda>x. fst x = r) xs = None) then 0 else (snd (the (find (\<lambda>x. fst x = r) xs))))"

definition signal_shift :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> (real \<times> 'v::real_vector) list" where
"signal_shift xs r = map (\<lambda>x. (fst x - r, snd x)) (drop (index (map fst xs) r) xs)"

value "find_time [(0,a),(1,b),(1.5,c)] 1.5"
value "signal_shift [(0,a),(1,b),(1.5,c)] 1.0"
value "signal_shift [(0,a),(0.5,b),(1.5,c),(21,d)] ((map fst [(0,a),(0.5,b),(1.5,c)])!1)"

lemma drop_index_r:
  fixes xs :: "(real \<times> 'v::real_vector) list" and r :: real
  assumes "valid_signal xs" "\<exists>n<length xs. fst (xs!n) = r"
  shows "\<forall>n<length (drop (index (map fst xs) r) xs). fst ((drop (index (map fst xs) r) xs)!n) \<ge> r"
proof -
  have "sorted (map fst xs)"
    using valid_signal_def assms(1)
    by blast
  then have "\<forall>n\<ge>(index (map fst xs) r). n<length (map fst xs) \<longrightarrow> (map fst xs)!n \<ge> r"
    using dual_order.strict_trans2 index_less_size_conv nth_index sorted_nth_mono
    by metis
  then have "\<forall>n<length (drop (index (map fst xs) r) xs). (map fst (drop (index (map fst xs) r) xs))!n \<ge> r"
    by auto
  then show "\<forall>n<length (drop (index (map fst xs) r) xs). fst ((drop (index (map fst xs) r) xs)!n) \<ge> r"
    by auto
qed

lemma signal_shift_exists:
  fixes t :: "(real \<times> 'v::real_vector) list" and r :: real
  assumes "\<exists>n<length t. fst (t!n) = r"
  shows "length (signal_shift t r) > 0"
  unfolding signal_shift_def
  using assms
  by auto

lemma signal_shift_valid:
  fixes xs :: "(real \<times> 'v::real_vector) list" and r :: real
  assumes "valid_signal xs" "\<exists>n<length xs. fst (xs!n) = r"
  shows "valid_signal (signal_shift xs r)"
proof -
  have 0:"map fst ((map (\<lambda>x. (fst x - r, snd x)) xs)) = map (\<lambda>x. fst x - r) xs"
    by simp
  then have "distinct (map (\<lambda>x. fst x - r) xs)"
    using assms(1) distinct_conv_nth length_map nth_map valid_signal_def
    by (smt (verit, ccfv_threshold))
  then have "distinct (map fst (signal_shift xs r))" 
    using signal_shift_def 0 distinct_drop distinct_map distinct_conv_nth 
      drop_map length_map nth_map
    by (smt (verit, best))
  have "\<forall>n<length xs. (\<lambda>x. fst x \<ge> 0) (xs!n)"
    using valid_signal_def assms(1)
    by auto
  then have "\<forall>n<length (signal_shift xs r). fst ((signal_shift xs r)!n) \<ge> 0"
    using signal_shift_def in_set_conv_nth in_set_dropD drop_index_r
      assms(1) assms(2) length_map nth_map prod.sel(1)
    by (smt (verit, ccfv_threshold))
  have "fst ((signal_shift xs r)!0) = 0" 
    using 0 add.right_neutral assms(1) assms(2) drop_map index_nth_id length_map 
      nat_less_le nth_drop nth_map signal_shift_def valid_signal_def
    by (smt (verit, ccfv_threshold))
  then have "sorted (drop (index (map fst xs) r) (map fst xs))"
    using assms sorted_drop valid_signal_def 
    by blast
  then have 1:"sorted (map fst (drop (index (map fst xs) r) xs))"
    using drop_map
    by metis
  then have "sorted (map (\<lambda>x. fst x - r) (drop (index (map fst xs) r) xs))"
  proof -
    have "\<forall>i j. i\<le>j \<longrightarrow> j < length (drop (index (map fst xs) r) xs) 
        \<longrightarrow> fst ((drop (index (map fst xs) r) xs)!i) 
          \<le> fst ((drop (index (map fst xs) r) xs)!j)"
      using 1 sorted_iff_nth_mono 
      by force
    then have "\<forall>i j. i\<le>j \<longrightarrow> j < length (drop (index (map fst xs) r) xs) 
        \<longrightarrow> fst ((drop (index (map fst xs) r) xs)!i) - r 
          \<le> fst ((drop (index (map fst xs) r) xs)!j) - r"
      by force
    then show ?thesis
      using dual_order.strict_trans2 length_map nth_map order_less_imp_le 
        sorted_iff_nth_mono_less
      by (smt (verit, del_insts))
  qed
  then have "sorted (map fst (signal_shift xs r))"
    using signal_shift_def 0 drop_map map_eq_conv
    by (smt (verit, best))
  then show ?thesis
    using valid_signal_def \<open>distinct (map fst (signal_shift xs r))\<close> 
      \<open>\<forall>n<length (signal_shift xs r). fst ((signal_shift xs r)!n) \<ge> 0\<close>
      \<open>fst (signal_shift xs r ! 0) = 0\<close> 
    by blast
qed

fun evals :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"evals p t (cMu f r) = (if (\<exists>n<length t. fst (t!n) = p) then (f (find_time t p) > r) else False)"
| "evals p t (cNot c) = (\<not>(evals p t c))"
| "evals p t (cAnd c1 c2) = ((evals p t c1) \<and> (evals p t c2))"
| "evals p t (cUntil x y c1 c2) = (\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1))"

lemma cTrue_evals:"evals p t cTrue = (if (\<exists>n<length t. fst (t!n) = p) then True else False)"
  using cTrue_def evals.simps(1) zero_less_one
  by metis

lemma cOr_evals:"evals p t (cOr c1 c2) = (evals p t c1 \<or> evals p t c2)"
  using cOr_def evals.simps(2,3)
  by metis

lemma cEventually_evals: "evals p t (cEventually x y c) =
    (\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c)"
  using evals.simps(4) cTrue_evals cEventually_def
  by (smt (verit))

lemma cAlways_evals: "evals p t (cAlways x y c) =
  (\<forall>p'. p'\<ge>p+x\<and>p'\<le>p+y\<and> (\<exists>n<length t. fst (t!n) = p') \<longrightarrow> evals p' t c)"
proof -
  have "evals p t (cAlways x y c) = (\<not>(\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t (cNot c)))"
    using cEventually_evals cAlways_def evals.simps(2)
    by metis
  then show ?thesis
    using evals.simps(2)
    by blast
qed

(* 
definition clip_timeline :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> (real \<times> 'v) list" where
"clip_timeline x t = signal_shift t (fst (t!(find_index (\<lambda>r. r\<ge>x) (map fst t))))"

lemma clip_timeline_length:"length (clip_timeline x xs) \<le> length xs"
  using clip_timeline_def length_rev length_take linorder_not_le min_less_iff_conj 
    order_less_imp_le rev_drop signal_shift_def length_map
  by (metis (no_types, lifting))

lemma clip_timeline_exists:
  fixes x y :: real and t :: "(real \<times> 'v::real_vector) list"
  assumes "y\<ge>x" "\<exists>n<length t. fst (t!n) = y"
  shows "length (clip_timeline x t) > 0"
proof -
  have "\<exists>n<length t. fst (t!n) = y"
    using assms(1,2)
    by blast
  then have "\<exists>m<length t. find_index (\<lambda>r. r=y) (map fst t) = m"
    using find_index_le_size index_def index_first length_map nat_neq_iff nth_map 
      verit_comp_simplify1(3)
    by metis
  then obtain m::nat where m_defn:"m<length t \<and> find_index (\<lambda>r. r\<ge>x) (map fst t) = m"
    using assms(1) find_index_eq_iff length_map
    by (metis (mono_tags, lifting))
  then have "clip_timeline x t = signal_shift t (fst (t!m))"
    using clip_timeline_def
    by blast
  then show ?thesis
    using signal_shift_exists m_defn
    by auto
qed

lemma Until_drop_length:
  assumes "length t > 0"
  shows "length (drop 1 (map (\<lambda>x. (fst x - fst (t!1), snd x)) t)) < length t"
  using assms
  by simp


lemma cUntil_evals_alt:
  fixes t :: "(real \<times> 'v::real_vector) list" and c1 c2 :: "'v constraint" and x y :: "real"
  assumes "valid_signal t"
  shows "evals t (cUntil x y c1 c2) = (length (clip_timeline x t) > 0 \<and> y\<ge>x 
    \<and> (evals (clip_timeline x t) c2)
      \<or> ((evals (clip_timeline x t) c1) 
        \<and> (evals (drop 1 (map (\<lambda>z. (fst z - fst ((clip_timeline x t)!1), snd z)) (clip_timeline x t))) (cUntil 0 (y-x-fst ((clip_timeline x t)!1)) c1 c2))))"
proof -
  {assume "evals t (cUntil x y c1 c2)"
    then obtain t' where t'_defn:"t'\<ge>x \<and> t'\<le>y \<and> (\<exists>n<length t. fst (t!n) = t') 
        \<and> evals (signal_shift t t') c2 \<and> (\<forall>t''. t''\<ge>0\<and>t''\<le>t'\<and> (\<exists>n<length t. fst (t!n) = t'') 
          \<longrightarrow> evals (signal_shift t t'') c1)"
      using eval.simps(4)
      by fastforce
    then have "length (clip_timeline x t) > 0 \<and> y\<ge>x"
      using clip_timeline_exists 
      by auto

    oops
*)      

value "clip_timeline 2 [(0::real,a),(2,b),(8,c),(12,d),(15,e)]"
value "length (clip_timeline (fst ([(0,a)]!1)) [(0,a)])"
value "((clip_timeline x t, c1, \<gamma>), t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure (\<lambda>(t, c, _). size c + length t)"

lemma length_filter_implies:
  assumes "\<forall>n. P n \<longrightarrow> Q n"
  shows "length (filter P xs) \<le> length (filter Q xs)"
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ys)
  then show ?case
    using assms 
    by fastforce
qed

function robust :: "real \<Rightarrow> (real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> real \<Rightarrow> real" where
"robust p t (cMu f r) \<gamma> = (if (\<exists>n<length t. fst (t!n) = p) then f (find_time t p) - r else -1)"
| "robust p t (cNot c) \<gamma> = - (robust p t c \<gamma>)"
| "robust p t (cAnd c1 c2) \<gamma> = Min_gamma_comp \<gamma> (robust p t c1 \<gamma>) (robust p t c2 \<gamma>)"
| "robust p t (cUntil x y c1 c2) \<gamma> = (if x<0 \<or> y<0 \<or> (length (filter (\<lambda>z. z \<ge> p+x) (map fst t)) = 0) then -1 
      else (Max_gamma_comp \<gamma>
          (robust (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c2 \<gamma>)
          (Min_gamma_comp \<gamma> 
            (robust (Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) t c1 \<gamma>)
            (robust (Min (((set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))) - {Min (set (filter (\<lambda>z. z \<ge> p+x) (map fst t)))})) t 
              (cUntil 0 (y-p-x) c1 c2) \<gamma>))))"
  by pat_completeness auto
termination 
  apply (relation 
      "Wellfounded.measure (\<lambda>(p,t,c,\<gamma>). card (set (filter (\<lambda>z. z \<ge> p) (map fst t))) + size c)")
        apply simp+
proof -
  have "\<And>p t (x::real) y c1.
       \<not> x < 0 \<and> \<not> y < 0 \<and> (\<exists>a b. find (\<lambda>z. p+x \<le> fst z) t = Some (a, b)) \<Longrightarrow>
      (\<forall>xa. fst (the (find (\<lambda>z. p+x \<le> fst z) t)) \<le> xa \<longrightarrow> p \<le> xa)"
    using find_Some_iff2 option.sel
    by (smt (verit, del_insts))
  then have 1:"\<And>p t (x::real) y c1.
     \<not> x < 0 \<and> \<not> y < 0 \<and> (\<exists>a b. find (\<lambda>z. p+x \<le> fst z) t = Some (a, b)) \<Longrightarrow>
    length (filter (\<lambda>xa. fst (the (find (\<lambda>z. p+x \<le> fst z) t)) \<le> fst xa) t)
    \<le> length (filter (\<lambda>x. p \<le> fst x) t)"
    using length_filter_implies find_Some_iff option.sel
    by (smt (verit, best))
  then show "\<And>p t (x::real) y c1.
     \<not> x < 0 \<and> \<not> y < 0 \<and> (\<exists>a b. find (\<lambda>z. p+x \<le> fst z) t = Some (a, b)) \<Longrightarrow>
      length (filter (\<lambda>xa. fst (the (find (\<lambda>z. p+x \<le> fst z) t)) \<le> fst xa) t)
       < Suc (length (filter (\<lambda>x. p \<le> fst x) t) + size c1)"
    by fastforce
  then have "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p+x \<le> fst z) t = None) \<Longrightarrow>
      length (filter (\<lambda>xa. (fst (the (find (\<lambda>z. p+x \<le> fst z) t))) \<le> fst xa) t) + size c1
      < length (filter (\<lambda>xa. p \<le> fst xa) t) + size (cUntil x y c1 c2)"
    using 1 
    by fastforce
  then show "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p+x \<le> fst z) t = None) \<Longrightarrow>
       ((fst (the (find (\<lambda>z. p+x \<le> fst z) t)), t, c1, \<gamma>), p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure (\<lambda>(p, t, c, \<gamma>). length (filter (\<lambda>xa. p \<le> fst xa) t) + size c)"
    by force
  have "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p + x \<le> fst z) t = None) \<Longrightarrow>
      (\<exists>n<length t. fst (t!n) \<ge> p+x)"
    using find_Some_iff2 option.collapse
    by metis
  then have "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p + x \<le> fst z) t = None) \<Longrightarrow>
      length (filter (\<lambda>xa. p+x \<le> fst xa) t) > 0"
  proof -
    have "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real) P.
      ((\<exists>n<length t. (\<lambda>z. fst z \<ge> p+x) (t!n)) \<longrightarrow> length (filter (\<lambda>xa. p+x \<le> fst xa) t) > 0)"
      using add_0 bot_nat_0.not_eq_extremum length_filter_less nth_mem order_less_irrefl 
        sum_length_filter_compl
      by (metis (no_types, lifting))
    then show "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p + x \<le> fst z) t = None) \<Longrightarrow>
      length (filter (\<lambda>xa. p+x \<le> fst xa) t) > 0"
      using \<open>\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p + x \<le> fst z) t = None) \<Longrightarrow>
      (\<exists>n<length t. fst (t!n) \<ge> p+x)\<close>
      by metis
  qed
  then have "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p + x \<le> fst z) t = None) \<Longrightarrow>
       length (filter (\<lambda>za. (fst (the (find (\<lambda>xa. fst (the (find (\<lambda>z. p+x \<le> fst z) t)) < fst xa) t))) \<le> fst za) t)
      + size (cUntil 0 (y-p) c1 c2)
      < length (filter (\<lambda>xa. p \<le> fst xa) t) + size (cUntil x y c1 c2)"
  then show "\<And>(p::real) (t::(real\<times>('v::real_vector)) list) (x::real) (y::real) (c1::'v constraint) (c2::'v constraint) (\<gamma>::real).
       \<not> (x < 0 \<or> y < 0 \<or> find (\<lambda>z. p + x \<le> fst z) t = None) \<Longrightarrow>
       ((fst (the (find (\<lambda>xa. fst (the (find (\<lambda>z. p+x \<le> fst z) t)) < fst xa) t)), t,
         cUntil 0 (y-p) c1 c2, \<gamma>),
        p, t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure (\<lambda>(p, t, c, \<gamma>). length (filter (\<lambda>xa. p \<le> fst xa) t) + size c)"
    
    

    
    
    
    

proof -
  have 1:"\<And>x y \<gamma> t c1 c2.
   \<not> (length (clip_timeline x t) = 0 \<or> y < 0) \<longrightarrow>
   length (clip_timeline x t)\<le> length t"
    using clip_timeline_length 
    by blast
  then have "\<And>x y \<gamma> t c1 c2.
   \<not> (length (clip_timeline x t) = 0 \<or> y < 0) \<longrightarrow>
    size c1 + length (clip_timeline x t) < size (cUntil x y c1 c2) + length t"
    using 1 
    by fastforce
  then have "\<And>x y \<gamma> t c1 c2.
   \<not> (length (clip_timeline x t) = 0 \<or> y < 0) \<longrightarrow>
    ((clip_timeline x t, c1, \<gamma>), t, cUntil x y c1 c2, \<gamma>)
   \<in> Wellfounded.measure (\<lambda>(t, c, \<gamma>). size c + length t)"
    by simp
  then show "\<And>x y \<gamma> t c1 c2.
   \<not> (length (clip_timeline x t) = 0 \<or> y < 0) \<Longrightarrow>
       ((clip_timeline x t, c1, \<gamma>), t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure
           (\<lambda>(t, c, \<gamma>). size c + length t)"
    by auto
  then have "\<And>t x y c1 c2 \<gamma>.
       \<not> (length (clip_timeline x t) = 0 \<or> y < 0) \<Longrightarrow>
    length (drop 1 (map (\<lambda>z. (fst z - fst (clip_timeline x t ! 1), snd z)) (clip_timeline x t))) < length t"
    using Until_drop_length add_diff_cancel_right' add_diff_inverse_nat cancel_ab_semigroup_add_class.diff_right_commute clip_timeline_length diff_is_0_eq' diff_le_self diff_zero length_drop length_map nle_le
    by (smt (verit, del_insts))
  then show "\<And>t x y c1 c2 \<gamma>.
       \<not> (length (clip_timeline x t) = 0 \<or> y < 0) \<Longrightarrow>
       ((drop 1 (map (\<lambda>z. (fst z - fst (clip_timeline x t ! 1), snd z)) (clip_timeline x t)),
         cUntil 0 (y - x - fst ((clip_timeline x t)!1)) c1 c2, \<gamma>),
        t, cUntil x y c1 c2, \<gamma>)
       \<in> Wellfounded.measure (\<lambda>(t, c, \<gamma>). size c + length t)"
    by auto
qed

lemma robust_evals_works:
  fixes t :: "(real \<times> 'v::real_vector) list" and c :: "'v constraint"
  assumes "valid_signal t"
  shows "(robust t c 0 > 0) \<longrightarrow> (evals t c) \<and> (robust t c 0 < 0) \<longrightarrow> \<not>(evals t c)"
proof (induction c)
  case (cMu f r)
  then show ?case
    using robust.simps(1) evals.simps(1)
    by simp
next
  case (cNot c)
  then show ?case
    by simp
next
  case (cAnd c)
  then show ?case
    by argo
next
  case (cUntil x y c1 c2)
  then show ?case
    oops

end
