theory STL_sample
  imports STL

begin

definition valid_signal :: "(real \<times> 'v::real_vector) list \<Rightarrow> bool" where
"valid_signal xs = (distinct (map fst xs) \<and> (\<forall>n<length xs. fst (xs!n) \<ge> 0)
  \<and> (\<exists>n<length xs. fst (xs!n) = 0))"

definition find_time :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> 'v" where
"find_time xs r = (if (find (\<lambda>x. fst x = r) xs = None) then 0 else (snd (the (find (\<lambda>x. fst x = r) xs))))"

definition signal_shift :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> (real \<times> 'v::real_vector) list" where
"signal_shift xs r = filter (\<lambda>x. fst x\<ge>0) (map (\<lambda>x. (fst x - r, snd x)) xs)"

definition next_time :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> real" where
"next_time xs r = Min (set (filter (\<lambda>x. x>r) (map fst xs)))"

lemma next_time_0_find:
  fixes xs :: "(real \<times> 'v::real_vector) list"
  assumes "length xs > 1" "valid_signal xs"
  shows "find (\<lambda>x. fst x = next_time xs 0) xs \<noteq> None"
proof -
  have 0:"distinct (map fst xs) \<and> (\<forall>n<length (map fst xs). (map fst xs)!n \<ge> 0)
    \<and> (\<exists>n<length (map fst xs). (map fst xs)!n = 0) \<and> length (map fst xs) > 1"
    using assms length_map nth_map valid_signal_def
    by metis
  then have "\<exists>n<length (map fst xs). (map fst xs)!n > 0"
    using distinct_conv_nth leI nat_less_le nle_le not_gr_zero zero_neq_one
    by metis
  then have "(set (filter (\<lambda>x. x>0) (map fst xs))) \<noteq> {} \<and> finite (set (filter (\<lambda>x. x>0) (map fst xs)))"
    by force
  then have "next_time xs 0 \<in> (set (filter (\<lambda>x. x>0) (map fst xs)))"
    using next_time_def Min_in
    by metis
  then have "\<exists>n<length (filter (\<lambda>x. x>0) (map fst xs)). (filter (\<lambda>x. x>0) (map fst xs))!n = next_time xs 0"
    using in_set_conv_nth 
    by metis
  then show ?thesis 
    using filter_set find_None_iff in_set_conv_nth length_map member_filter nth_map nth_mem
    by (smt (verit))
qed

definition shorten_signal :: "(real \<times> 'v::real_vector) list \<Rightarrow> (real \<times> 'v::real_vector) list" where
"shorten_signal xs = signal_shift xs (next_time xs 0)"

value "find_time [(0,a),(1,b),(1.5,c)] 1.5"
value "signal_shift [(0,a),(1,b),(1.5,c)] 1.0"

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
    using signal_shift_def 0 distinct_map_filter map_eq_conv
    by (smt (verit, ccfv_threshold))
  then have "\<forall>n<length (signal_shift xs r). fst ((signal_shift xs r)!n) \<ge> 0"
    using signal_shift_def mem_Collect_eq nth_mem set_filter
    by (smt (verit, ccfv_threshold))
  then have "\<exists>x\<in>set xs. fst x = r" 
    using assms(2)
    by auto
  then have "\<exists>x\<in>set(signal_shift xs r). fst x = 0"
    using signal_shift_def image_eqI list.set_map mem_Collect_eq prod.sel(1) set_filter
    by (smt (verit, best))
  then have "0\<in>set(map fst (signal_shift xs r))"
    by force
  then have "\<exists>n<length (signal_shift xs r). fst ((signal_shift xs r)!n) = 0"
    using \<open>\<exists>x\<in>set (signal_shift xs r). fst x = 0\<close> in_set_conv_nth
    by metis
  then show ?thesis
    using valid_signal_def \<open>distinct (map fst (signal_shift xs r))\<close> 
      \<open>\<forall>n<length (signal_shift xs r). fst ((signal_shift xs r)!n) \<ge> 0\<close>
    by blast
qed

lemma shorten_signal_shortens:
  fixes xs :: "(real \<times> 'v::real_vector) list"
  assumes "length xs > 1" "valid_signal xs"
  shows "length (shorten_signal xs) + 1 = length xs"
proof -
  
lemma shorten_signal_valid:
  fixes xs :: "(real \<times> 'v::real_vector) list"
  assumes "valid_signal xs"
  shows "valid_signal (shorten_signal xs)"
proof -

fun evals :: "(real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"evals t (cMu f r) = (f (find_time t 0) > r)"
| "evals t (cNot c) = (\<not>(evals t c))"
| "evals t (cAnd c1 c2) = ((evals t c1) \<and> (evals t c2))"
| "evals t (cUntil x y c1 c2) = (\<exists>t'\<ge>x. t'\<le>y \<and> (\<exists>n<length t. fst (t!n) = t') \<and> evals (signal_shift t t') c2 
    \<and> (\<forall>t''. t''\<ge>0\<and>t''\<le>t'\<and> (\<exists>n<length t. fst (t!n) = t'') \<longrightarrow> evals (signal_shift t t'') c1))"

lemma cTrue_evals:"evals t cTrue"
  using cTrue_def evals.simps(1) zero_less_one
  by metis

lemma cOr_evals:"evals t (cOr c1 c2) = (evals t c1 \<or> evals t c2)"
  using cOr_def evals.simps(2,3)
  by metis

lemma cEventually_evals: "evals t (cEventually x y c) =
    (\<exists>t'\<ge>x. t'\<le>y \<and> (\<exists>n<length t. fst (t!n) = t') \<and> evals (signal_shift t t') c)"
  using evals.simps(4) cTrue_evals cEventually_def
  by metis

lemma cAlways_evals: "evals t (cAlways x y c) =
  (\<forall>t'. t'\<ge>x\<and>t'\<le>y\<and> (\<exists>n<length t. fst (t!n) = t') \<longrightarrow> evals (signal_shift t t') c)"
proof -
  have "evals t (cAlways x y c) = (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> (\<exists>n<length t. fst (t!n) = t') \<and> evals (signal_shift t t') (cNot c)))"
    using cEventually_evals cAlways_def evals.simps(2)
    by metis
  then show ?thesis
    using evals.simps(2)
    by blast
qed

end
