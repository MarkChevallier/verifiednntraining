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

fun evals :: "(real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"evals t (cMu f r) = (f (find_time t 0) > r)"
| "evals t (cNot c) = (\<not>(evals t c))"
| "evals t (cAnd c1 c2) = ((evals t c1) \<and> (evals t c2))"
| "evals t (cUntil x y c1 c2) = (\<exists>t'\<ge>x. t'\<le>y \<and> (\<exists>n<length t. fst (t!n) = t') \<and> evals (signal_shift t t') c2 
    \<and> (\<forall>t''. t''\<ge>0\<and>t''\<le>t'\<and> (\<exists>n<length t. fst (t!n) = t'') \<longrightarrow> evals (signal_shift t t'') c1))"


end
