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

definition clip_timeline :: "real \<Rightarrow> real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> (real \<times> 'v) list" where
"clip_timeline x y t = take 
  (find_index (\<lambda>r. r>y) (map fst (drop (find_index (\<lambda>r. r\<ge>x) (map fst t)) t)))
  (drop (find_index (\<lambda>r. r\<ge>x) (map fst t)) t)"

lemma clip_timeline_length:"length (clip_timeline x y xs) \<le> length xs"
  using clip_timeline_def length_rev length_take linorder_not_le min_less_iff_conj 
    order_less_imp_le rev_drop
  by (metis (no_types, lifting))

value "clip_timeline 13.5 5 [(1,a),(2,b),(8,c),(12,d),(15,e)]"

function robust :: "(real \<times> 'v::real_vector) list \<Rightarrow> 'v constraint \<Rightarrow> real \<Rightarrow> real" where
"robust t (cMu f r) \<gamma> = f (find_time t 0) - r"
| "robust t (cNot c) \<gamma> = -(robust t c \<gamma>)"
| "robust t (cAnd c1 c2) \<gamma> = Max_gamma_comp \<gamma> (robust t c1 \<gamma>) (robust t c2 \<gamma>)"
| "robust t (cUntil x y c1 c2) \<gamma> = (if length (clip_timeline x y t) = 0 then -1 else 
    (if length (clip_timeline x y t) = 1 then
      (robust (clip_timeline x y t) c2 \<gamma>) else
    (Min_gamma_comp \<gamma>
      (robust (clip_timeline x y t) c2 \<gamma>)
      (Max_gamma_comp \<gamma> 
        (robust (clip_timeline x y t) c1 \<gamma>)
        (robust (map (\<lambda>p. (fst p - (fst ((clip_timeline x y t)!1)), snd p)) (drop 1 (clip_timeline x y t))) (cUntil 0 (y-x) c1 c2) \<gamma>)))))"
  by (pat_completeness, simp+)
termination 
  apply simp+
  by (size_change)
  

(*
Min_gamma_comp \<gamma> (L c2 (s # ss) \<gamma>) 
    (Max_gamma_comp \<gamma> (L c1 (s # ss) \<gamma>) (if ss = [] then 0 
      else (L (Until c1 c2) ss \<gamma>)))"
*)

end
