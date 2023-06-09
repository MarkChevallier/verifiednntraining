theory STL_sample
  imports STL Code_Real_Approx_By_Float_2

begin

fun recurs_exist_list :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "recurs_exist_list P [] = False"
| "recurs_exist_list P (x#xs) = (P x \<or> recurs_exist_list P xs)"

lemma recurs_exist_list_equiv:"(\<exists>n<length t. P (t!n)) = (recurs_exist_list P t)"
proof (induct t)
  case Nil
  then show ?case 
    by auto
  case (Cons x xs)
  then show ?case
  proof (cases "P x")
    case True
    then show ?thesis 
      by force
  next
    case False
    then show ?thesis
    proof (cases "recurs_exist_list P xs")
      case True
      then show ?thesis 
        using Cons 
        by force
    next
      case False
      then show ?thesis
        using Cons \<open>\<not>(P x)\<close>
        by (metis in_set_conv_nth recurs_exist_list.simps(2) set_ConsD)
    qed
  qed
qed

lemma recurse_length_until:
  fixes P P' :: "'a \<Rightarrow> bool" and t :: "'a list"
  assumes "length t > 0"
  shows "(\<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n'))) 
    = ((P (t!0) \<and> P' (t!0)) \<or> (P' (t!0) \<and> (\<lambda>t. \<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n'))) (drop 1 t)))"
proof -
  obtain x xs where x:"t = x#xs"
    using assms Suc_pred' length_Suc_conv
    by meson
  then show ?thesis
  proof (cases "P x")
    case True
    then show ?thesis
      using x 
      by auto
  next
    case False
    {assume 1:"\<exists>n<length (x#xs). P ((x#xs)!n) \<and> (\<forall>n'\<le>n. P' ((x#xs)!n'))"
      then have "P' ((x#xs)!0)"
        using False 
        by blast
      have "\<exists>n<length (x#xs). n>0 \<and> P ((x#xs)!n) \<and> (\<forall>n'\<le>n. P' ((x#xs)!n'))"
        using 1 False nth_Cons_0 zero_less_iff_neq_zero
        by metis
      then have "\<exists>n<length xs. P (xs!n) \<and> (\<forall>n'\<le>n. P' (xs!n'))"
        using Suc_pred' length_Cons linorder_not_le not_less_eq nth_Cons_Suc
        by metis
      then have "((P ((x#xs)!0) \<and> P' ((x#xs)!0)) \<or> (P' ((x#xs)!0) \<and> (\<lambda>t. \<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n'))) (drop 1 (x#xs))))"
        using \<open>P' ((x#xs)!0)\<close>
        by auto}
    then have onew:"\<exists>n<length (x#xs). P ((x#xs)!n) \<and> (\<forall>n'\<le>n. P' ((x#xs)!n'))
        \<Longrightarrow> ((P ((x#xs)!0) \<and> P' ((x#xs)!0)) \<or> (P' ((x#xs)!0) \<and> (\<lambda>t. \<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n'))) (drop 1 (x#xs))))"
      by blast
    {assume 2:"((P ((x#xs)!0) \<and> P' ((x#xs)!0)) \<or> (P' ((x#xs)!0) \<and> (\<lambda>t. \<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n'))) (drop 1 (x#xs))))"
      then have "\<exists>n<length (x#xs). P ((x#xs)!n) \<and> (\<forall>n'\<le>n. P' ((x#xs)!n'))"
      proof (cases "P ((x#xs)!0) \<and> P' ((x#xs)!0)")
        case True
        then show ?thesis
          by blast
      next
        case False
        then have "(P' ((x#xs)!0) \<and> (\<lambda>t. \<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n'))) xs)"
          using 2 
          by auto
        then show ?thesis
          using Suc_pred' bot_nat_0.not_eq_extremum length_Cons linorder_not_le not_less_eq 
            nth_Cons_Suc 
          by (metis (no_types, opaque_lifting))
      qed}
    then show ?thesis
      using onew x
      by blast
  qed
qed

lemma recurse_length:
  fixes P :: "'a \<Rightarrow> bool" and t :: "'a list"
  assumes "length t > 0"
  shows "(\<exists>n<length t. P (t!n)) = (P (t!0) \<or> (\<lambda>t. \<exists>n<length t. P (t!n)) (drop 1 t))"
  using recurse_length_until [where ?P'="\<lambda>x. True"] assms
  by auto

lemma recurse_length_release_alt: 
  fixes foo bar :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" 
  assumes "\<And>t P P'. foo P P' t = (\<exists>n<length t. P (t!n) \<and> (\<forall>n'\<le>n. P' (t!n')))" and "\<And>P P'. bar P P' [] = False" 
    and "\<And>x xs P P'. bar P P' (x#xs) = ((P x \<and> P' x) \<or> ((P' x) \<and> bar P P' xs))"
  shows "\<And>P P' xs. foo P P' xs = bar P P' xs"
proof -
  {fix xs :: "'a list"
    have "\<And>P P'. foo P P' xs = bar P P' xs"
    proof (induct xs)
      case Nil
      then show ?case 
        using assms
        by simp
    next
      case (Cons x xs)
      then show ?case
      proof (cases "P x")
        case True
        then show ?thesis
          using assms
          by auto
      next
        case False
        {assume 1:"foo P P' (x#xs)"
          then have "P' x"
            using assms(1) 
            by auto
          then have "\<exists>n<length (x#xs). n>0 \<and> P ((x#xs)!n) \<and> (\<forall>n'\<le>n. P' ((x#xs)!n'))"
            using 1 assms(1) False nth_Cons_0 zero_less_iff_neq_zero
            by metis
          then have "\<exists>n<length xs. P (xs!n) \<and> (\<forall>n'\<le>n. P' (xs!n'))"
            using Suc_pred' length_Cons linorder_not_le not_less_eq nth_Cons_Suc
            by metis
          then have "foo P P' xs"
            using assms(1)
            by blast
          then have "((P ((x#xs)!0) \<and> P' ((x#xs)!0)) \<or> (P' ((x#xs)!0) \<and> bar P P' xs))"
            using Cons \<open>P' x\<close>
            by simp
          then have "bar P P' (x#xs)"
            using assms(3)
            by simp}
        then have onew:"foo P P' (x#xs) \<Longrightarrow> bar P P' (x#xs)"
          by blast
        {assume 2:"bar P P' (x#xs)"
          then have "((P ((x#xs)!0) \<and> P' ((x#xs)!0)) \<or> (P' ((x#xs)!0) \<and> bar P P' xs))"
            using assms(3)
            by simp
          then have "\<exists>n<length (x#xs). P ((x#xs)!n) \<and> (\<forall>n'\<le>n. P' ((x#xs)!n'))"
          proof (cases "P ((x#xs)!0) \<and> P' ((x#xs)!0)")
            case True
            then show ?thesis
              by blast
          next
            case False
            then have "(P' ((x#xs)!0) \<and> bar P P' xs)"
              using 2 assms(3)
              by auto
            then have "(P' ((x#xs)!0) \<and> (\<exists>n<length xs. P (xs!n) \<and> (\<forall>n'\<le>n. P' (xs!n'))))"
              using Cons assms(1)
              by blast
            then show ?thesis
              using Suc_pred' bot_nat_0.not_eq_extremum length_Cons linorder_not_le not_less_eq 
                nth_Cons_Suc 
              by (metis (no_types, opaque_lifting))
          qed
          then have "foo P P' (x#xs)"
            using assms(1) 
            by blast}
        then show ?thesis
          using onew 
          by blast
      qed
    qed}
  then show "\<And>P P' xs. foo P P' xs = bar P P' xs"
    by simp
qed

lemma recurse_length_alt: 
  fixes foo bar :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" 
  assumes "\<And>P t. foo P t = (\<exists>n<length t. P (t!n))" and "\<And>P. bar P [] = False" 
    and "\<And>P x xs. bar P (x#xs) = (P x \<or> bar P xs)"
  shows "\<And>P xs. foo P xs = bar P xs"
proof -
  {fix P :: "'a \<Rightarrow> bool" and xs :: "'a list"
    have "foo P xs = bar P xs"
    proof (induct xs)
      case Nil
      then show ?case 
        using assms 
        by force
    next
      case (Cons y ys)
      then show ?case
        using assms One_nat_def drop0 drop_Suc_Cons length_greater_0_conv list.discI nth_Cons_0 
          recurse_length
        by (metis (no_types, lifting))
    qed}
  then show "\<And>P xs. foo P xs = bar P xs"
    by simp
qed

lemma recurse_length_all:
  fixes foo bar :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes "\<And>t P. foo P t = (\<forall>n<length t. P (t!n))" and "\<And>P. bar P [] = True"
    and "\<And>x xs P. bar P (x#xs) = (P x \<and> bar P xs)"
  shows "foo P xs = bar P xs"
proof (induct xs)
  case Nil
  then show ?case 
    using assms 
    by force
next
  case (Cons x xs)
  then show ?case
    using assms less_Suc_eq_0_disj length_Cons nth_Cons_0 nth_Cons_Suc 
    by (smt (verit))
qed

lemma recurse_length_alt_Pdep: 
  fixes foo bar :: "('a list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" 
  assumes "\<And>P t t'. foo P t t' = (\<exists>n<length t. (P t') (t!n))" and "\<And>P t'. bar P [] t' = False" 
    and "\<And>P x xs t'. bar P (x#xs) t' = ((P t') x \<or> bar P xs t')"
  shows "foo P xs t' = bar P xs t'"
proof (induct xs)
  case Nil
  then show ?case 
    using assms 
    by simp
next
  case (Cons y ys)
  then show ?case
    using assms One_nat_def drop0 drop_Suc_Cons length_greater_0_conv list.discI nth_Cons_0 
      recurse_length
    by (metis (no_types, lifting))
qed

fun recurs_exist_list_Pdep :: "('a list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "recurs_exist_list_Pdep P [] t = False"
| "recurs_exist_list_Pdep P (x#xs) t = ((P t) x \<or> recurs_exist_list_Pdep P xs t)"

fun recurs_all_list :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "recurs_all_list P [] = True"
| "recurs_all_list P (x#xs) = (P x \<and> recurs_all_list P xs)"

fun recurs_exist_list_Pdep_real :: "('a list \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> real \<Rightarrow> real" where
  "recurs_exist_list_Pdep_real P [] t \<gamma> = -1"
| "recurs_exist_list_Pdep_real P (x#xs) t \<gamma> = Max_gamma_comp \<gamma> (recurs_exist_list_Pdep_real P xs t \<gamma>) ((P t) x)"

fun recurs_release :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "recurs_release P P' [] = False"
| "recurs_release P P' (x#xs) = ((P x \<and> P' x) \<or> ((P' x) \<and> recurs_release P P' xs))"

fun recurs_release_real :: "('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "recurs_release_real P P' [] \<gamma> E = -(abs E)"
| "recurs_release_real P P' (x#xs) \<gamma> E = (Max_gamma_comp \<gamma> (Min_gamma_comp \<gamma> (P x \<gamma>) (P' x \<gamma>))
      (Min_gamma_comp \<gamma> (P' x \<gamma>) (recurs_release_real P P' xs \<gamma> (P x \<gamma>))))"

lemma recurs_release_real_sound_0:
  assumes "\<And>z. Pr z 0 > 0 \<longrightarrow> P z" "\<And>z. Pr z 0 < 0 \<longrightarrow> \<not>(P z)"
      "\<And>z. P'r z 0 > 0 \<longrightarrow> P' z" "\<And>z. P'r z 0 < 0 \<longrightarrow> \<not>(P' z)"
  shows "(recurs_release_real Pr P'r t 0 E > 0 \<longrightarrow> recurs_release P P' t)"
      "recurs_release_real Pr P'r t 0 E < 0 \<longrightarrow> \<not>(recurs_release P P' t)"
proof (induct t arbitrary: E)
  case Nil
  then show "\<And>E. (recurs_release_real Pr P'r [] 0 E > 0 \<longrightarrow> recurs_release P P' [])"
      "\<And>E. recurs_release_real Pr P'r [] 0 E < 0 \<longrightarrow> \<not>(recurs_release P P' [])"
    by simp+
next
  case (Cons x xs)
  have 1:"\<And>E. recurs_release_real Pr P'r (x#xs) 0 E = (max (min (Pr x 0) (P'r x 0)) 
    (min (P'r x 0) (recurs_release_real Pr P'r xs 0 (Pr x 0))))"
    by force
  then show "\<And>E. recurs_release_real Pr P'r (x#xs) 0 E > 0 \<longrightarrow> recurs_release P P' (x#xs)"
    using Cons assms(1,3) recurs_release.simps(2)
    by (smt (verit))
  then show "\<And>E. recurs_release_real Pr P'r (x#xs) 0 E < 0 \<longrightarrow> \<not>(recurs_release P P' (x#xs))"
    using Cons assms(2,4) recurs_release.simps(2) 1
    by (smt (verit))
qed

lemma recurs_release_real_const_bel0: 
  assumes "\<And>z. \<forall>x\<le>0. P z x = P z 0" "\<And>z. \<forall>x\<le>0. P' z x = P' z 0"
  shows "\<And>z. \<forall>\<gamma>\<le>0. recurs_release_real P P' t \<gamma> (P z \<gamma>) = recurs_release_real P P' t 0 (P z 0)"
proof (induct t)
  case Nil
  then show ?case 
    using assms(1) recurs_release_real.simps(1)
    by metis
next
  case (Cons x xs)
  then show ?case
    using assms Max_gamma_const_bel0 Min_gamma_const_bel0 Max_gamma_comp_eq Min_gamma_comp_eq
      recurs_release_real.simps(2) recurs_release_real.elims
    by (smt (verit, ccfv_SIG))
qed

lemma recurs_release_real_const_bel0_const: 
  assumes "\<And>z. \<forall>x\<le>0. P z x = P z 0" "\<And>z. \<forall>x\<le>0. P' z x = P' z 0"
  shows "\<And>z. \<forall>\<gamma>\<le>0. recurs_release_real P P' t \<gamma> E = recurs_release_real P P' t 0 E"
proof (induct t)
  case Nil
  then show ?case 
    using assms(1) recurs_release_real.simps(1)
    by metis
next
  case (Cons x xs)
  then show ?case
    using assms Max_gamma_const_bel0 Min_gamma_const_bel0 Max_gamma_comp_eq Min_gamma_comp_eq
      recurs_release_real.simps(2) recurs_release_real.elims
    by (smt (verit, ccfv_SIG))
qed

lemma recurs_release_real_cont_0_var:
  assumes "\<And>z. isCont (P z) 0" "\<And>z. isCont (P' z) 0"
    "\<And>z. \<forall>x\<le>0. P z x = P z 0" "\<And>z. \<forall>x\<le>0. P' z x = P' z 0"
  shows "\<And>x. isCont (\<lambda>\<gamma>. recurs_release_real P P' t \<gamma> (P x \<gamma>)) 0"
proof (induct t)
  case Nil
  then show ?case 
    using recurs_release_real.simps(1) assms
    by auto
next
  case (Cons y ys)
  then have 1:"isCont (P' y) 0" "isCont (\<lambda>\<gamma>. recurs_release_real P P' ys \<gamma> (P y \<gamma>)) 0" 
    "(\<forall>x\<le>0. P' y x = P' y 0)"
    "isCont (P y) 0" "(\<forall>x\<le>0. P y x = P y 0)"
    using assms
    by blast+
  have 11:"\<forall>x\<le>0. recurs_release_real P P' ys x (P y x) = recurs_release_real P P' ys 0 (P y 0)"
    using assms recurs_release_real_const_bel0
    by meson
  have 2:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>))) 0"
    using 1(1-3) 11 Min_gamma_chain_cont_0 Min_gamma_comp_eq
    by presburger
  then have 3:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>)) 0"
    using 1(1,3-5) Min_gamma_chain_cont_0 Min_gamma_comp_eq
    by presburger
  have "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>) = Min_gamma_comp 0 (P y 0) (P' y 0)"
      "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>)) = Min_gamma_comp 0 (P' y 0) (recurs_release_real P P' ys 0 (P y 0))"
    using Min_gamma_const_bel0 1(3,5) Min_gamma_comp_eq 11
    by presburger+
  then have "isCont (\<lambda>\<gamma>. Max_gamma \<gamma> (Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>)) 
    (Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>)))) 0"
    using 1 2 3 Max_gamma_chain_cont_0
    by blast
  then show ?case
    using Max_gamma_comp_eq
    by simp
qed

lemma recurs_release_real_cont_0:
  assumes "\<And>z. isCont (P z) 0" "\<And>z. isCont (P' z) 0"
    "\<And>z. \<forall>x\<le>0. P z x = P z 0" "\<And>z. \<forall>x\<le>0. P' z x = P' z 0"
  shows "\<And>x. isCont (\<lambda>\<gamma>. recurs_release_real P P' t \<gamma> E) 0"
proof (induct t)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  then have 1:"isCont (P' y) 0" 
    "(\<forall>x\<le>0. P' y x = P' y 0)"
    "isCont (P y) 0" "(\<forall>x\<le>0. P y x = P y 0)"
    using assms
    by blast+
  then have 12:"isCont (\<lambda>\<gamma>. recurs_release_real P P' ys \<gamma> (P y \<gamma>)) 0"
    using recurs_release_real_cont_0_var assms
    by (metis (mono_tags))
  have 11:"\<forall>x\<le>0. recurs_release_real P P' ys x (P y x) = recurs_release_real P P' ys 0 (P y 0)"
    using assms recurs_release_real_const_bel0
    by meson
  have 2:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>))) 0"
    using 1(1-2) 11 12 Min_gamma_chain_cont_0 Min_gamma_comp_eq
    by presburger
  then have 3:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>)) 0"
    using 1 Min_gamma_chain_cont_0 Min_gamma_comp_eq
    by presburger
  have "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>) = Min_gamma_comp 0 (P y 0) (P' y 0)"
      "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>)) = Min_gamma_comp 0 (P' y 0) (recurs_release_real P P' ys 0 (P y 0))"
    using Min_gamma_const_bel0 1 Min_gamma_comp_eq 11
    by presburger+
  then have "isCont (\<lambda>\<gamma>. Max_gamma \<gamma> (Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>)) 
    (Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>)))) 0"
    using 1 2 3 Max_gamma_chain_cont_0
    by blast
  then show ?case
    using Max_gamma_comp_eq
    by simp
qed

lemma recurs_exist_list_Pdep_real_sound_0:
  assumes "\<And>t x. P t x > 0 \<longrightarrow> P' t x" "\<And>t x. P t x < 0 \<longrightarrow> \<not>(P' t x)"
  shows "(recurs_exist_list_Pdep_real P xs t 0 > 0) \<longrightarrow> (recurs_exist_list_Pdep P' xs t)"
      "(recurs_exist_list_Pdep_real P xs t 0 < 0) \<longrightarrow> \<not>(recurs_exist_list_Pdep P' xs t)"
proof (induct xs)
  case Nil 
  then show "(recurs_exist_list_Pdep_real P [] t 0 > 0) \<longrightarrow> (recurs_exist_list_Pdep P' [] t)"
    by auto
  then show "(recurs_exist_list_Pdep_real P [] t 0 < 0) \<longrightarrow> \<not>(recurs_exist_list_Pdep P' [] t)" 
    by simp
next
  case (Cons y ys)
  then show "(recurs_exist_list_Pdep_real P (y#ys) t 0 > 0) \<longrightarrow> (recurs_exist_list_Pdep P' (y#ys) t)"
    using assms
    by fastforce
  then show "(recurs_exist_list_Pdep_real P (y#ys) t 0 < 0) \<longrightarrow> \<not>(recurs_exist_list_Pdep P' (y#ys) t)"
    using Cons assms
    by force
qed

fun recurs_all_list_real :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> real \<Rightarrow> real" where 
  "recurs_all_list_real P [] \<gamma> = 1"
| "recurs_all_list_real P (x#xs) \<gamma> = Min_gamma_comp \<gamma> (if P x then 1 else -1) (recurs_all_list_real P xs \<gamma>)"

fun valid_constraints :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"valid_constraints p t (cMu f ct r) = (p\<in>set (map fst t))"
| "valid_constraints p t (cNot c) = (valid_constraints p t c)"
| "valid_constraints p t (cAnd c1 c2) = (valid_constraints p t c1 \<and> valid_constraints p t c2)"
| "valid_constraints p t (cUntil x y c1 c2) = (x \<ge> 0 \<and> y \<ge> 0)"

definition valid_signal :: "(real \<times> 'v) list \<Rightarrow> bool" where
"valid_signal xs = sorted_wrt (<) (map fst xs)"

(*
definition first_time :: "(real \<times> 'v) list \<Rightarrow> real" where
"first_time xs = Min (set (map fst xs))"

definition at_time :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> real" where
"at_time p xs = Min (set (filter (\<lambda>x. x\<ge>p) (map fst xs)))"

definition next_time :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> real" where
"next_time p xs = Min (set (filter (\<lambda>x. x>p) (map fst xs)))"
*)

fun find_time :: "(real \<times> 'v) list \<Rightarrow> real \<Rightarrow> 'v" where
"find_time [] r = undefined"
| "find_time (x#xs) r = (if fst x = r then snd x else find_time xs r)"

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

fun evals :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"evals p t (cMu f ct r) = (if (recurs_exist_list (\<lambda>z. fst z = p) t) then (f ct (find_time t p) > r) else False)"
| "evals p t (cNot c) = (\<not>(evals p t c))"
| "evals p t (cAnd c1 c2) = ((evals p t c1) \<and> (evals p t c2))"
| "evals p t (cUntil x y c1 c2) 
  = recurs_release (\<lambda>z. fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2) (\<lambda>z. evals (fst z) t c1 \<or> fst z < p) t"

lemma equiv_Until_semantics:
  fixes t :: "(real\<times>'v) list" and p x y :: real
    and c1 c2 :: "'v constraint"
  shows "((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1))) = (\<exists>n<length t. (\<lambda>z. fst z \<ge> p+x \<and> fst z \<le> p+y 
      \<and> evals (fst z) t c2 \<and> (\<forall>m<length t. (\<lambda>z'. evals (fst z') t c1 
        \<or> fst z' < p \<or> fst z' > (fst z)) (t!m))) (t!n))"
  by (smt (verit))

lemma equiv_Until_semantics_2:
  fixes t :: "(real\<times>'v) list" and p x y :: real
    and c1 c2 :: "'v constraint"
  assumes "valid_signal t" "x>0" "y>0"
  shows "((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1))) 
    = (\<exists>n<length t. fst (t!n) \<ge> p+x \<and> fst (t!n) \<le> p+y \<and> evals (fst (t!n)) t c2
      \<and> (\<forall>m\<le>n. evals (fst (t!m)) t c1 \<or> fst (t!m) < p))"
proof -
  have "\<And>P. \<And>n::nat. n<length t \<Longrightarrow> (\<forall>m<length t. P (t!m) \<or> m > n) = (\<forall>m\<le>n. P (t!m))"
    by (meson dual_order.trans linorder_not_less)
  then have 0:"\<And>P P'. (\<exists>n<length t. P' (t!n) \<and> (\<forall>m<length t. P (t!m) \<or> m > n))
      = (\<exists>n<length t. P' (t!n) \<and> (\<forall>m\<le>n. P (t!m)))"
    by blast
  have 1:"((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1)))
    = (\<exists>n<length t. fst (t!n) \<ge> p+x \<and> fst (t!n) \<le> p+y 
      \<and> evals (fst (t!n)) t c2 \<and>
        (\<forall>m<length t. evals (fst (t!m)) t c1 
        \<or> fst (t!m) < p \<or> fst (t!m) > (fst (t!n))))"
  proof -
    have "\<forall>n<length t. fst (t!n) \<ge> p \<longrightarrow> ((\<forall>m<length t. evals (fst (t!m)) t c1 
        \<or> fst (t!m) < p \<or> fst (t!m) > (fst (t!n))) \<longrightarrow> evals (fst (t!n)) t c1)"
      by fastforce
    then show ?thesis
      using assms(2) equiv_Until_semantics
      by (smt (verit))
  qed
  then show ?thesis
  proof -
    have "\<forall>n<length t. (\<forall>m>n. m<length t \<longrightarrow> fst (t!m) > fst (t!n))"
      using assms(1) valid_signal_def length_map nth_map sorted_wrt_iff_nth_less
      by metis
    then have "\<forall>n<length t. (\<forall>m<length t. (m>n) = (fst (t!m) > fst (t!n)))"
      using linorder_neq_iff order_less_asym'
      by metis
    then have "((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1)))
    = (\<exists>n<length t. fst (t!n) \<ge> p+x \<and> fst (t!n) \<le> p+y 
      \<and> evals (fst (t!n)) t c2 \<and>
        (\<forall>m<length t. evals (fst (t!m)) t c1 
        \<or> fst (t!m) < p \<or> m > n))"
      using 1 
      by blast
    then show ?thesis
      using 0 [where ?P'="\<lambda>z. fst z \<ge> p+x \<and> fst z \<le> p+y 
      \<and> evals (fst z) t c2" and ?P="\<lambda>z. evals (fst z) t c1 \<or> fst z < p"]
      by presburger
  qed
qed

lemma recurse_evals_Until_equiv:
  fixes p x y :: real and t :: "(real\<times>'v) list"
  assumes "valid_signal t" "x>0" "y>0"
  shows "evals p t (cUntil x y c1 c2)
      = ((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. fst (t!n) = p'') \<longrightarrow> evals p'' t c1)))"
proof -
  have "evals p t (cUntil x y c1 c2) 
      = (\<exists>n<length t. fst (t!n) \<ge> p+x \<and> fst (t!n) \<le> p+y \<and> evals (fst (t!n)) t c2
        \<and> (\<forall>m\<le>n. fst (t!m) < p \<or> evals (fst (t!m)) t c1))"
    using recurse_length_release_alt [where ?foo="\<lambda>P P' t. (\<exists>n<length t. P (t ! n) \<and> (\<forall>n'\<le>n. P' (t ! n')))"
      and ?bar="recurs_release" and ?xs="t" and ?P="\<lambda>z. fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2"
      and ?P'="\<lambda>z. evals (fst z) t c1 \<or> fst z < p"] evals.simps(4) [where ?p="p" and ?t="t" 
        and ?c1.0="c1" and ?c2.0="c2" and ?x="x" and ?y="y"]
    by auto
  then show ?thesis
    using equiv_Until_semantics_2 [where ?x="x" and ?y="y" and ?t="t" and ?p="p" and ?c1.0="c1" and ?c2.0="c2"] 
      assms
    by auto
qed

lemma cTrue_valid_constraints:
  "valid_constraints p t cTrue = (p\<in>set (map fst t))"
  using cTrue_def valid_constraints.simps(1)
  by metis

lemma cTrue_evals:"evals p t cTrue = (\<exists>n<length t. fst (t!n) = p)"
  using cTrue_def evals.simps(1) zero_less_one recurs_exist_list_equiv
  by (metis (mono_tags, lifting))

lemma cOr_valid_constraints:
  "valid_constraints p t (cOr c1 c2) = (valid_constraints p t c1 \<and> valid_constraints p t c2)"
  using cOr_def valid_constraints.simps(2,3)
  by metis

lemma cOr_evals:"evals p t (cOr c1 c2) = (evals p t c1 \<or> evals p t c2)"
  using cOr_def evals.simps(2,3)
  by metis

lemma cImplies_valid_constraints:
  "valid_constraints p t (cImplies c1 c2) = (valid_constraints p t c1 \<and> valid_constraints p t c2)"
  using cImplies_def cOr_def valid_constraints.simps(2,3)
  by metis

lemma cImplies_evals:"evals p t (cImplies c1 c2) = (evals p t c1 \<longrightarrow> evals p t c2)"
  using cOr_evals cImplies_def evals.simps(2)
  by metis

lemma cEventually_valid_constraints:
  "valid_constraints p t (cEventually x y c) = (x\<ge>0 \<and> y\<ge>0)"
  using cEventually_def valid_constraints.simps(4)
  by metis

lemma cEventually_evals: 
  assumes "x>0" "y>0" "valid_signal t"  
  shows "evals p t (cEventually x y c) = (\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. fst (t!n) = p') \<and> evals p' t c)"
  using evals.simps(4) cTrue_evals cEventually_def length_map nth_map nth_mem recurse_evals_Until_equiv assms
  by (smt (verit))

lemma cAlways_valid_constraints: "valid_constraints p t (cAlways x y c) = (x\<ge>0 \<and> y\<ge>0)"
  using cAlways_def valid_constraints.simps(2) cEventually_valid_constraints
  by metis

lemma cAlways_evals: 
  assumes "x>0" "y>0" "valid_signal t"  
  shows "evals p t (cAlways x y c) =
  (\<forall>p'. p'\<ge>p+x\<and>p'\<le>p+y\<and> (\<exists>n<length t. fst (t!n) = p') \<longrightarrow> evals p' t c)"
proof -
  have "evals p t (cAlways x y c) = evals p t (cNot (cEventually x y (cNot c)))"
    using cAlways_def
    by metis
  then have "evals p t (cAlways x y c) = (\<not>(\<exists>p'\<ge>p + x. p' \<le> p + y \<and> (\<exists>n<length t. fst (t ! n) = p') \<and> evals p' t (cNot c)))"
    using cEventually_evals evals.simps(2) assms
    by metis
  then have "evals p t (cAlways x y c) = (\<forall>p'\<ge>p + x. \<not>(p' \<le> p + y \<and> (\<exists>n<length t. fst (t ! n) = p') \<and> evals p' t (cNot c)))"
    by blast
  then have "evals p t (cAlways x y c) = (\<forall>p'\<ge>p + x. \<not>(p' \<le> p + y \<and> (\<exists>n<length t. fst (t ! n) = p') \<and> \<not>(evals p' t c)))"
    using evals.simps(2) 
    by simp
  then show ?thesis
    by blast
qed

(* definition clip_timeline :: "real \<Rightarrow> real \<Rightarrow> (real\<times>'v) list \<Rightarrow> (real\<times>'v) list" where
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

fun robust :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> 'v constraint \<Rightarrow> real \<Rightarrow> real" where
"robust p t (cMu f ct r) \<gamma> = (if (recurs_exist_list (\<lambda>z. fst z = p) t) then f ct (find_time t p) - r else -1)"
| "robust p t (cNot c) \<gamma> = - (robust p t c \<gamma>)"
| "robust p t (cAnd c1 c2) \<gamma> = Min_gamma_comp \<gamma> (robust p t c1 \<gamma>) (robust p t c2 \<gamma>)"
| "robust p t (cUntil x y c1 c2) \<gamma> = recurs_release_real 
    (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p+x)) (Min_gamma_comp \<gamma> ((p+y) - fst z) (robust (fst z) t c2 \<gamma>))) 
    (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p-fst z)) t \<gamma> (-1)"

lemma robust_sound_0:
  shows "\<And>p. (robust p t c 0 > 0) \<longrightarrow> (evals p t c)" 
       "\<And>p. (robust p t c 0 < 0) \<longrightarrow> \<not>(evals p t c)"
proof (induct c)
  case (cMu f ct r)
  then show "\<And>p. (robust p t (cMu f ct r) 0 > 0) \<longrightarrow> (evals p t (cMu f ct r))" 
       "\<And>p. (robust p t (cMu f ct r) 0 < 0) \<longrightarrow> \<not>(evals p t (cMu f ct r))"
    using recurs_exist_list_equiv
    by auto+
next
  case (cNot c)
  then show "\<And>p. (robust p t (cNot c) 0 > 0) \<longrightarrow> (evals p t (cNot c))" 
       "\<And>p. (robust p t (cNot c) 0 < 0) \<longrightarrow> \<not>(evals p t (cNot c))" 
    by force+
next
  case (cAnd c1 c2)
  then show "\<And>p. (robust p t (cAnd c1 c2) 0 > 0) \<longrightarrow> (evals p t (cAnd c1 c2))" 
       "\<And>p. (robust p t (cAnd c1 c2) 0 < 0) \<longrightarrow> \<not>(evals p t (cAnd c1 c2))"
     apply simp
  proof -
    {fix p :: real 
      assume "(robust p t (cAnd c1 c2) 0 < 0)"
      then have "\<not>(evals p t (cAnd c1 c2))"
        using cAnd
        by force}
    then show "\<And>p. (robust p t (cAnd c1 c2) 0 < 0) \<longrightarrow> \<not>(evals p t (cAnd c1 c2))"
      by blast
  qed
next
  case (cUntil x y c1 c2)
  then show "\<And>p. (robust p t (cUntil x y c1 c2) 0 > 0) \<longrightarrow> (evals p t (cUntil x y c1 c2))" 
       "\<And>p. (robust p t (cUntil x y c1 c2) 0 < 0) \<longrightarrow> \<not>(evals p t (cUntil x y c1 c2))"
    unfolding evals.simps(4) robust.simps(4)
  proof -
    have U1:"\<And>p z. Min_gamma_comp 0 (fst z - (p+x)) (Min_gamma_comp 0 (p+y - fst z) (robust (fst z) t c2 0)) > 0
      \<longrightarrow> fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2"
    proof -
      {fix z :: "(real\<times>'v)" and p :: real
        assume "Min_gamma_comp 0 (fst z - (p+x)) (Min_gamma_comp 0 (p+y - fst z) (robust (fst z) t c2 0)) > 0"
        then have "(fst z - (p+x))>0 \<and> (p+y-fst z) > 0 \<and> (robust (fst z) t c2 0) > 0"
          by force
        then have "fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2"
          using cUntil 
          by auto}
      then show "\<And>p z. Min_gamma_comp 0 (fst z - (p+x)) (Min_gamma_comp 0 (p+y - fst z) (robust (fst z) t c2 0)) > 0
      \<longrightarrow> fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2"
        by blast
    qed
    have U2:"\<And>p z. Min_gamma_comp 0 (fst z - (p+x)) (Min_gamma_comp 0 (p+y - fst z) (robust (fst z) t c2 0)) < 0
      \<longrightarrow> \<not>(fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2)"
    proof -
      {fix z :: "(real\<times>'v)" and p :: real
        assume "Min_gamma_comp 0 (fst z - (p+x)) (Min_gamma_comp 0 (p+y - fst z) (robust (fst z) t c2 0)) < 0"
        then have "(fst z - (p+x)) < 0 \<or> (p+y-fst z) < 0 \<or> (robust (fst z) t c2 0) < 0"
          by auto
        then have "\<not>(fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2)"
          using cUntil 
          by auto}
      then show "\<And>p z. Min_gamma_comp 0 (fst z - (p+x)) (Min_gamma_comp 0 (p+y - fst z) (robust (fst z) t c2 0)) < 0
      \<longrightarrow> \<not>(fst z \<ge> p+x \<and> fst z \<le> p+y \<and> evals (fst z) t c2)"
        by blast
    qed
    have U3:"\<And>p z. Max_gamma_comp 0 (robust (fst z) t c1 0) (p-fst z) > 0
      \<longrightarrow> evals (fst z) t c1 \<or> fst z < p"
    proof -
      {fix z :: "(real\<times>'v)" and p :: real
        assume "Max_gamma_comp 0 (robust (fst z) t c1 0) (p-fst z) > 0"
        then have "(robust (fst z) t c1 0) > 0 \<or> (p-fst z) > 0"
          by auto
        then have "(evals (fst z) t c1 \<or> fst z < p)"
          using cUntil 
          by auto}
      then show "\<And>p z. Max_gamma_comp 0 (robust (fst z) t c1 0) (p-fst z) > 0
      \<longrightarrow> evals (fst z) t c1 \<or> fst z < p"
        by blast
    qed
    have U4:"\<And>p z. Max_gamma_comp 0 (robust (fst z) t c1 0) (p-fst z) < 0
      \<longrightarrow> \<not>(evals (fst z) t c1 \<or> fst z < p)"
    proof -
      {fix z :: "(real\<times>'v)" and p :: real
        assume "Max_gamma_comp 0 (robust (fst z) t c1 0) (p-fst z) < 0"
        then have "(robust (fst z) t c1 0) < 0 \<and> (p-fst z) < 0"
          by auto
        then have "\<not>(evals (fst z) t c1 \<or> fst z < p)"
          using cUntil 
          by simp}
      then show "\<And>p z. Max_gamma_comp 0 (robust (fst z) t c1 0) (p-fst z) < 0
      \<longrightarrow> \<not>(evals (fst z) t c1 \<or> fst z < p)"
        by blast
    qed
    then show "(\<And>p. 0 < recurs_release_real
               (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)))
               (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)) t 0 (-1) \<longrightarrow>
          recurs_release (\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2) (\<lambda>z. evals (fst z) t c1 \<or> fst z < p)
           t)" 
       "(\<And>p. recurs_release_real
           (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)))
           (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)) t 0 (-1)
          < 0 \<longrightarrow>
          \<not> recurs_release (\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2)
              (\<lambda>z. evals (fst z) t c1 \<or> fst z < p) t)"
    proof -
      {fix p :: real
        have "0 < recurs_release_real
               (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)))
               (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)) t 0 (-1) \<longrightarrow>
          recurs_release (\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2) (\<lambda>z. evals (fst z) t c1 \<or> fst z < p)
           t"
          "recurs_release_real
           (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)))
           (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)) t 0 (-1)
          < 0 \<longrightarrow>
          \<not> recurs_release (\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2)
              (\<lambda>z. evals (fst z) t c1 \<or> fst z < p) t"
          using U1 U2 U3 U4 recurs_release_real_sound_0
            [where ?Pr="\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>))" 
              and ?P'r="\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)"
              and ?P="\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2"
              and ?P'="\<lambda>z. evals (fst z) t c1 \<or> fst z < p" and ?t="t"]
          by blast+}
      then show "(\<And>p. 0 < recurs_release_real
                   (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)))
                   (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)) t 0 (-1) \<longrightarrow>
              recurs_release (\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2) (\<lambda>z. evals (fst z) t c1 \<or> fst z < p)
               t)" 
           "(\<And>p. recurs_release_real
               (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)))
               (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)) t 0 (-1)
              < 0 \<longrightarrow>
              \<not> recurs_release (\<lambda>z. p + x \<le> fst z \<and> fst z \<le> p + y \<and> evals (fst z) t c2)
                  (\<lambda>z. evals (fst z) t c1 \<or> fst z < p) t)"
        by blast+
    qed
  qed
qed

lemma robust_const_bel0:
  shows "\<And>p. \<forall>\<gamma>\<le>0. robust p t c \<gamma> = robust p t c 0"
proof (induct c)
  case (cMu f r)
  then show ?case
    by simp
next
  case (cNot c)
  then show ?case 
    using robust.simps(2) 
    by metis
next
  case (cAnd c1 c2)
  then show ?case
    using Min_gamma_const_bel0 Min_gamma_comp_eq robust.simps(3)
    by metis
next
  case (cUntil x y c1 c2)
  then have "\<And>z. \<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)) 
        = Min_gamma_comp 0 (fst z - (p + x)) (Min_gamma_comp 0 (p + y - fst z) (robust (fst z) t c2 0))"
      "\<And>z. \<forall>\<gamma>\<le>0. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)
        = Max_gamma_comp 0 (robust (fst z) t c1 0) (p - fst z)"
    using Min_gamma_const_bel0 Min_gamma_comp_eq Max_gamma_const_bel0 Max_gamma_comp_eq
    by metis+
  then show ?case
    using robust.simps(4) recurs_release_real_const_bel0_const [where ?t="t"
      and ?P="\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>))"
      and ?P'="\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)" and ?E="-1"]
    by auto
qed

lemma robust_cont_0:
  shows "\<And>p. isCont (robust p t c) 0" 
proof (induct c)
  case (cMu f r)
  then show ?case 
    by simp
next
  case (cNot c)
  then show ?case
    by simp
next
  case (cAnd c1 c2)
  then have "\<forall>\<gamma>\<le>0. robust p t c1 \<gamma> = robust p t c1 0"
    "\<forall>x\<le>0. robust p t c2 x = robust p t c2 0"
    using robust_const_bel0 
    by force+
  then show ?case
    using cAnd Min_gamma_chain_cont_0 [where ?f="robust p t c1" and ?g="robust p t c2"] Min_gamma_comp_eq 
    by fastforce
next
  case (cUntil x y c1 c2)
  {fix p :: real
    let ?P="\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (fst z - (p + x)) (Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>))"
    let ?P'="\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (fst z) t c1 \<gamma>) (p - fst z)"
    {fix z :: "(real\<times>'v)"
      have 1:"\<forall>\<gamma>\<le>0. robust (fst z) t c1 \<gamma> = robust (fst z) t c1 0"
          "\<forall>\<gamma>\<le>0. robust (fst z) t c2 \<gamma> = robust (fst z) t c2 0"
        using robust_const_bel0 recurs_release_real.simps robust.simps(4)
        by blast+
      then have 3:"isCont (?P' z) 0"
        using cUntil Max_gamma_chain_cont_0 [where ?f="robust (fst z) t c1" and ?g="\<lambda>\<gamma>. p - fst z"]
          Max_gamma_comp_eq 
        by fastforce
      then have 4:"\<forall>\<gamma>\<le>0. ?P' z \<gamma> = ?P' z 0"
        using Max_gamma_const_bel0 Max_gamma_comp_eq 1
        by presburger
      then have 5:"\<forall>\<gamma>\<le>0. ?P z \<gamma> = ?P z 0"
        using 1 Min_gamma_const_bel0 Min_gamma_comp_eq
        by presburger
      have 2:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)) 0"
        using 1 cUntil Min_gamma_chain_cont_0 [where ?g="robust (fst z) t c2" and ?f="\<lambda>\<gamma>. p + y - fst z"]
          Min_gamma_comp_eq
        by fastforce
      have "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>) = Min_gamma_comp 0 (p + y - fst z) (robust (fst z) t c2 0)"
        using 1 Min_gamma_const_bel0 Min_gamma_comp_eq
        by presburger
      then have "isCont (?P z) 0" "isCont (?P' z) 0" "\<forall>\<gamma>\<le>0. ?P' z \<gamma> = ?P' z 0"
        using 2 cUntil Min_gamma_chain_cont_0 [where ?f="\<lambda>\<gamma>. fst z-(p+x)" and ?g="\<lambda>\<gamma>. Min_gamma_comp \<gamma> (p + y - fst z) (robust (fst z) t c2 \<gamma>)"]
          Min_gamma_comp_eq 3 4
        by fastforce+
      then have "isCont (?P z) 0" "isCont (?P' z) 0" "\<forall>\<gamma>\<le>0. ?P' z \<gamma> = ?P' z 0" "\<forall>\<gamma>\<le>0. ?P z \<gamma> = ?P z 0"
        using 5
        by blast+}
    then have "isCont (\<lambda>\<gamma>. recurs_release_real ?P ?P' t \<gamma> (-1)) 0"
      using recurs_release_real_cont_0 [where ?P="?P" and ?P'="?P'" and ?t="t"]
      by blast}
  then show ?case
    using robust.simps(4)
    by auto
qed

lemma robust_sound:
  assumes "robust p t c \<midarrow>0\<rightarrow> x"
  shows "x>0 \<longrightarrow> evals p t c"
    "x<0 \<longrightarrow> \<not>evals p t c"
  using robust_cont_0 robust_sound_0 LIM_unique assms continuous_within
  by blast+

definition evalsb :: "real \<Rightarrow> ((real\<times>'v) list) list \<Rightarrow> 'v constraint \<Rightarrow> bool list" where
"evalsb p T c = map (\<lambda>t. evals p t c) T"

definition robustb :: "real \<Rightarrow> ((real\<times>'v) list) list \<Rightarrow> 'v constraint \<Rightarrow> real \<Rightarrow> real list" where
"robustb p T c \<gamma> = map (\<lambda>t. robust p t c \<gamma>) T"

lemma robustb_sound:
  assumes "\<forall>n<length T. (\<lambda>\<gamma>. (robustb p T c \<gamma>)!n) \<midarrow>0\<rightarrow> X!n"
  shows "\<forall>n<length T. (X!n) > 0 \<longrightarrow> (evalsb p T c)!n"
    "\<forall>n<length T. (X!n) < 0 \<longrightarrow> \<not>((evalsb p T c)!n)"
proof -
  {fix n :: nat
    assume "n<length T"
    then have "(\<lambda>\<gamma>. (robustb p T c \<gamma>)!n) \<midarrow>0\<rightarrow> robust p (T!n) c 0"
      using robustb_def robust_cont_0 LIM_cong continuous_at nth_map
      by (smt (verit))}
  then have "\<forall>n<length T. X!n = robust p (T!n) c 0"
    using assms LIM_unique
    by blast
  then show "\<forall>n<length T. (X!n) > 0 \<longrightarrow> (evalsb p T c)!n"
    "\<forall>n<length T. (X!n) < 0 \<longrightarrow> \<not>((evalsb p T c)!n)"
  using robust_sound_0 robustb_def evalsb_def LIM_cong nth_map
  by metis+
qed

fun nthint :: "'a list \<Rightarrow> int \<Rightarrow> 'a" where
"nthint [] n = undefined"
| "nthint (x # xs) n = (if eqint n 0 then x else nthint xs ((absint n)-1))"

fun Feval :: "cterm \<Rightarrow> real list \<Rightarrow> real" where
"Feval (Get n) xs = nthint xs n"
| "Feval (Add c1 c2) xs = Feval c1 xs + Feval c2 xs"
| "Feval (Mult c1 c2) xs = Feval c1 xs * Feval c2 xs"
| "Feval (Uminus c) xs = -1 * (Feval c xs)"
| "Feval (Divide c1 c2) xs = Feval c1 xs / Feval c2 xs"

fun constraintright :: "real list constraint \<Rightarrow> bool" where
"constraintright (cMu f ct r) = (f = Feval)"
| "constraintright (cNot c) = constraintright c"
| "constraintright (cAnd c1 c2) = (constraintright c1 \<and> constraintright c2)"
| "constraintright (cUntil x y c1 c2) = (constraintright c1 \<and> constraintright c2)"

typedef rconstraint = "{c. constraintright c}"
  morphisms to_constraint to_rconstraint 
  using constraintright.simps(1) 
  by blast

declare to_constraint_inverse [simp]
  to_rconstraint_inverse [simp]

setup_lifting type_definition_rconstraint

lift_definition revals :: "real \<Rightarrow> (real\<times>real list) list \<Rightarrow> rconstraint \<Rightarrow> bool" is evals .

lift_definition rrobust :: "real \<Rightarrow> (real \<times>real list) list \<Rightarrow> rconstraint \<Rightarrow> real \<Rightarrow> real" is robust .

lemma rrobust_sound:
  fixes p :: real and t :: "(real\<times>real list) list" and c :: rconstraint and x :: real
  assumes "rrobust p t c \<midarrow>0\<rightarrow> x"
  shows "x>0 \<longrightarrow> revals p t c"
    "x<0 \<longrightarrow> \<not>revals p t c"
proof -
  have "robust p t (to_constraint c) \<midarrow>0\<rightarrow> x"
    using assms
    by (simp add: rrobust.rep_eq)
  then have "x>0 \<longrightarrow> evals p t (to_constraint c)"
    "x<0 \<longrightarrow> \<not>evals p t (to_constraint c)"
    using robust_sound
    by blast+
  then show "x>0 \<longrightarrow> revals p t c"
    "x<0 \<longrightarrow> \<not>revals p t c"
    by (simp add: revals.rep_eq)+
qed

(* Type constructors for code generation *)
definition mkGet :: "int \<Rightarrow> cterm" where
"mkGet n = Get n"

definition mkAdd :: "cterm \<Rightarrow> cterm \<Rightarrow> cterm" where
"mkAdd ct1 ct2 = Add ct1 ct2"

definition mkMult :: "cterm \<Rightarrow> cterm \<Rightarrow> cterm" where
"mkMult ct1 ct2 = Mult ct1 ct2"

definition mkUminus :: "cterm \<Rightarrow> cterm" where
"mkUminus ct = Uminus ct"

definition mkDivide :: "cterm \<Rightarrow> cterm \<Rightarrow> cterm" where
"mkDivide ct1 ct2 = Divide ct1 ct2"

definition mkMu :: "(cterm \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> cterm \<Rightarrow> real \<Rightarrow> 'v constraint" where
  "mkMu f ct r = cMu f ct r"

definition mkNot :: "'v constraint \<Rightarrow> 'v constraint" where
  "mkNot c = cNot c"

definition mkAnd :: "'v constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
  "mkAnd c1 c2 = cAnd c1 c2"

definition mkUntil :: "real \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
  "mkUntil x y c1 c2 = cUntil x y c1 c2"

export_code mkGet mkAdd mkMult mkUminus mkDivide mkMu mkNot mkAnd mkUntil evals robust Feval
 in OCaml
  module_name STLLoss

end
