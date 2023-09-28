theory STL_sample
  imports STL

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
  "recurs_release_real P P' [] \<gamma> E = Min_gamma_comp \<gamma> E (-E)"
| "recurs_release_real P P' (x#xs) \<gamma> E = (Max_gamma_comp \<gamma> (Min_gamma_comp \<gamma> (P x \<gamma>) (P' x \<gamma>))
      (Min_gamma_comp \<gamma> (P' x \<gamma>) (recurs_release_real P P' xs \<gamma> (P x \<gamma>))))"

fun drecurs_release_real :: "(real list \<Rightarrow> real \<Rightarrow> real) 
  \<Rightarrow> (real list \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real list list \<Rightarrow> real \<Rightarrow> int \<Rightarrow> int 
  \<Rightarrow> (real list \<Rightarrow> real \<Rightarrow> int \<Rightarrow> real) \<Rightarrow> (real list \<Rightarrow> real \<Rightarrow> int \<Rightarrow> real) 
  \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"drecurs_release_real P P' [] \<gamma> i j dP dP' E dE = dMin_gamma_ds \<gamma> E dE (-E) (-dE)"
| "drecurs_release_real P P' (x#xs) \<gamma> i j dP dP' E dE = (dMax_gamma_ds \<gamma> 
    (Min_gamma_comp \<gamma> (P x \<gamma>) (P' x \<gamma>))
      (dMin_gamma_ds \<gamma> (P x \<gamma>) (dP x \<gamma> j) (P' x \<gamma>) (dP' x \<gamma> j))
    (Min_gamma_comp \<gamma> (P' x \<gamma>) (recurs_release_real P P' xs \<gamma> (P x \<gamma>)))
      (dMin_gamma_ds \<gamma> (P' x \<gamma>) (dP' x \<gamma> j) 
        (recurs_release_real P P' xs \<gamma> (P x \<gamma>)) 
        (drecurs_release_real P P' xs \<gamma> i j dP dP' (P x \<gamma>) (dP x \<gamma> j))))"

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
  shows "\<And>z. \<forall>\<gamma>\<le>0. recurs_release_real P P' t \<gamma> E = recurs_release_real P P' t 0 E"
proof (induct t arbitrary: E)
  case Nil
  then show ?case 
    using assms(1) recurs_release_real.simps(1) Min_gamma_const_bel0 Min_gamma_comp_eq
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
proof (induct t arbitrary: E)
  case Nil
  then show ?case 
    using assms(1) recurs_release_real.simps(1) Min_gamma_const_bel0 Min_gamma_comp_eq
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
  have "\<And>z. isCont (\<lambda>\<gamma>. -(P z \<gamma>)) 0" "\<And>z. \<forall>x\<le>0. -(P z x) = -(P z 0)"
    using assms(1,3) apply simp 
    using assms(1,3) by metis
  then have "\<And>x. isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P x \<gamma>) (-(P x \<gamma>))) 0"
    using Min_gamma_chain_cont_0 Min_gamma_comp_eq assms(1,3) 
    by presburger
  then show ?case 
    using recurs_release_real.simps(1)
    by simp
next
  case (Cons y ys)
  then have 1:"isCont (P' y) 0" "isCont (\<lambda>\<gamma>. recurs_release_real P P' ys \<gamma> (P y \<gamma>)) 0" 
    "(\<forall>x\<le>0. P' y x = P' y 0)"
    "isCont (P y) 0" "(\<forall>x\<le>0. P y x = P y 0)"
    using assms
    by blast+
  have 11:"\<forall>x\<le>0. recurs_release_real P P' ys x (P y x) = recurs_release_real P P' ys 0 (P y 0)"
    using assms recurs_release_real_const_bel0
    by metis
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
  case Nil 
  then show ?case
    using Min_gamma_cont_0 Min_gamma_comp_eq recurs_release_real.simps(1)
    by simp    
next
  case (Cons y ys)
  then have 1:"isCont (P' y) 0" "isCont (\<lambda>\<gamma>. recurs_release_real P P' ys \<gamma> E) 0"
    "\<forall>x\<le>0. P' y x = P' y 0" "\<forall>x\<le>0. E = E" "isCont (\<lambda>x. E) 0"
    "isCont (P y) 0" "\<forall>x\<le>0. P y x = P y 0"
    using assms continuous_const
    by blast+
  have 10:"isCont (\<lambda>\<gamma>. recurs_release_real P P' ys \<gamma> (P y \<gamma>)) 0"
    using recurs_release_real_cont_0_var assms
    by metis
  have "\<forall>x\<le>0. recurs_release_real P P' ys x E = recurs_release_real P P' ys 0 E"
    using assms recurs_release_real_const_bel0
    by meson
  then have 12:"\<forall>x\<le>0. recurs_release_real P P' ys x (P y x) = recurs_release_real P P' ys 0 (P y 0)" 
    using Min_gamma_const_bel0 1 Min_gamma_comp_eq assms(3-4) recurs_release_real_const_bel0_const
    by (smt (verit, del_insts))
  then have 2:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>))) 0"
    using 1(1,3) 10 Min_gamma_chain_cont_0 Min_gamma_comp_eq
    by presburger
  then have 3:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>)) 0"
    using 1 Min_gamma_chain_cont_0 Min_gamma_comp_eq
    by presburger
  have "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>) = Min_gamma_comp 0 (P y 0) (P' y 0)"
      "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>)) = Min_gamma_comp 0 (P' y 0) (recurs_release_real P P' ys 0 (P y 0))"
    using Min_gamma_const_bel0 1 Min_gamma_comp_eq 12
    by presburger+
  then have "isCont (\<lambda>\<gamma>. Max_gamma \<gamma> (Min_gamma_comp \<gamma> (P y \<gamma>) (P' y \<gamma>)) 
    (Min_gamma_comp \<gamma> (P' y \<gamma>) (recurs_release_real P P' ys \<gamma> (P y \<gamma>)))) 0"
    using 2 3 Max_gamma_chain_cont_0
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

fun valid_constraints :: "real \<Rightarrow> (real list) list \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"valid_constraints p t (cMu f ct r) = (p\<in>set (map hd t))"
| "valid_constraints p t (cNot c) = (valid_constraints p t c)"
| "valid_constraints p t (cAnd c1 c2) = (valid_constraints p t c1 \<and> valid_constraints p t c2)"
| "valid_constraints p t (cUntil x y c1 c2) = (x \<ge> 0 \<and> y \<ge> 0)"

definition valid_signal :: "(real list) list \<Rightarrow> bool" where
"valid_signal xs = sorted_wrt (<) (map hd xs)"

(*
definition first_time :: "(real \<times> 'v) list \<Rightarrow> real" where
"first_time xs = Min (set (map fst xs))"

definition at_time :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> real" where
"at_time p xs = Min (set (filter (\<lambda>x. x\<ge>p) (map fst xs)))"

definition next_time :: "real \<Rightarrow> (real \<times> 'v) list \<Rightarrow> real" where
"next_time p xs = Min (set (filter (\<lambda>x. x>p) (map fst xs)))"
*)

fun find_time :: "(real list) list \<Rightarrow> real \<Rightarrow> real list" where
"find_time [] r = undefined"
| "find_time (x#xs) r = (if hd x = r then x else find_time xs r)"

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

fun evals :: "real \<Rightarrow> (real list) list \<Rightarrow> (real list) constraint \<Rightarrow> bool" where
"evals p t (cMu f ct r) = (if (recurs_exist_list (\<lambda>z. hd z = p) t) then (f ct (find_time t p) > r) else False)"
| "evals p t (cNot c) = (\<not>(evals p t c))"
| "evals p t (cAnd c1 c2) = ((evals p t c1) \<and> (evals p t c2))"
| "evals p t (cUntil x y c1 c2) 
  = recurs_release (\<lambda>z. hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2) (\<lambda>z. evals (hd z) t c1 \<or> hd z < p) t"

lemma equiv_Until_semantics:
  fixes t :: "real list list" and p x y :: real
    and c1 c2 :: "real list constraint"
  shows "((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. hd (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. hd (t!n) = p'') \<longrightarrow> evals p'' t c1))) = (\<exists>n<length t. (\<lambda>z. hd z \<ge> p+x \<and> hd z \<le> p+y 
      \<and> evals (hd z) t c2 \<and> (\<forall>m<length t. (\<lambda>z'. evals (hd z') t c1 
        \<or> hd z' < p \<or> hd z' > (hd z)) (t!m))) (t!n))"
  by (smt (verit))

lemma equiv_Until_semantics_2:
  fixes t :: "real list list" and p x y :: real
    and c1 c2 :: "real list constraint"
  assumes "valid_signal t" "x>0" "y>0"
  shows "((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. hd (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. hd (t!n) = p'') \<longrightarrow> evals p'' t c1))) 
    = (\<exists>n<length t. hd (t!n) \<ge> p+x \<and> hd (t!n) \<le> p+y \<and> evals (hd (t!n)) t c2
      \<and> (\<forall>m\<le>n. evals (hd (t!m)) t c1 \<or> hd (t!m) < p))"
proof -
  have "\<And>P. \<And>n::nat. n<length t \<Longrightarrow> (\<forall>m<length t. P (t!m) \<or> m > n) = (\<forall>m\<le>n. P (t!m))"
    by (meson dual_order.trans linorder_not_less)
  then have 0:"\<And>P P'. (\<exists>n<length t. P' (t!n) \<and> (\<forall>m<length t. P (t!m) \<or> m > n))
      = (\<exists>n<length t. P' (t!n) \<and> (\<forall>m\<le>n. P (t!m)))"
    by blast
  have 1:"((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. hd (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. hd (t!n) = p'') \<longrightarrow> evals p'' t c1)))
    = (\<exists>n<length t. hd (t!n) \<ge> p+x \<and> hd (t!n) \<le> p+y 
      \<and> evals (hd (t!n)) t c2 \<and>
        (\<forall>m<length t. evals (hd (t!m)) t c1 
        \<or> hd (t!m) < p \<or> hd (t!m) > (hd (t!n))))"
  proof -
    have "\<forall>n<length t. hd (t!n) \<ge> p \<longrightarrow> ((\<forall>m<length t. evals (hd (t!m)) t c1 
        \<or> hd (t!m) < p \<or> hd (t!m) > (hd (t!n))) \<longrightarrow> evals (hd (t!n)) t c1)"
      by fastforce
    then show ?thesis
      using assms(2) equiv_Until_semantics
      by (smt (verit))
  qed
  then show ?thesis
  proof -
    have "\<forall>n<length t. (\<forall>m>n. m<length t \<longrightarrow> hd (t!m) > hd (t!n))"
      using assms(1) valid_signal_def length_map nth_map sorted_wrt_iff_nth_less
      by metis
    then have "\<forall>n<length t. (\<forall>m<length t. (m>n) = (hd (t!m) > hd (t!n)))"
      using linorder_neq_iff order_less_asym'
      by metis
    then have "((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. hd (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. hd (t!n) = p'') \<longrightarrow> evals p'' t c1)))
    = (\<exists>n<length t. hd (t!n) \<ge> p+x \<and> hd (t!n) \<le> p+y 
      \<and> evals (hd (t!n)) t c2 \<and>
        (\<forall>m<length t. evals (hd (t!m)) t c1 
        \<or> hd (t!m) < p \<or> m > n))"
      using 1 
      by blast
    then show ?thesis
      using 0 [where ?P'="\<lambda>z. hd z \<ge> p+x \<and> hd z \<le> p+y 
      \<and> evals (hd z) t c2" and ?P="\<lambda>z. evals (hd z) t c1 \<or> hd z < p"]
      by presburger
  qed
qed

lemma recurse_evals_Until_equiv:
  fixes p x y :: real and t :: "real list list"
  assumes "valid_signal t" "x>0" "y>0"
  shows "evals p t (cUntil x y c1 c2)
      = ((\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. hd (t!n) = p') \<and> evals p' t c2 
    \<and> (\<forall>p''. p''\<ge>p\<and>p''\<le>p'\<and> (\<exists>n<length t. hd (t!n) = p'') \<longrightarrow> evals p'' t c1)))"
proof -
  have "evals p t (cUntil x y c1 c2) 
      = (\<exists>n<length t. hd (t!n) \<ge> p+x \<and> hd (t!n) \<le> p+y \<and> evals (hd (t!n)) t c2
        \<and> (\<forall>m\<le>n. hd (t!m) < p \<or> evals (hd (t!m)) t c1))"
    using recurse_length_release_alt [where ?foo="\<lambda>P P' t. (\<exists>n<length t. P (t ! n) \<and> (\<forall>n'\<le>n. P' (t ! n')))"
      and ?bar="recurs_release" and ?xs="t" and ?P="\<lambda>z. hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2"
      and ?P'="\<lambda>z. evals (hd z) t c1 \<or> hd z < p"] evals.simps(4) [where ?p="p" and ?t="t" 
        and ?c1.0="c1" and ?c2.0="c2" and ?x="x" and ?y="y"]
    by auto
  then show ?thesis
    using equiv_Until_semantics_2 [where ?x="x" and ?y="y" and ?t="t" and ?p="p" and ?c1.0="c1" and ?c2.0="c2"] 
      assms
    by auto
qed

lemma cTrue_valid_constraints:
  "valid_constraints p t cTrue = (p\<in>set (map hd t))"
  using cTrue_def valid_constraints.simps(1)
  by metis

lemma cTrue_evals:"evals p t cTrue = (\<exists>n<length t. hd (t!n) = p)"
  unfolding cTrue_def
  using evals.simps(1) zero_less_one recurs_exist_list_equiv
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
  shows "evals p t (cEventually x y c) = (\<exists>p'\<ge>p+x. p'\<le>p+y \<and> (\<exists>n<length t. hd (t!n) = p') \<and> evals p' t c)"
  using evals.simps(4) cTrue_evals cEventually_def length_map nth_map nth_mem recurse_evals_Until_equiv assms
  by (smt (verit))

lemma cAlways_valid_constraints: "valid_constraints p t (cAlways x y c) = (x\<ge>0 \<and> y\<ge>0)"
  using cAlways_def valid_constraints.simps(2) cEventually_valid_constraints
  by metis

lemma cAlways_evals: 
  assumes "x>0" "y>0" "valid_signal t"  
  shows "evals p t (cAlways x y c) =
  (\<forall>p'. p'\<ge>p+x\<and>p'\<le>p+y\<and> (\<exists>n<length t. hd (t!n) = p') \<longrightarrow> evals p' t c)"
proof -
  have "evals p t (cAlways x y c) = evals p t (cNot (cEventually x y (cNot c)))"
    using cAlways_def
    by metis
  then have "evals p t (cAlways x y c) = (\<not>(\<exists>p'\<ge>p + x. p' \<le> p + y \<and> (\<exists>n<length t. hd (t ! n) = p') \<and> evals p' t (cNot c)))"
    using cEventually_evals evals.simps(2) assms
    by metis
  then have "evals p t (cAlways x y c) = (\<forall>p'\<ge>p + x. \<not>(p' \<le> p + y \<and> (\<exists>n<length t. hd (t ! n) = p') \<and> evals p' t (cNot c)))"
    by blast
  then have "evals p t (cAlways x y c) = (\<forall>p'\<ge>p + x. \<not>(p' \<le> p + y \<and> (\<exists>n<length t. hd (t ! n) = p') \<and> \<not>(evals p' t c)))"
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

fun robust :: "real \<Rightarrow> real list list \<Rightarrow> real list constraint \<Rightarrow> real \<Rightarrow> real" where
"robust p t (cMu f ct r) \<gamma> = (if (recurs_exist_list (\<lambda>z. hd z = p) t) then f ct (find_time t p) - r else -1)"
| "robust p t (cNot c) \<gamma> = - (robust p t c \<gamma>)"
| "robust p t (cAnd c1 c2) \<gamma> = Min_gamma_comp \<gamma> (robust p t c1 \<gamma>) (robust p t c2 \<gamma>)"
| "robust p t (cUntil x y c1 c2) \<gamma> = recurs_release_real 
    (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p+x)) (Min_gamma_comp \<gamma> ((p+y) - hd z) (robust (hd z) t c2 \<gamma>))) 
    (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p-hd z)) t \<gamma> 0"

fun update_rl :: "real list \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real list" where
"update_rl [] j r = []" 
| "update_rl (x#xs) j r = (if j = 0 then (r#xs) else (x#(update_rl xs (j-1) r)))"

lemma update_rl_update:
  fixes n :: nat
  shows "update_rl xs (int n) r = list_update xs n r"
proof (cases "xs=[]")
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
  proof (induction n arbitrary: xs)
    case 0
    then show ?case
      using update_rl.simps
      by (metis int_ops(1) list_update_code(2) update_rl.elims)
  next
    case (Suc m)
    then have "xs = (hd xs)#(tl xs)"
      using False
      by simp
    then have 1:"update_rl xs (int (Suc m)) r = ((hd xs)#(update_rl (tl xs) (int m) r))"
      using update_rl.simps
      by (smt (verit, ccfv_SIG) int_plus less_numeral_extra(4) of_nat_less_0_iff of_nat_neq_0 one_less_of_natD plus_1_eq_Suc)
    then have "list_update xs (Suc m) r = ((hd xs)#(list_update (tl xs) m r))"
      by (metis \<open>xs = hd xs # tl xs\<close> list_update_code(3))
    then show ?case
      using 1 Suc
      by (metis list_update_nonempty update_rl.simps(1))
  qed
qed

lemma nthint_nth:
  fixes n :: nat
  assumes "n<length xs"
  shows "nthint xs (int n) = nth xs n"
proof (insert assms, induction n arbitrary: xs)
  case 0
  then have "length xs > 0"
    by blast
  then have "xs = (hd xs)#(tl xs)"
    by simp
  then show ?case
    by (metis int_ops(1) nth_Cons_0 nthint_Cons_0)
next
  case (Suc m)
  then have "length xs > 0"
    by auto
  then have "xs = (hd xs)#(tl xs)"
    by simp
  have "length (tl xs) > 0"
    using Suc.prems(1) Zero_not_Suc bot_nat_0.not_eq_extremum length_Cons less_Suc0 \<open>length xs > 0\<close>
    by simp
  then have "m<length (tl xs)"
    using Suc.prems(1) 
    by auto
  then show ?case
    using Suc \<open>m<length (tl xs)\<close> nth_Cons_Suc nthint_Cons_plusone \<open>xs = (hd xs)#(tl xs)\<close>
    by (metis add.commute of_nat_0_le_iff of_nat_Suc)
qed

lemma nthint_update_rl_eq:
  fixes n :: nat
  assumes "n<length xs"
  shows "nthint (update_rl xs (int n) r) (int n) = r"
  using assms nthint_nth update_rl_update length_list_update nth_list_update_eq
  by metis

lemma nthint_update_rl_neq:
  fixes n m :: nat
  assumes "n<length xs" "k<length xs" "n\<noteq>k"
  shows "nthint (update_rl xs (int n) r) (int k) = nthint xs (int k)"
  using assms nthint_nth update_rl_update length_list_update nth_list_update_neq
  by metis

lemma lam_deriv:
  fixes n j :: nat
  assumes "n<length xs" "j<length xs"
  shows "((\<lambda>y. nthint (update_rl xs j y) n) has_real_derivative (if n=j then 1 else 0)) (at x)"
  using nthint_update_rl_eq assms nthint_update_rl_neq
  by simp

primrec update_signal :: "real list list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real list list" where
"update_signal [] i j = (\<lambda>x. [])"
| "update_signal (y#ys) i j = (if i = 0 then (\<lambda>x. (update_rl y j x)#ys)
    else (if i < 0 then (\<lambda>x. (y#ys)) else (\<lambda>x. y # (update_signal ys (i-1) j x))))"

lemma drecurs_release_real_correct:
  fixes i j :: nat and xs :: "real list list" and \<gamma> E dE :: real
    and P P' :: "real list \<Rightarrow> real \<Rightarrow> real"
    and dP dP' :: "real list \<Rightarrow> real \<Rightarrow> int \<Rightarrow> real"
  assumes "i < length xs" "j < length (xs!i)" "((\<lambda>y. E) has_real_derivative dE) (at x)"
    "\<And>xs::(real list list). \<And>m n::nat. \<lbrakk>m<length xs; n<length (xs!i)\<rbrakk> \<Longrightarrow> ((\<lambda>y. P ((update_signal xs (int i) (int j) y)!i) \<gamma>) has_real_derivative (dP ((update_signal xs (int i) (int j) x)!i) \<gamma> j)) (at x)"
    "\<And>xs::(real list list). \<And>m n::nat. \<lbrakk>m<length xs; n<length (xs!i)\<rbrakk> \<Longrightarrow> ((\<lambda>y. P' ((update_signal xs (int i) (int j) y)!i) \<gamma>) has_real_derivative (dP' ((update_signal xs (int i) (int j) x)!i) \<gamma> j)) (at x)"
    "\<gamma>>0" "\<forall>m<length xs. \<forall>n<length xs. length (xs!m) = length (xs!n)"
  shows "((\<lambda>y. recurs_release_real P P' (update_signal xs (int i) (int j) y) \<gamma> E) has_real_derivative
    (drecurs_release_real P P' (update_signal xs (int i) (int j) x) \<gamma> (int i) (int j) dP dP' E dE)) (at x)"
proof (insert assms(1-3,7), induction xs)
  case Nil
  then show ?case
    by (metis less_nat_zero_code list.size(3))
next
  case (Cons z zs)
  then show ?case
  proof (cases "int i = 0")
    case True
    then have 1:"\<And>y. recurs_release_real P P' (update_signal (z#zs) (int i) (int j) y) \<gamma> E
      = Max_gamma_comp \<gamma> (Min_gamma_comp \<gamma> (P (update_rl z (int j) y) \<gamma>) (P' (update_rl z (int j) y) \<gamma>))
       (Min_gamma_comp \<gamma> (P' (update_rl z (int j) y) \<gamma>) (recurs_release_real P P' zs \<gamma> (P (update_rl z (int j) y) \<gamma>)))"
      by simp
    have "\<And>y. drecurs_release_real P P' (update_signal (z#zs) (int i) (int j) y) \<gamma> (int i) (int j) dP dP' E dE
      = (dMax_gamma_ds \<gamma> 
    (Min_gamma_comp \<gamma> (P (update_rl z (int j) y) \<gamma>) (P' (update_rl z (int j) y) \<gamma>))
      (dMin_gamma_ds \<gamma> (P (update_rl z (int j) y) \<gamma>) (dP (update_rl z (int j) y) \<gamma> j) (P' (update_rl z (int j) y) \<gamma>) (dP' (update_rl z (int j) y) \<gamma> (int j)))
    (Min_gamma_comp \<gamma> (P' (update_rl z (int j) y) \<gamma>) (recurs_release_real P P' zs \<gamma> (P (update_rl z (int j) y) \<gamma>)))
      (dMin_gamma_ds \<gamma> (P' (update_rl z (int j) y) \<gamma>) (dP' (update_rl z (int j) y) \<gamma> (int j))
        (recurs_release_real P P' zs \<gamma> (P (update_rl z (int j) y) \<gamma>)) (drecurs_release_real P P' zs \<gamma> (int i) (int j) dP dP' (P (update_rl z (int j) y) \<gamma>) (dP (update_rl z (int j) y) \<gamma> (int j)))))"
      using True drecurs_release_real.simps(2)
      by simp
    have "((\<lambda>y. (recurs_release_real P P' zs \<gamma> (P (update_rl z (int j) y) \<gamma>)))
        has_real_derivative (drecurs_release_real P P' zs \<gamma> (int i) (int j) dP dP' (P (update_rl z (int j) x) \<gamma>) (dP (update_rl z (int j) x) \<gamma> (int j)))) (at x)"
    proof (cases "zs=[]")
      case True
      then have 0:"j<length ((z#zs)!i) \<and> i<length (z#zs) \<and> (\<forall>y. (update_signal (z#zs) (int i) (int j) y ! i) = update_rl z (int j) y)"
        using assms(7) Cons(2-3)
        by simp
      then have 1:"((\<lambda>y. P (update_rl z (int j) y) \<gamma>) has_real_derivative (dP (update_rl z (int j) x) \<gamma> (int j))) (at x)"
        using assms(4)
        by force
      then have "((\<lambda>y. -(P (update_rl z (int j) y) \<gamma>)) has_real_derivative -(dP (update_rl z (int j) x) \<gamma> (int j))) (at x)"
        by (simp add: DERIV_minus)
      then show ?thesis
        using True 0 1 assms(6)
          dMin_gamma_chain [where ?\<gamma>="\<gamma>" and ?f="\<lambda>y. P (update_rl z (int j) y) \<gamma>" and ?g="\<lambda>y. -(P (update_rl z (int j) y) \<gamma>)"
            and ?Df="dP (update_rl z (int j) x) \<gamma> (int j)" and ?Dg="-(dP (update_rl z (int j) x) \<gamma> (int j))" and ?x="x"]
        by simp
    next
      case False
      then have 0:"j<length (zs!i) \<and> i<length zs \<and> (\<forall>y. (update_signal (z#zs) (int i) (int j) y ! i) = (update_rl z (int j) y))"
        using assms(7) Cons(2-3) \<open>int i = 0\<close>
        
      then show ?thesis
        using Cons(1) 
        
        
        
        
        
        
      then show ?thesis
        using Cons \<open>int i = 0\<close>


        
      using Cons \<open>int i = 0\<close> assms(6) 
    have "((\<lambda>y. (Min_gamma_comp \<gamma> (P' (fst z, (update_rl (snd z) j y)) \<gamma>) 
          (recurs_release_real P P' zs \<gamma> (P (fst z, (update_rl (snd z) j y)) \<gamma>))))
        has_real_derivative (dMin_gamma_ds \<gamma> 
          (P' (fst z, (update_rl (snd z) j x)) \<gamma>) 
            (dP' (fst z, (update_rl (snd z) j x)) \<gamma> j)
          (recurs_release_real P P' zs \<gamma> (P (fst z, (update_rl (snd z) j x)) \<gamma>)) 
            (drecurs_release_real P P' zs \<gamma> (P (fst z, (update_rl (snd z) j x)) \<gamma>) i j dP dP'))) (at x)"
      using dMin_gamma_chain assms(4-5) Cons
      
*)
    
    

fun valid_ct :: "cterm \<Rightarrow> real list \<Rightarrow> bool" where
"valid_ct (Get n) xs = (nat n < length xs \<and> n\<ge>0)"
| "valid_ct (Const r) xs = True"
| "valid_ct (Add c1 c2) xs = (valid_ct c1 xs \<and> valid_ct c2 xs)"
| "valid_ct (Mult c1 c2) xs = (valid_ct c1 xs \<and> valid_ct c2 xs)"
| "valid_ct (Uminus c) xs = (valid_ct c xs)"
| "valid_ct (Divide c1 c2) xs = (valid_ct c1 xs \<and> valid_ct c2 xs)"

fun dFeval :: "cterm \<Rightarrow> real list \<Rightarrow> int \<Rightarrow> real" where
"dFeval (Get n) xs m = (if n=m then 1 else 0)"
| "dFeval (Const r) xs m = 0"
| "dFeval (Add c1 c2) xs m = dFeval c1 xs m + dFeval c2 xs m"
| "dFeval (Mult c1 c2) xs m = Feval c2 xs * dFeval c1 xs m + Feval c1 xs * dFeval c2 xs m"
| "dFeval (Uminus c) xs m = -1 * (dFeval c xs m)"
| "dFeval (Divide c1 c2) xs m = ((dFeval c1 xs m * Feval c2 xs) - (Feval c1 xs * dFeval c2 xs m)) / (Feval c2 xs * Feval c2 xs)"

lemma dFeval_correct:
  fixes m :: nat
  assumes "m<length xs" "valid_ct ct xs" 
    "\<forall>c c1 c2. subcterm ct c \<and> c = (Divide c1 c2) \<longrightarrow> Feval c2 (update_rl xs (int m) x) \<noteq> 0"
  shows "((\<lambda>y. Feval ct (update_rl xs (int m) y)) has_real_derivative 
    (dFeval ct (update_rl xs (int m) x) (int m))) (at x)"
proof (insert assms(2,3), induction ct)
  case (Get n)
  then have "nat n < length xs \<and> n \<ge> 0"
    by auto
  have "\<And>m n::nat. \<And>xs::real list. \<lbrakk>m<length xs; n<length xs\<rbrakk> \<Longrightarrow> 
    ((\<lambda>y. Feval (Get (int n)) (update_rl xs (int m) y)) has_real_derivative 
    (dFeval (Get (int n)) (update_rl xs (int m) x) (int m))) (at x)"
    using Feval.simps(1) dFeval.simps(1) lam_deriv
  by simp
  then have "((\<lambda>y. Feval (Get (int (nat n))) (update_rl xs (int m) y)) has_real_derivative 
    (dFeval (Get (int (nat n))) (update_rl xs (int m) x) (int m))) (at x)"
    using assms(1) \<open>nat n < length xs \<and> n \<ge> 0\<close>
    by blast
  then show ?case
    using Get.prems 
    by auto 
next
  case (Const r)
  then show ?case
    using dFeval.simps(2) Feval.simps(2)
    by simp
next
  case (Add c1 c2)
  then have "\<forall>c c3 c4. (subcterm c1 c \<and> c = (Divide c3 c4)) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    "\<forall>c c3 c4. subcterm c2 c \<and> c = (Divide c3 c4) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    using subcterm_trans
    by auto+
  then show ?case
    using dFeval.simps(3) Feval.simps(3) Add
    by (simp add: Deriv.field_differentiable_add)
next
  case (Mult c1 c2)
  then have "valid_ct c1 xs \<and> valid_ct c2 xs"
    by simp
  then have "\<forall>c c3 c4. subcterm c1 c \<and> c = (Divide c3 c4) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    "\<forall>c c3 c4. subcterm c2 c \<and> c = (Divide c3 c4) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    using subcterm_trans Mult
    by auto+
  then have "((\<lambda>y. Feval c1 (update_rl xs (int m) y)) has_field_derivative dFeval c1 (update_rl xs (int m) x) (int m)) (at x within UNIV)"
    "((\<lambda>y. Feval c2 (update_rl xs (int m) y)) has_field_derivative dFeval c2 (update_rl xs (int m) x) (int m)) (at x within UNIV)"
    using Mult \<open>valid_ct c1 xs \<and> valid_ct c2 xs\<close>
    by blast+
  then have "((\<lambda>x. Feval c1 (update_rl xs (int m) x) * Feval c2 (update_rl xs (int m) x)) has_real_derivative
     Feval c1 (update_rl xs (int m) x) * dFeval c2 (update_rl xs (int m) x) (int m) +
     dFeval c1 (update_rl xs (int m) x) (int m) * Feval c2 (update_rl xs (int m) x))
     (at x)"
    using DERIV_mult'[where ?f="\<lambda>y. Feval c1 (update_rl xs (int m) y)" and ?D="dFeval c1 (update_rl xs (int m) x) (int m)"
        and ?g="\<lambda>y. Feval c2 (update_rl xs (int m) y)" and ?E="dFeval c2 (update_rl xs (int m) x) (int m)" and ?x="x" and ?s="UNIV"]
    by blast
  then have "((\<lambda>x. Feval (Mult c1 c2) (update_rl xs (int m) x)) has_real_derivative
     Feval c1 (update_rl xs (int m) x) * dFeval c2 (update_rl xs (int m) x) (int m) +
     dFeval c1 (update_rl xs (int m) x) (int m) * Feval c2 (update_rl xs (int m) x))
     (at x)"
    using Feval.simps(4) 
    by presburger
  then show ?case
    using dFeval.simps(4) [where ?c1.0="c1" and ?c2.0="c2" and ?xs="update_rl xs (int m) x" and ?m="int m"]
      add.commute mult.commute
    by metis
next
  case (Uminus c)
  then have "valid_ct c xs" "\<forall>c5 c3 c4. subcterm c c5 \<and> c5 = (Divide c3 c4) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    apply simp using subcterm_trans Uminus
    by auto
  then have "((\<lambda>y. Feval c (update_rl xs (int m) y)) has_field_derivative dFeval c (update_rl xs (int m) x) (int m)) (at x within UNIV)"
    using Uminus 
    by simp
  then show ?case
    using Feval.simps(5) dFeval.simps(5) Deriv.field_differentiable_minus 
    by fastforce
next
  case (Divide c1 c2)
  have "subcterm (Divide c1 c2) (Divide c1 c2)"
    by simp
  then have "Feval c2 (update_rl xs (int m) x) \<noteq> 0"
    using Divide(4) 
    by simp
  then have "valid_ct c1 xs \<and> valid_ct c2 xs"
    using Divide
    by simp
  then have "\<forall>c c3 c4. subcterm c1 c \<and> c = (Divide c3 c4) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    "\<forall>c c3 c4. subcterm c2 c \<and> c = (Divide c3 c4) \<longrightarrow> Feval c4 (update_rl xs (int m) x) \<noteq> 0"
    using subcterm_trans Divide
    by auto+
  then have "((\<lambda>y. Feval c1 (update_rl xs (int m) y)) has_field_derivative dFeval c1 (update_rl xs (int m) x) (int m)) (at x within UNIV)"
    "((\<lambda>y. Feval c2 (update_rl xs (int m) y)) has_field_derivative dFeval c2 (update_rl xs (int m) x) (int m)) (at x within UNIV)"
    using Divide \<open>valid_ct c1 xs \<and> valid_ct c2 xs\<close> 
    by presburger+
  then show ?case
    using Feval.simps(6) dFeval.simps(6) \<open>Feval c2 (update_rl xs (int m) x) \<noteq> 0\<close> DERIV_divide
    by fastforce
qed

fun drobust :: "real \<Rightarrow> real list list \<Rightarrow> real list constraint \<Rightarrow> real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real" where
"drobust p t (cMu f ct r) \<gamma> i j = (if f = Feval then dFeval ct (nthint t i) j else 0)"
| "drobust p t (cNot c) \<gamma> i j = - (drobust p t c \<gamma> i j)"
| "drobust p t (cAnd c1 c2) \<gamma> i j = dMin_gamma_ds \<gamma>
  (robust p t c1 \<gamma>)
    (drobust p t c1 \<gamma> i j)
  (robust p t c2 \<gamma>)
    (drobust p t c2 \<gamma> i j)"
| "drobust p t (cUntil x y c1 c2) \<gamma> i j = recurs_release_real 
    (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p+x)) (Min_gamma_comp \<gamma> ((p+y) - hd z) (robust (hd z) t c2 \<gamma>))) 
    (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p-hd z)) t \<gamma> (-1)"

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
    have U1:"\<And>p z. Min_gamma_comp 0 (hd z - (p+x)) (Min_gamma_comp 0 (p+y - hd z) (robust (hd z) t c2 0)) > 0
      \<longrightarrow> hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2"
    proof -
      {fix z :: "real list" and p :: real
        assume "Min_gamma_comp 0 (hd z - (p+x)) (Min_gamma_comp 0 (p+y - hd z) (robust (hd z) t c2 0)) > 0"
        then have "(hd z - (p+x))>0 \<and> (p+y-hd z) > 0 \<and> (robust (hd z) t c2 0) > 0"
          by force
        then have "hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2"
          using cUntil 
          by auto}
      then show "\<And>p z. Min_gamma_comp 0 (hd z - (p+x)) (Min_gamma_comp 0 (p+y - hd z) (robust (hd z) t c2 0)) > 0
      \<longrightarrow> hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2"
        by blast
    qed
    have U2:"\<And>p z. Min_gamma_comp 0 (hd z - (p+x)) (Min_gamma_comp 0 (p+y - hd z) (robust (hd z) t c2 0)) < 0
      \<longrightarrow> \<not>(hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2)"
    proof -
      {fix z :: "real list" and p :: real
        assume "Min_gamma_comp 0 (hd z - (p+x)) (Min_gamma_comp 0 (p+y - hd z) (robust (hd z) t c2 0)) < 0"
        then have "(hd z - (p+x)) < 0 \<or> (p+y-hd z) < 0 \<or> (robust (hd z) t c2 0) < 0"
          by auto
        then have "\<not>(hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2)"
          using cUntil 
          by auto}
      then show "\<And>p z. Min_gamma_comp 0 (hd z - (p+x)) (Min_gamma_comp 0 (p+y - hd z) (robust (hd z) t c2 0)) < 0
      \<longrightarrow> \<not>(hd z \<ge> p+x \<and> hd z \<le> p+y \<and> evals (hd z) t c2)"
        by blast
    qed
    have U3:"\<And>p z. Max_gamma_comp 0 (robust (hd z) t c1 0) (p-hd z) > 0
      \<longrightarrow> evals (hd z) t c1 \<or> hd z < p"
    proof -
      {fix z :: "real list" and p :: real
        assume "Max_gamma_comp 0 (robust (hd z) t c1 0) (p-hd z) > 0"
        then have "(robust (hd z) t c1 0) > 0 \<or> (p-hd z) > 0"
          by auto
        then have "(evals (hd z) t c1 \<or> hd z < p)"
          using cUntil 
          by auto}
      then show "\<And>p z. Max_gamma_comp 0 (robust (hd z) t c1 0) (p-hd z) > 0
      \<longrightarrow> evals (hd z) t c1 \<or> hd z < p"
        by blast
    qed
    have U4:"\<And>p z. Max_gamma_comp 0 (robust (hd z) t c1 0) (p-hd z) < 0
      \<longrightarrow> \<not>(evals (hd z) t c1 \<or> hd z < p)"
    proof -
      {fix z :: "real list" and p :: real
        assume "Max_gamma_comp 0 (robust (hd z) t c1 0) (p-hd z) < 0"
        then have "(robust (hd z) t c1 0) < 0 \<and> (p-hd z) < 0"
          by auto
        then have "\<not>(evals (hd z) t c1 \<or> hd z < p)"
          using cUntil 
          by simp}
      then show "\<And>p z. Max_gamma_comp 0 (robust (hd z) t c1 0) (p-hd z) < 0
      \<longrightarrow> \<not>(evals (hd z) t c1 \<or> hd z < p)"
        by blast
    qed
    then show "(\<And>p. 0 < recurs_release_real
               (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)))
               (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)) t 0 0 \<longrightarrow>
          recurs_release (\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2) (\<lambda>z. evals (hd z) t c1 \<or> hd z < p)
           t)" 
       "(\<And>p. recurs_release_real
           (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)))
           (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)) t 0 0
          < 0 \<longrightarrow>
          \<not> recurs_release (\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2)
              (\<lambda>z. evals (hd z) t c1 \<or> hd z < p) t)"
    proof -
      {fix p :: real
        have "0 < recurs_release_real
               (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)))
               (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)) t 0 0 \<longrightarrow>
          recurs_release (\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2) (\<lambda>z. evals (hd z) t c1 \<or> hd z < p)
           t"
          "recurs_release_real
           (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)))
           (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)) t 0 0
          < 0 \<longrightarrow>
          \<not> recurs_release (\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2)
              (\<lambda>z. evals (hd z) t c1 \<or> hd z < p) t"
          using U1 U2 U3 U4 recurs_release_real_sound_0
            [where ?Pr="\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>))" 
              and ?P'r="\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)"
              and ?P="\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2"
              and ?P'="\<lambda>z. evals (hd z) t c1 \<or> hd z < p" and ?t="t"]
          by blast+}
      then show "(\<And>p. 0 < recurs_release_real
                   (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)))
                   (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)) t 0 0 \<longrightarrow>
              recurs_release (\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2) (\<lambda>z. evals (hd z) t c1 \<or> hd z < p)
               t)" 
           "(\<And>p. recurs_release_real
               (\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)))
               (\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)) t 0 0
              < 0 \<longrightarrow>
              \<not> recurs_release (\<lambda>z. p + x \<le> hd z \<and> hd z \<le> p + y \<and> evals (hd z) t c2)
                  (\<lambda>z. evals (hd z) t c1 \<or> hd z < p) t)"
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
  then have "\<And>z. \<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)) 
        = Min_gamma_comp 0 (hd z - (p + x)) (Min_gamma_comp 0 (p + y - hd z) (robust (hd z) t c2 0))"
      "\<And>z. \<forall>\<gamma>\<le>0. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)
        = Max_gamma_comp 0 (robust (hd z) t c1 0) (p - hd z)"
    using Min_gamma_const_bel0 Min_gamma_comp_eq Max_gamma_const_bel0 Max_gamma_comp_eq
    by metis+
  then show ?case
    using robust.simps(4) recurs_release_real_const_bel0_const [where ?t="t"
      and ?P="\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>))"
      and ?P'="\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)" and ?E="0"]
    by presburger
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
    by blast+
  then show ?case
    using cAnd Min_gamma_chain_cont_0 [where ?f="robust p t c1" and ?g="robust p t c2"] Min_gamma_comp_eq 
    by fastforce
next
  case (cUntil x y c1 c2)
  {fix p :: real
    let ?P="\<lambda>z \<gamma>. Min_gamma_comp \<gamma> (hd z - (p + x)) (Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>))"
    let ?P'="\<lambda>z \<gamma>. Max_gamma_comp \<gamma> (robust (hd z) t c1 \<gamma>) (p - hd z)"
    {fix z :: "real list"
      have 1:"\<forall>\<gamma>\<le>0. robust (hd z) t c1 \<gamma> = robust (hd z) t c1 0"
          "\<forall>\<gamma>\<le>0. robust (hd z) t c2 \<gamma> = robust (hd z) t c2 0"
        using robust_const_bel0 recurs_release_real.simps robust.simps(4)
        by blast+
      then have 3:"isCont (?P' z) 0"
        using cUntil Max_gamma_chain_cont_0 [where ?f="robust (hd z) t c1" and ?g="\<lambda>\<gamma>. p - hd z"]
          Max_gamma_comp_eq 
        by fastforce
      then have 4:"\<forall>\<gamma>\<le>0. ?P' z \<gamma> = ?P' z 0"
        using Max_gamma_const_bel0 Max_gamma_comp_eq 1
        by presburger
      then have 5:"\<forall>\<gamma>\<le>0. ?P z \<gamma> = ?P z 0"
        using 1 Min_gamma_const_bel0 Min_gamma_comp_eq
        by presburger
      have 2:"isCont (\<lambda>\<gamma>. Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)) 0"
        using 1 cUntil Min_gamma_chain_cont_0 [where ?g="robust (hd z) t c2" and ?f="\<lambda>\<gamma>. p + y - hd z"]
          Min_gamma_comp_eq
        by fastforce
      have "\<forall>\<gamma>\<le>0. Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>) = Min_gamma_comp 0 (p + y - hd z) (robust (hd z) t c2 0)"
        using 1 Min_gamma_const_bel0 Min_gamma_comp_eq
        by presburger
      then have "isCont (?P z) 0" "isCont (?P' z) 0" "\<forall>\<gamma>\<le>0. ?P' z \<gamma> = ?P' z 0"
        using 2 cUntil Min_gamma_chain_cont_0 [where ?f="\<lambda>\<gamma>. hd z-(p+x)" and ?g="\<lambda>\<gamma>. Min_gamma_comp \<gamma> (p + y - hd z) (robust (hd z) t c2 \<gamma>)"]
          Min_gamma_comp_eq 3 4
        by fastforce+
      then have "isCont (?P z) 0" "isCont (?P' z) 0" "\<forall>\<gamma>\<le>0. ?P' z \<gamma> = ?P' z 0" "\<forall>\<gamma>\<le>0. ?P z \<gamma> = ?P z 0"
        using 5
        by blast+}
    then have "isCont (\<lambda>\<gamma>. recurs_release_real ?P ?P' t \<gamma> 0) 0"
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

definition evalsb :: "real \<Rightarrow> real list list list \<Rightarrow> real list constraint \<Rightarrow> bool list" where
"evalsb p T c = map (\<lambda>t. evals p t c) T"

definition robustb :: "real \<Rightarrow> real list list list \<Rightarrow> real list constraint \<Rightarrow> real \<Rightarrow> real list" where
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

fun constraintright :: "real list constraint \<Rightarrow> bool" where
"constraintright (cMu f ct r) = (f = Feval)"
| "constraintright (cNot c) = constraintright c"
| "constraintright (cAnd c1 c2) = (constraintright c1 \<and> constraintright c2)"
| "constraintright (cUntil x y c1 c2) = (constraintright c1 \<and> constraintright c2)"

(*
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
*)

(* Type constructors for code generation *)
definition mkGet :: "int \<Rightarrow> cterm" where
"mkGet n = Get n"

definition mkConst :: "real \<Rightarrow> cterm" where
"mkConst r = Const r"

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

definition mkOr :: "'v constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
  "mkOr c1 c2 = cOr c1 c2"

definition mkUntil :: "real \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
  "mkUntil x y c1 c2 = cUntil x y c1 c2"

definition mkEventually :: "real \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
  "mkEventually x y c = cEventually x y c"

definition mkAlways :: "real \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
  "mkAlways x y c = cAlways x y c"

export_code mkGet mkConst mkAdd mkMult mkUminus mkDivide mkMu mkNot mkAnd mkOr mkUntil mkEventually
  mkAlways evals robust Feval
  in OCaml
  module_name STLLoss

end
