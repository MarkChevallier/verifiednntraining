theory Max_Min

imports Complex_Main
  "HOL-Analysis.Analysis"
  "HOL-Library.Lub_Glb"

begin

(* definition of the max and min gamma functions *)
(* expanded definition to match original paper where \<gamma> can equal 0 *)

fun logsumexp :: "real \<Rightarrow> real \<Rightarrow> real" where
  "logsumexp a b = (if a < b then a + ln ((1::real) + exp (b - a)) else
  (if b < a then b + ln ((1::real) + exp (a - b)) else
  a + ln (2::real)))"
  
function Max_gamma_comp :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Max_gamma_comp \<gamma> a b = (if \<gamma> \<le> (0::real) then max a b
  else \<gamma> * (if (a/\<gamma>) < (b/\<gamma>) then (a/\<gamma>) + ln ((1::real) + exp ((b/\<gamma>) - (a/\<gamma>))) else
  (if (b/\<gamma>) < (a/\<gamma>) then (b/\<gamma>) + ln ((1::real) + exp ((a/\<gamma>) - (b/\<gamma>))) else
  (a/\<gamma>) + ln ((1::real)+(1::real)))))"
  by pat_completeness auto
termination by size_change

lemma Max_gamma_comp_equiv:"Max_gamma_comp \<gamma> a b = (if \<gamma> \<le> (0::real) then max a b
  else \<gamma> * (if (a/\<gamma>) < (b/\<gamma>) then (a/\<gamma>) + ln (1 + exp ((b/\<gamma>) - (a/\<gamma>))) else
  (if (b/\<gamma>) < (a/\<gamma>) then (b/\<gamma>) + ln (1 + exp ((a/\<gamma>) - (b/\<gamma>))) else
  (a/\<gamma>) + ln (2))))"
  by auto

function Min_gamma_comp :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Min_gamma_comp \<gamma> a b = (if \<gamma> \<le> (0::real) then min a b
  else -\<gamma> * (if (-a/\<gamma>) < (-b/\<gamma>) then (-a/\<gamma>) + ln ((1::real) + exp ((-b/\<gamma>) - (-a/\<gamma>))) else
  (if (-b/\<gamma>) < (-a/\<gamma>) then (-b/\<gamma>) + ln ((1::real) + exp ((-a/\<gamma>) - (-b/\<gamma>))) else
  (-a/\<gamma>) + ln ((1::real)+(1::real)))))"
  by pat_completeness auto
termination by size_change

lemma Min_gamma_comp_equiv:  "Min_gamma_comp \<gamma> a b = (if \<gamma> \<le> (0::real) then min a b
  else -\<gamma> * (if (-a/\<gamma>) < (-b/\<gamma>) then (-a/\<gamma>) + ln (1 + exp ((-b/\<gamma>) - (-a/\<gamma>))) else
  (if (-b/\<gamma>) < (-a/\<gamma>) then (-b/\<gamma>) + ln (1 + exp ((-a/\<gamma>) - (-b/\<gamma>))) else
  (-a/\<gamma>) + ln (2))))"
  by auto

fun Max_gamma :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Max_gamma \<gamma> a b = (if \<gamma> \<le> 0 then max a b 
    else \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>)))"

fun Min_gamma :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Min_gamma \<gamma> a b = (if \<gamma> \<le> 0 then min a b 
    else -\<gamma> * ln (exp (-a/\<gamma>) + exp (-b/\<gamma>)))"

lemma Max_gamma_comp_eq:"Max_gamma_comp \<gamma> a b = Max_gamma \<gamma> a b"
proof (cases "\<gamma>\<le>0")
  case True
  then show ?thesis 
  by simp
next
  case False
  then have 1:"Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>))" 
    by simp
  have 2:"exp (a/\<gamma>) > 0 \<and> (1 + exp ((b-a)/\<gamma>)) > 0 \<and>  (1 + exp ((a-b)/\<gamma>)) > 0 \<and> exp (b/\<gamma>) > 0"
    by (simp add: add_pos_nonneg)
  have 3:"Max_gamma_comp \<gamma> a b = \<gamma> * (if (a/\<gamma>) < (b/\<gamma>) then (a/\<gamma>) + ln (1 + exp ((b/\<gamma>) - (a/\<gamma>))) else
    (if (b/\<gamma>) < (a/\<gamma>) then (b/\<gamma>) + ln (1 + exp ((a/\<gamma>) - (b/\<gamma>))) else
    (a/\<gamma>) + ln 2))"
    using False by simp
  then show ?thesis
  proof (cases "(a/\<gamma>)<(b/\<gamma>)")
    case True
    then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) + exp (((b-a)+a)/\<gamma>))"
      using 1 by simp
    then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) + exp (a/\<gamma>) * exp ((b-a)/\<gamma>))"
      using add.commute add_divide_distrib mult_exp_exp by metis
    then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) * (1 + exp ((b-a)/\<gamma>)))"
      by (simp add: distrib_left)
    then have "Max_gamma \<gamma> a b = \<gamma> * ((a/\<gamma>) + ln (1 + exp ((b-a)/\<gamma>)))"
      using ln_mult 2 ln_exp by presburger
    then have 4:"Max_gamma \<gamma> a b = \<gamma> * ((a/\<gamma>) + ln (1 + exp ((b/\<gamma>)-(a/\<gamma>))))"
      by argo
    then have "Max_gamma_comp \<gamma> a b = \<gamma> * ((a/\<gamma>) + ln (1 + exp ((b/\<gamma>)-(a/\<gamma>))))"
      using True 3 by simp
    then show ?thesis
      using 4 by simp
  next
    case False
      then show ?thesis
      proof (cases "(b/\<gamma>)<(a/\<gamma>)")
        case True
      then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (((a-b)+b)/\<gamma>) + exp (b/\<gamma>))"
        using 1 by simp
      then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (b/\<gamma>) + exp (b/\<gamma>) * exp ((a-b)/\<gamma>))"
        using add.commute add_divide_distrib mult_exp_exp by metis
      then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (b/\<gamma>) * (1 + exp ((a-b)/\<gamma>)))"
        by (simp add: distrib_left)
      then have "Max_gamma \<gamma> a b = \<gamma> * ((b/\<gamma>) + ln (1 + exp ((a-b)/\<gamma>)))"
        using ln_mult 2 ln_exp by presburger
      then have 4:"Max_gamma \<gamma> a b = \<gamma> * ((b/\<gamma>) + ln (1 + exp ((a/\<gamma>)-(b/\<gamma>))))"
        by argo
      then have "Max_gamma_comp \<gamma> a b = \<gamma> * ((b/\<gamma>) + ln (1 + exp ((a/\<gamma>)-(b/\<gamma>))))"
        using True 3 by simp
      then show ?thesis
        using 4 by simp
    next
      case False
      then have 4:"(a/\<gamma>) = (b/\<gamma>)"
        using \<open>\<not>(a/\<gamma>)<(b/\<gamma>)\<close> by auto
      then have "Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) + exp (a/\<gamma>))"
        using 1 by presburger
      then have "Max_gamma \<gamma> a b = \<gamma> * ln (2 * exp (a/\<gamma>))"
        by simp
      then have 5:"Max_gamma \<gamma> a b = \<gamma> * (ln 2 + (a/\<gamma>))"
        using ln_mult 2 ln_exp by simp
      then have "Max_gamma_comp \<gamma> a b = \<gamma> * (ln 2 + (a/\<gamma>))"
        using 3 4 by auto
      then show ?thesis
        using 5 by simp
    qed
  qed
qed

lemma Min_gamma_comp_eq:"Min_gamma_comp \<gamma> a b = Min_gamma \<gamma> a b"
proof (cases "\<gamma>\<le>0")
  case True
  then show ?thesis 
    by simp
next
  case False
  then have 1:"Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a/\<gamma>) + exp (-b/\<gamma>))" 
    by simp
  have 2:"exp (-a/\<gamma>) > 0 \<and> (1 + exp (-(b-a)/\<gamma>)) > 0 \<and>  (1 + exp (-(a-b)/\<gamma>)) > 0 \<and> exp (-b/\<gamma>) > 0"
    by (simp add: add_pos_nonneg)
  have 3:"Min_gamma_comp \<gamma> a b = -\<gamma> * (if (-a/\<gamma>) < (-b/\<gamma>) then 
    (-a/\<gamma>) + ln (1 + exp ((-b/\<gamma>) - (-a/\<gamma>))) else
    (if (-b/\<gamma>) < (-a/\<gamma>) then (-b/\<gamma>) + ln (1 + exp ((-a/\<gamma>) - (-b/\<gamma>))) else
    (-a/\<gamma>) + ln 2))"
    using False by simp
  then show ?thesis
  proof (cases "(-a/\<gamma>)<(-b/\<gamma>)")
    case True
    then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a/\<gamma>) + exp (((-b+a)-a)/\<gamma>))"
      using 1 by simp
    then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a/\<gamma>) + exp (-a/\<gamma>) * exp ((-b+a)/\<gamma>))"
      using add.commute add_divide_distrib mult_exp_exp uminus_add_conv_diff by metis
    then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a/\<gamma>) * (1 + exp ((-b+a)/\<gamma>)))"
      by (simp add: distrib_left)
    then have "Min_gamma \<gamma> a b = -\<gamma> * ((-a/\<gamma>) + ln (1 + exp ((-b+a)/\<gamma>)))"
      using ln_mult 2 ln_exp by simp
    then have 4:"Min_gamma \<gamma> a b = -\<gamma> * ((-a/\<gamma>) + ln (1 + exp ((-b/\<gamma>)-(-a/\<gamma>))))"
      by argo
    then have "Min_gamma_comp \<gamma> a b = -\<gamma> * ((-a/\<gamma>) + ln (1 + exp ((-b/\<gamma>)-(-a/\<gamma>))))"
      using True 3 by simp
    then show ?thesis
      using 4 by simp
  next
    case False
      then show ?thesis
      proof (cases "(-b/\<gamma>)<(-a/\<gamma>)")
        case True
      then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (((-a+b)-b)/\<gamma>) + exp (-b/\<gamma>))"
        using 1 by simp
      then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (((-a+b)+(-b))/\<gamma>) + exp (-b/\<gamma>))"
        using 1 by simp
      then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-b/\<gamma>) + exp (-b/\<gamma>) * exp ((-a+b)/\<gamma>))"
        using add.commute add_divide_distrib mult_exp_exp by metis
      then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-b/\<gamma>) * (1 + exp ((-a+b)/\<gamma>)))"
        by (simp add: distrib_left)
      then have "Min_gamma \<gamma> a b = -\<gamma> * ((-b/\<gamma>) + ln (1 + exp ((-a+b)/\<gamma>)))"
        using ln_mult 2 ln_exp by simp
      then have 4:"Min_gamma \<gamma> a b = -\<gamma> * ((-b/\<gamma>) + ln (1 + exp ((-a/\<gamma>)-(-b/\<gamma>))))"
        by argo
      then have "Min_gamma_comp \<gamma> a b = -\<gamma> * ((-b/\<gamma>) + ln (1 + exp ((-a/\<gamma>)-(-b/\<gamma>))))"
        using True 3 by simp
      then show ?thesis
        using 4 by simp
    next
      case False
      then have 4:"(-a/\<gamma>) = (-b/\<gamma>)"
        using \<open>\<not>(-a/\<gamma>)<(-b/\<gamma>)\<close> by auto
      then have "Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a/\<gamma>) + exp (-a/\<gamma>))"
        using 1 by presburger
      then have "Min_gamma \<gamma> a b = -\<gamma> * ln (2 * exp (-a/\<gamma>))"
        by simp
      then have 5:"Min_gamma \<gamma> a b = -\<gamma> * (ln 2 + (-a/\<gamma>))"
        using ln_mult 2 ln_exp by simp
      then have "Min_gamma_comp \<gamma> a b = -\<gamma> * (ln 2 + (-a/\<gamma>))"
        using 3 4 by auto
      then show ?thesis
        using 5 by simp
    qed
  qed
qed

lemma Max_gamma_comm:
  fixes a::real and b::real
  shows "Max_gamma \<gamma> a b = Max_gamma \<gamma> b a"
proof (cases "\<gamma> \<le> 0")
  case True
  then show ?thesis by simp
next
  case False
  then have 1:"\<And>a b. Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>))" by simp
  then have "Max_gamma \<gamma> b a = \<gamma> * ln (exp (b/\<gamma>) + exp (a/\<gamma>))" by auto
  then show ?thesis using 1 add.commute by metis
qed

lemma Max_gamma_nn:
  fixes a b \<gamma> :: real
  assumes "a\<ge>0" "b\<ge>0" "\<gamma>>0"
  shows "Max_gamma (abs \<gamma>) a b \<ge> 0"
proof -
  have "\<not>\<gamma>\<le>0" using assms less_le_not_le by metis 
  then have "\<And>a b. Max_gamma \<gamma> a b = \<gamma> * ln (exp (a/\<gamma>) + exp (b/\<gamma>))" by simp
  then show ?thesis using assms Max_gamma_comm divide_nonneg_pos exp_gt_zero ln_ge_iff 
      mult_nonneg_nonneg
    by (smt (verit, ccfv_threshold) )
qed

lemma Min_gamma_comm:
  fixes a::real and b::real
  shows "Min_gamma \<gamma> a b = Min_gamma \<gamma> b a"
proof (cases "\<gamma> \<le> 0")
  case True
  then show ?thesis by simp
next
  case False
  then have 1:"\<And>a b. Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a/\<gamma>) + exp (-b/\<gamma>))" by simp
  then have "Min_gamma \<gamma> b a = -\<gamma> * ln (exp (-b/\<gamma>) + exp (-a/\<gamma>))" by auto
  then show ?thesis using 1 add.commute by metis
qed

lemma Max_gamma_works:
  fixes \<epsilon> :: real and a :: real and b :: real and \<gamma> :: real
  assumes eps_pos:"\<epsilon>>0"
      and gamma_pos:"\<gamma>>0"
      and gamma_less:"\<gamma><(\<epsilon>/ln 2)"
    shows "\<bar>Max_gamma \<gamma> a b - max a b\<bar> < \<epsilon>"
proof -
  obtain c::real and d::real where cd_defn:"c = max a b \<and> d = min a b" by simp
  have "(c = a \<and> d = b) \<or> (c = b \<and> d = a)" using cd_defn by auto
  then have 1:"Max_gamma \<gamma> a b = Max_gamma \<gamma> d c" using Max_gamma_comm by blast
  have 2:"\<And>x::real. exp x > 0" by simp
  have "d\<le>c" using cd_defn by simp
  then have 21:"exp (d/\<gamma>) \<le> exp (c/\<gamma>)" using gamma_pos divide_right_mono by fastforce
  then have 3:"exp (d/\<gamma>)/exp (c/\<gamma>) \<le> 1" by simp
  then have 31:"exp (d/\<gamma>)/exp (c/\<gamma>) > 0" by simp
  have "Max_gamma \<gamma> a b - c = \<gamma> * (ln (exp (d/\<gamma>) + exp (c/\<gamma>))) - c" using 1 gamma_pos by simp
  also have 4:"Max_gamma \<gamma> a b - c = \<gamma> * (ln ((exp (d/\<gamma>)/exp(c/\<gamma>))*exp(c/\<gamma>) + exp (c/\<gamma>))) - c" 
    using calculation by auto
  moreover have "Max_gamma \<gamma> a b - c \<le> \<gamma> * (ln (exp(c/\<gamma>) + exp (c/\<gamma>))) - c" using 3 
    by (smt calculation(2) divide_nonneg_nonneg gamma_pos ln_less_cancel_iff mult_left_le_one_le 
        nonzero_eq_divide_eq not_exp_le_zero ordered_comm_semiring_class.comm_mult_left_mono)
  moreover have "Max_gamma \<gamma> a b - c \<le> \<gamma> * (ln (2 * exp (c/\<gamma>))) - c" using calculation(3) by auto
  moreover have "Max_gamma \<gamma> a b - c \<le> \<gamma> * (ln 2 + ln (exp (c/\<gamma>))) - c" 
    using ln_mult 2 calculation(3) by auto
  moreover have "Max_gamma \<gamma> a b - c \<le> \<gamma> * ln 2 + \<gamma> * c/\<gamma> - c"
    using calculation(5) ln_exp 
         ring_class.ring_distribs(1)
    by (metis times_divide_eq_right)
  ultimately have 5:"Max_gamma \<gamma> a b - c \<le> \<gamma> * ln 2"
    using gamma_pos by auto
  have "Max_gamma \<gamma> a b - c > \<gamma> * (ln (exp (c/\<gamma>))) - c" using 31 4
    by (smt (verit, best) gamma_pos ln_less_cancel_iff mult_le_cancel_left_pos mult_pos_pos not_exp_le_zero)
  moreover have "Max_gamma \<gamma> a b - c > \<gamma> * c/\<gamma> - c" using calculation by auto
  ultimately have 6:"Max_gamma \<gamma> a b - c > 0" using gamma_pos by auto
  have "Max_gamma \<gamma> a b - max a b \<le> \<gamma> * ln 2 \<and> Max_gamma \<gamma> a b - max a b > 0" 
    using cd_defn 5 6 by simp
  then show ?thesis using gamma_less
    by (simp add: less_divide_eq)
qed

lemma Min_gamma_works:
  fixes \<epsilon> :: real and a :: real and b :: real and \<gamma> :: real
  assumes eps_pos:"\<epsilon>>0"
      and gamma_pos:"\<gamma>>0"
      and gamma_less:"\<gamma><(\<epsilon>/ln 2)"
    shows "\<bar>min a b - Min_gamma \<gamma> a b\<bar> < \<epsilon>"
proof -
  obtain c::real and d::real where cd_defn:"c = -max a b \<and> d = -min a b" by simp
  have "(c = -a \<and> d = -b) \<or> (c = -b \<and> d = -a)" using cd_defn by auto
  then have 1:"Min_gamma \<gamma> a b = Min_gamma \<gamma> (-d) (-c)" using Min_gamma_comm by fastforce
  have 2:"\<And>x::real. exp x > 0" by simp
  have "d\<ge>c" using cd_defn by simp
  then have 21:"exp (d/\<gamma>) \<ge> exp (c/\<gamma>)" using gamma_pos divide_right_mono 
    by fastforce
  then have 3:"exp (c/\<gamma>)/exp (d/\<gamma>) \<le> 1" by simp
  then have 31:"exp (c/\<gamma>)/exp (d/\<gamma>) > 0" by simp
  have "-Min_gamma \<gamma> a b - d = \<gamma> * (ln (exp (d/\<gamma>) + exp (c/\<gamma>))) - d" using 1 gamma_pos by simp
  also have 4:"-Min_gamma \<gamma> a b - d = \<gamma> * (ln (exp (d/\<gamma>) + exp(d/\<gamma>) * exp (c/\<gamma>)/exp (d/\<gamma>))) - d" 
    using calculation by auto
  moreover have "-Min_gamma \<gamma> a b - d \<le> \<gamma> * (ln (exp(d/\<gamma>) + exp (d/\<gamma>))) - d" using 3
    by (smt 21 calculation(1) gamma_pos ln_less_cancel_iff not_exp_le_zero 
        ordered_comm_semiring_class.comm_mult_left_mono)
  moreover have "-Min_gamma \<gamma> a b - d \<le> \<gamma> * (ln (2 * exp (d/\<gamma>))) - d" using calculation(3) by auto
  moreover have "-Min_gamma \<gamma> a b - d \<le> \<gamma> * (ln 2 + ln (exp (d/\<gamma>))) - d" 
    using ln_mult 2 calculation(3) by auto
  moreover have "-Min_gamma \<gamma> a b - d \<le> \<gamma> * ln 2 + \<gamma> * d/\<gamma> - d"
    using calculation(5) ln_exp 
         ring_class.ring_distribs(1)
    by (metis times_divide_eq_right)
  ultimately have 5:"-Min_gamma \<gamma> a b - d \<le> \<gamma> * ln 2"
    using gamma_pos by auto
  have "-Min_gamma \<gamma> a b - d > \<gamma> * (ln (exp (d/\<gamma>))) - d" using 31 4
    by (smt (verit, best) gamma_pos ln_less_cancel_iff mult_le_cancel_left_pos nonzero_mult_div_cancel_left not_exp_le_zero) 
  moreover have "-Min_gamma \<gamma> a b - d > \<gamma> * d/\<gamma> - d" using calculation by auto
  ultimately have 6:"-Min_gamma \<gamma> a b - d > 0" using gamma_pos by auto
  have "min a b - Min_gamma \<gamma> a b \<le> \<gamma> * ln 2 \<and> min a b - Min_gamma \<gamma> a b > 0" 
    using cd_defn 5 6 by simp
  then show ?thesis using gamma_less 
    by (smt gamma_pos less_divide_eq zero_less_mult_pos)
qed

lemma Max_gamma_lim:
  fixes a b :: real
  shows "(\<lambda>\<gamma>. Max_gamma \<gamma> a b) \<midarrow>0\<rightarrow> max a b"
proof -
  have "(\<forall>r>0. \<forall>x. x > 0 \<and> x < (r/ln 2) \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> a b) x - max a b\<bar> < r)"
    using Max_gamma_works by auto
  then have "(\<forall>r>0. \<exists>s>0. \<forall>x. x > 0 \<and> x < s \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> a b) x - max a b\<bar> < r)"
    by (metis (full_types) ln_gt_zero one_less_numeral_iff semiring_norm(76) zero_less_divide_iff)
  then have "\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> a b) x - max a b\<bar> < r"
    by force
  then have 1:"\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm ((\<lambda>\<gamma>. Max_gamma \<gamma> a b) x - (max a b)) < r"
    by simp
  {fix L :: real
    assume "max a b = L"
  then have "\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm ((\<lambda>\<gamma>. Max_gamma \<gamma> a b) x - L) < r"
    using 1 by simp
  then have "((\<lambda>\<gamma>. Max_gamma \<gamma> a b) \<midarrow>0\<rightarrow> L)"
    using LIM_eq by blast}
  {fix L :: real
    assume 2:"((\<lambda>\<gamma>. Max_gamma \<gamma> a b) \<midarrow>0\<rightarrow> L)"
    then have "((\<lambda>\<gamma>. Max_gamma \<gamma> a b) \<midarrow>0\<rightarrow> max a b)"
      using 1 LIM_eq by blast
    then have "max a b = L"
      using LIM_unique [where ?f="(\<lambda>\<gamma>. Max_gamma \<gamma> a b)"]  2 
      by blast}
  then have "\<And>L. (max a b = L) = ((\<lambda>\<gamma>. Max_gamma \<gamma> a b) \<midarrow>0\<rightarrow> L)"
    using \<open>\<And>L. max a b = L \<Longrightarrow> (\<lambda>\<gamma>. Max_gamma \<gamma> a b) \<midarrow>0 \<rightarrow> L\<close> 
    by blast
  then show ?thesis 
    by blast
qed

lemma Min_gamma_lim:
  fixes a b :: real
  shows "(\<lambda>\<gamma>. Min_gamma \<gamma> a b) \<midarrow>0\<rightarrow> min a b"
proof -
  have "(\<forall>r>0. \<forall>x. x > 0 \<and> x < (r/ln 2) \<longrightarrow> \<bar>(\<lambda>\<gamma>. Min_gamma \<gamma> a b) x - min a b\<bar> < r)"
    using Min_gamma_works by (simp add: abs_minus_commute)
  then have "(\<forall>r>0. \<exists>s>0. \<forall>x. x > 0 \<and> x < s \<longrightarrow> \<bar>(\<lambda>\<gamma>. Min_gamma \<gamma> a b) x - min a b\<bar> < r)"
    by (metis (full_types) ln_gt_zero one_less_numeral_iff semiring_norm(76) zero_less_divide_iff)
  then have "\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> \<bar>(\<lambda>\<gamma>. Min_gamma \<gamma> a b) x - min a b\<bar> < r"
    by force
  then have 1:"\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm ((\<lambda>\<gamma>. Min_gamma \<gamma> a b) x - (min a b)) < r"
    by simp
  {fix L :: real
    assume "min a b = L"
  then have "\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm ((\<lambda>\<gamma>. Min_gamma \<gamma> a b) x - L) < r"
    using 1 by simp
  then have "((\<lambda>\<gamma>. Min_gamma \<gamma> a b) \<midarrow>0\<rightarrow> L)"
    using LIM_eq by blast}
  {fix L :: real
    assume 2:"((\<lambda>\<gamma>. Min_gamma \<gamma> a b) \<midarrow>0\<rightarrow> L)"
    then have "((\<lambda>\<gamma>. Min_gamma \<gamma> a b) \<midarrow>0\<rightarrow> min a b)"
      using 1 LIM_eq by blast
    then have "min a b = L"
      using LIM_unique [where ?f="(\<lambda>\<gamma>. Min_gamma \<gamma> a b)"]  2 
      by blast}
  then have "\<And>L. ((\<lambda>\<gamma>. Min_gamma \<gamma> a b) \<midarrow>0\<rightarrow> L) = (min a b = L)"
    using \<open>\<And>L. min a b = L \<Longrightarrow> (\<lambda>\<gamma>. Min_gamma \<gamma> a b) \<midarrow>0 \<rightarrow> L\<close> 
    by blast
  then show ?thesis
    by blast
qed

lemma lim_chain:
  fixes f g :: "real\<Rightarrow>real" and a b :: real
  assumes "f \<midarrow>b\<rightarrow> L" "g \<midarrow>a\<rightarrow> b" "continuous_on UNIV f"
  shows "(f \<circ> g) \<midarrow>a\<rightarrow> L"
  using LIM_unique UNIV_I assms(1) assms(2) assms(3) 
    continuous_on_def filterlim_def tendsto_at_iff_tendsto_nhds tendsto_compose_filtermap 
    tendsto_mono
  by metis

lemma real_abs_div_continuous:
  fixes y :: real
  shows "continuous_on ((UNIV::real set)-{0}) (\<lambda>x. y/(abs x))"
proof -
  {fix x1 :: real
    assume "x1\<noteq>0"
    then have "isCont (\<lambda>x. y/(abs x)) x1" by auto}
  then have "\<forall>x1. x1\<notin>{0} \<longrightarrow> isCont (\<lambda>x. y/(abs x)) x1"
    by blast
  then show ?thesis 
    using continuous_at_imp_continuous_on 
    by blast
qed

lemma real_div_continuous:
  fixes y :: real
  shows "continuous_on ((UNIV::real set)-{0}) (\<lambda>x. y/x)"
proof -
  {fix x1 :: real
    assume "x1\<noteq>0"
    then have "isCont (\<lambda>x. y/x) x1" by auto}
  then have "\<forall>x1\<in>((UNIV::real set)-{0}). isCont (\<lambda>x. y/x) x1"
    by blast
  then show ?thesis 
    using continuous_at_imp_continuous_on 
    by blast
qed

lemma real_mult_continuous:
  fixes y :: real
  shows "continuous_on (UNIV::real set) (\<lambda>x. (abs x)*y)"
proof -
  {fix x1 :: real
    have "isCont (\<lambda>x. (abs x)*y) x1" by auto}
  then have "\<forall>x1. isCont (\<lambda>x. (abs x)*y) x1"
    by blast
  then show ?thesis 
    using continuous_at_imp_continuous_on 
    by blast
qed

lemma real_abs_continuous:
  shows "continuous_on (UNIV::real set) abs"
proof -
  {fix x :: real
    have "isCont abs x"
    proof (cases "x>0")
      case True
      then have "abs x = x" by fastforce
      then show "isCont abs x" 
        by simp
    next
      case False
      then have "abs x = -1 * x" by fastforce
      then show "isCont abs x"
        by simp
    qed}
  then show ?thesis
    using continuous_on_eq_continuous_at
    by blast
qed

lemma max_continuous:
  shows "continuous_on (UNIV::real set) max"
proof -
  {fix a :: real
    have "continuous_on UNIV (\<lambda>b. max a b)" 
    proof -
      have 0:"{a..}\<union>{..a} = UNIV"
        by auto
      have 1:"continuous_on {a..} (\<lambda>b. if b \<ge> a then b else a)"
        using continuous_on_topological by fastforce
      have "continuous_on {..a} (\<lambda>b. if b \<ge> a then b else a)"
        using UNIV_I atMost_iff open_UNIV continuous_on_topological
        by (smt (verit, del_insts))
      then have "continuous_on UNIV (\<lambda>b. if b \<ge> a then b else a)"
        using 0 1 closed_atLeast closed_atMost continuous_on_closed_Un
        by (metis (no_types, lifting))
      then show ?thesis 
        by (smt (z3))
    qed}
  {fix b :: real
    have "continuous_on UNIV (\<lambda>a. max a b)"
      by (meson \<open>\<And>a. continuous_on UNIV (max a)\<close> continuous_on_eq max.commute)}
  then show ?thesis
    using continuous_on_coordinatewise_then_product 
    by blast
qed

lemma Max_gamma_continuous_gamma:
  fixes a b :: real
  shows "continuous_on UNIV (\<lambda>x. Max_gamma x a b)"
proof -
  have 0:"{0::real..}\<union>{..0} = UNIV"
    by auto
  have 1:"\<forall>x\<in>{x. x>0}. exp (a/x) + exp(b/x) \<noteq> 0"
    using add_pos_pos exp_gt_zero less_numeral_extra(3)
    by metis
  have 2:"\<And>\<gamma>. \<gamma>\<in>({x. x>0}) \<Longrightarrow> Max_gamma \<gamma> a b = \<gamma> * ln (exp (a /\<gamma>) + exp (b /\<gamma>))"
    by auto
  have 3:"open ((UNIV::real set)-{0})"
    by auto
  have 4:"open {x::real. x>0}"
    using equalityI greaterThan_iff mem_Collect_eq open_greaterThan subsetI
    by metis
  have "\<And>y::real. continuous_on {x. x>0} (\<lambda>x. exp (y/x))"
  proof -
    have "{x::real. x>0} \<subseteq> (UNIV-{0})" 
      by blast
    then show "\<And>y::real. continuous_on {x. x>0} (\<lambda>x. exp (y/x))"
      using real_div_continuous continuous_on_exp continuous_on_subset
      by blast
  qed
  then have "continuous_on {x. x>0} (\<lambda>x. exp (a/x) + exp(b/x))"
    using continuous_on_add 
    by blast
  then have 5:"continuous_on {x. x>0} (\<lambda>x. ln (exp (a/x) + exp(b/x)))"
    using continuous_on_ln 1 
    by blast
  then have "continuous_on {x. x>0} (\<lambda>x. x * ln (exp (a/x) + exp(b/x)))"
    using continuous_on_id continuous_on_mult 
    by blast
  then have 6:"continuous_on {x. x>0} (\<lambda>x. Max_gamma x a b)"
    using 4 2 continuous_on_cong
    by (metis (no_types, lifting))
  have 7:"\<forall>x\<in>{..0}. Max_gamma x a b = max a b"
    by simp
  then have "continuous_on {..0} (\<lambda>x. max a b)"
    using continuous_on_const 
    by blast
  then have 8:"continuous_on {..0} (\<lambda>x. Max_gamma x a b)"
    using continuous_on_cong 7 
    by metis
  have "(\<lambda>x. Max_gamma x a b) \<midarrow>0\<rightarrow> max a b"
    using Max_gamma_lim by blast
  then have "isCont (\<lambda>x. Max_gamma x a b) 0"
    using 7 isCont_def 
    by fastforce
  then have "continuous_on {0..} (\<lambda>x. Max_gamma x a b)"
    using 6 4 continuous_at_imp_continuous_on continuous_on_eq_continuous_at mem_Collect_eq 
      atLeast_iff
    by (smt (verit, ccfv_SIG))
  then show ?thesis
    using 0 8 continuous_on_closed_Un closed_atLeast closed_atMost
    by metis
qed

lemma Min_gamma_continuous_gamma:
  fixes a b :: real
  shows "continuous_on UNIV (\<lambda>x. Min_gamma x a b)"
proof -
  have 0:"{0::real..}\<union>{..0} = UNIV"
    by auto
  have 1:"\<forall>x\<in>{x. x>0}. exp (-a/x) + exp(-b/x) \<noteq> 0"
    using add_pos_pos exp_gt_zero less_numeral_extra(3)
    by metis
  have 2:"\<And>\<gamma>. \<gamma>\<in>({x. x>0}) \<Longrightarrow> Min_gamma \<gamma> a b = -\<gamma> * ln (exp (-a /\<gamma>) + exp (-b /\<gamma>))"
    by auto
  have 3:"open ((UNIV::real set)-{0})"
    by auto
  have 4:"open {x::real. x>0}"
    using equalityI greaterThan_iff mem_Collect_eq open_greaterThan subsetI
    by metis
  have "\<And>y::real. continuous_on {x. x>0} (\<lambda>x. exp (-y/x))"
  proof -
    have "{x::real. x>0} \<subseteq> (UNIV-{0})" 
      by blast
    then show "\<And>y::real. continuous_on {x. x>0} (\<lambda>x. exp (-y/x))"
      using real_div_continuous continuous_on_exp continuous_on_subset
      by blast
  qed
  then have "continuous_on {x. x>0} (\<lambda>x. exp (-a/x) + exp(-b/x))"
    using continuous_on_add 
    by blast
  then have 5:"continuous_on {x. x>0} (\<lambda>x. ln (exp (-a/x) + exp(-b/x)))"
    using continuous_on_ln 1 
    by blast
  then have "continuous_on {x. x>0} (\<lambda>x. -x * ln (exp (-a/x) + exp(-b/x)))"
    using continuous_on_id continuous_on_mult continuous_on_minus
    by blast
  then have 6:"continuous_on {x. x>0} (\<lambda>x. Min_gamma x a b)"
    using 4 2 continuous_on_cong
    by (metis (no_types, lifting))
  have 7:"\<forall>x\<in>{..0}. Min_gamma x a b = min a b"
    by simp
  then have "continuous_on {..0} (\<lambda>x. min a b)"
    using continuous_on_const 
    by blast
  then have 8:"continuous_on {..0} (\<lambda>x. Min_gamma x a b)"
    using continuous_on_cong 7 
    by metis
  have "(\<lambda>x. Min_gamma x a b) \<midarrow>0\<rightarrow> min a b"
    using Min_gamma_lim by blast
  then have "isCont (\<lambda>x. Min_gamma x a b) 0"
    using 7 isCont_def 
    by fastforce
  then have "continuous_on {0..} (\<lambda>x. Min_gamma x a b)"
    using 6 4 continuous_at_imp_continuous_on continuous_on_eq_continuous_at mem_Collect_eq 
      atLeast_iff
    by (smt (verit, ccfv_SIG))
  then show ?thesis
    using 0 8 continuous_on_closed_Un closed_atLeast closed_atMost
    by metis
qed

lemma DERIV_fun_ln: "\<lbrakk> DERIV g (x::real) :> m; g x > 0 \<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. ln (g x)) x :>  m/g x"
  by (simp add: DERIV_chain2 DERIV_ln divide_inverse_commute)

fun dAbs_a_minus_b_da :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dAbs_a_minus_b_da a b = (if a=b then (a-a) else (a-b)/(abs (a-b)))"

lemma dAbs_a_minus_b_da_equiv:"dAbs_a_minus_b_da a b = (if a=b then 0 else (a-b)/(abs (a-b)))" by simp

fun dAbs_a_minus_b_db :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dAbs_a_minus_b_db a b = (if a=b then (a-a) else (b-a)/(abs (a-b)))"

lemma dAbs_a_minus_b_db_equiv:"dAbs_a_minus_b_db a b = (if a=b then 0 else (b-a)/(abs (a-b)))" by simp

(* Max_gamma derivative *)

fun dMax_da :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dMax_da a b = (1::real)/((1::real)+(1::real))*((1::real) + (dAbs_a_minus_b_da a b))"

fun dMax_db :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dMax_db a b = (1::real)/((1::real)+(1::real))*((1::real) + (dAbs_a_minus_b_db a b))"

fun dMax_gamma_da :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMax_gamma_da \<gamma> a b = (if \<gamma> \<le> (0::real) then dMax_da a b 
    else exp(a/\<gamma>)/(exp (a/\<gamma>) + exp (b/\<gamma>)))"

theorem max_gamma2_deriv_wrt_a:
  fixes x \<gamma> b :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "((\<lambda>y. Max_gamma \<gamma> y b) has_field_derivative dMax_gamma_da \<gamma> x b) (at x)"
proof -
  have "((\<lambda>y. exp(y/\<gamma>)) has_field_derivative (1/\<gamma>)*exp(x/\<gamma>)) (at x)"
    using DERIV_fun_exp [where g="\<lambda>y. y/\<gamma>" and m="1/\<gamma>"] by (simp add: DERIV_cdivide)
  moreover have "((\<lambda>y. exp(b/\<gamma>)) has_field_derivative 0) (at x)" by simp
  ultimately have sum_exp_diff: "((\<lambda>y. exp(y/\<gamma>) + exp(b/\<gamma>)) has_field_derivative (1/\<gamma>)*exp(x/\<gamma>)) (at x)"
    using DERIV_add by fastforce
  have "exp(x/\<gamma>) + exp(b/\<gamma>) > 0" by (simp add: pos_add_strict)
  hence "(ln has_real_derivative 1 / (exp(x/\<gamma>) + exp(b/\<gamma>))) (at (exp(x/\<gamma>) + exp(b/\<gamma>)))" using DERIV_ln_divide by simp
  from this and sum_exp_diff have "(ln \<circ> (\<lambda>y. exp(y/\<gamma>) + exp(b/\<gamma>)) has_field_derivative (exp(x/\<gamma>)/(\<gamma>*(exp(x/\<gamma>) + exp(b/\<gamma>))))) (at x)"
    using DERIV_chain by fastforce
  hence "((\<lambda>y. ln (exp(y/\<gamma>) + exp(b/\<gamma>))) has_field_derivative (exp(x/\<gamma>)/(\<gamma>*(exp(x/\<gamma>) + exp(b/\<gamma>))))) (at x)" by (simp add: o_def)
  hence "((\<lambda>y. \<gamma> * ln (exp(y/\<gamma>) + exp(b/\<gamma>))) has_field_derivative \<gamma>*(exp(x/\<gamma>)/(\<gamma>*(exp(x/\<gamma>) + exp(b/\<gamma>))))) (at x)" using DERIV_cmult by blast
  hence "((\<lambda>y. \<gamma> * ln (exp(y/\<gamma>) + exp(b/\<gamma>))) has_field_derivative (exp(x/\<gamma>)/(exp(x/\<gamma>) + exp(b/\<gamma>)))) (at x)" using gamma_gt_zero by force
  thus ?thesis using gamma_gt_zero by auto
qed

fun dMax_gamma_db :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMax_gamma_db \<gamma> a b = (if \<gamma> \<le> (0::real) then dMax_db a b 
    else exp(b/\<gamma>)/(exp (a/\<gamma>) + exp (b/\<gamma>)))"

lemma Max_gamma_swap_indices:
  fixes \<gamma> c :: real
  shows "(\<lambda>y. Max_gamma \<gamma> c y) = (\<lambda>y. Max_gamma \<gamma> y c)"
  using Max_gamma_comm by auto

lemma dMax_gamma_swap_indices:
  fixes \<gamma> x c :: real
  assumes "\<gamma>>0"
  shows "dMax_gamma_da \<gamma> x c = dMax_gamma_db \<gamma> c x"
  using assms by auto

theorem max_gamma2_deriv_wrt_b:
  fixes x \<gamma> a :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "((\<lambda>y. Max_gamma \<gamma> a y) has_field_derivative dMax_gamma_db \<gamma> a x) (at x)"
using assms Max_gamma_swap_indices dMax_gamma_swap_indices by (metis max_gamma2_deriv_wrt_a)

fun dMax_gamma_ds :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMax_gamma_ds \<gamma> a da b db = (dMax_gamma_da \<gamma> a b) * da + (dMax_gamma_db \<gamma> a b) * db"

(* Min_gamma derivative *)

fun dMin_da :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dMin_da a b = (1::real)/((1::real)+(1::real))*((1::real) - (dAbs_a_minus_b_da a b))"

fun dMin_db :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dMin_db a b = (1::real)/((1::real)+(1::real))*((1::real) - (dAbs_a_minus_b_db a b))"

fun dMin_gamma_da :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMin_gamma_da \<gamma> a b = (if \<gamma> \<le> (0::real) then dMin_da a b 
    else exp(-a/\<gamma>)/(exp (-a/\<gamma>) + exp (-b/\<gamma>)))"

lemma Min_gamma_as_max:
  fixes \<gamma> a b :: real
  shows "Min_gamma \<gamma> a b = (-1) * Max_gamma \<gamma> (-a) (-b)"
  by force
  
lemma dMin_gamma_da_as_dMax:
  fixes \<gamma> a b :: real
  assumes "\<gamma>>0"
  shows "dMin_gamma_da \<gamma> a b = dMax_gamma_da \<gamma> (-a) (-b)"
  using assms by auto


theorem min_gamma2_deriv_wrt_a:
  fixes x \<gamma> b :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "((\<lambda>y. Min_gamma \<gamma> y b) has_field_derivative dMin_gamma_da \<gamma> x b) (at x)"
proof -
  from assms have "((\<lambda>y. Max_gamma \<gamma> y (-b)) has_field_derivative dMax_gamma_da \<gamma> (-x) (-b)) (at (-x))"
    using max_gamma2_deriv_wrt_a by blast
  moreover have "((\<lambda>y. -y) has_field_derivative (-1)) (at x)" using DERIV_minus DERIV_ident by blast
  ultimately have "((\<lambda>y. Max_gamma \<gamma> y (-b))\<circ>(\<lambda>y. -y) has_field_derivative (-1) * dMax_gamma_da \<gamma> (-x) (-b)) (at x)"
    using DERIV_chain by fastforce
  hence "((\<lambda>y. Max_gamma \<gamma> (-y) (-b)) has_field_derivative (-1) * dMax_gamma_da \<gamma> (-x) (-b)) (at x)"
    by (simp add: o_def)
  hence "((\<lambda>y. (-1) * Max_gamma \<gamma> (-y) (-b)) has_field_derivative dMax_gamma_da \<gamma> (-x) (-b)) (at x)"
    using DERIV_cmult [where c="-1" and f="(\<lambda>y. Max_gamma \<gamma> (-y) (-b))"] by fastforce
  thus ?thesis using gamma_gt_zero Min_gamma_as_max dMin_gamma_da_as_dMax by simp
qed

fun dMin_gamma_db :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMin_gamma_db \<gamma> a b = (if \<gamma> \<le> (0::real) then dMin_db a b 
    else exp(-b/\<gamma>)/(exp (-a/\<gamma>) + exp (-b/\<gamma>)))"

lemma dMin_gamma_db_as_dMax:
  fixes \<gamma> a b :: real
  assumes "\<gamma>>0"
  shows "dMin_gamma_db \<gamma> a b = dMax_gamma_db \<gamma> (-a) (-b)"
  using assms by auto

lemma Min_gamma_swap_indices:
  fixes \<gamma> c :: real
  shows "(\<lambda>y. Min_gamma \<gamma> c y) = (\<lambda>y. Min_gamma \<gamma> y c)"
  using Min_gamma_comm by auto

lemma dMin_gamma_swap_indices:
  fixes \<gamma> x c :: real
  assumes "\<gamma>>0"
  shows "dMin_gamma_da \<gamma> x c = dMin_gamma_db \<gamma> c x"
  using assms by auto

theorem min_gamma2_deriv_wrt_b:
  fixes x \<gamma> a :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "((\<lambda>y. Min_gamma \<gamma> a y) has_field_derivative dMin_gamma_db \<gamma> a x) (at x)"
using assms Min_gamma_swap_indices dMin_gamma_swap_indices by (metis min_gamma2_deriv_wrt_a)


fun dMin_gamma_ds :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMin_gamma_ds \<gamma> a da b db = (dMin_gamma_da \<gamma> a b) * da + (dMin_gamma_db \<gamma> a b) * db"

theorem dMax_gamma_chain:
  fixes f g :: "real \<Rightarrow> real" and Df Dg \<gamma> :: real
  assumes "\<gamma> > 0"
  and "(f has_real_derivative Df) (at x)"
and "(g has_real_derivative Dg) (at x)"
shows "((\<lambda>y. (Max_gamma_comp \<gamma> (f y) (g y))) has_real_derivative (dMax_gamma_ds \<gamma> (f x) Df (g x) Dg)) (at x)"
proof -
  have "((\<lambda>x. exp (f x / \<gamma>)) has_real_derivative exp (f x / \<gamma>) * Df / \<gamma>) (at x)"
    using assms  DERIV_fun_exp [OF DERIV_divide, of f Df x "\<lambda>x. \<gamma>" 0]
    by simp
  moreover have "((\<lambda>x. exp (g x / \<gamma>)) has_real_derivative exp (g x / \<gamma>) * Dg / \<gamma>) (at x)"
    using assms DERIV_fun_exp [OF DERIV_divide, of g Dg x "\<lambda>x. \<gamma>" 0]
    by simp
  ultimately have "((\<lambda>y. ln (exp (f y / \<gamma>) + exp (g y / \<gamma>))) has_real_derivative
     (exp (f x / \<gamma>) * Df/\<gamma> + exp (g x / \<gamma>) * Dg/\<gamma>) / (exp (f x / \<gamma>) + exp (g x / \<gamma>))) (at x)"
    by (auto intro!: DERIV_fun_ln DERIV_add simp add: add_pos_pos)
  then have "((\<lambda>y. \<gamma> * ln (exp (f y / \<gamma>) + exp (g y / \<gamma>))) has_real_derivative
     \<gamma> * (exp (f x / \<gamma>) * Df/\<gamma> + exp (g x / \<gamma>) * Dg/\<gamma>) / (exp (f x / \<gamma>) + exp (g x / \<gamma>))) (at x)"
    using DERIV_cmult by fastforce
  then have "((\<lambda>y. \<gamma> * ln (exp (f y / \<gamma>) + exp (g y / \<gamma>))) has_real_derivative
     (exp (f x / \<gamma>) * Df + exp (g x / \<gamma>) * Dg) / (exp (f x / \<gamma>) + exp (g x / \<gamma>))) (at x)"
    using assms(1) 
    by (metis (no_types, lifting) add_divide_distrib less_irrefl nonzero_mult_div_cancel_left times_divide_eq_right)
  then show ?thesis unfolding Max_gamma_comp_eq using assms(1) by (simp add: add_divide_distrib)
qed

theorem dMin_gamma_chain:
  fixes f g :: "real \<Rightarrow> real" and Df Dg \<gamma> x :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  and f_deriv: "(f has_real_derivative Df) (at x)"
and g_deriv: "(g has_real_derivative Dg) (at x)"
shows "((\<lambda>y. (Min_gamma_comp \<gamma> (f y) (g y))) has_real_derivative (dMin_gamma_ds \<gamma> (f x) Df (g x) Dg)) (at x)"
proof -
  let ?n_f = "(\<lambda>y. (-1) * f y)"
  let ?n_g = "(\<lambda>y. (-1) * g y)"
  from f_deriv have "(?n_f has_real_derivative (-1)*Df) (at x)" using DERIV_cmult by blast
  moreover from g_deriv have "(?n_g has_real_derivative (-1)*Dg) (at x)" using DERIV_cmult by blast
  ultimately have deriv: "((\<lambda>y. (Max_gamma_comp \<gamma> (?n_f y) (?n_g y))) has_real_derivative
  (dMax_gamma_ds \<gamma> (?n_f x) (-Df) (?n_g x) (-Dg))) (at x)" using gamma_gt_zero dMax_gamma_chain by fastforce
  have "(\<lambda>y. (Min_gamma_comp \<gamma> (f y) (g y))) = (\<lambda>y. (-1)*(Max_gamma_comp \<gamma> (?n_f y) (?n_g y)))"
    using Max_gamma_comp_eq Min_gamma_comp_eq by force
  from this and deriv have "((\<lambda>y. (Min_gamma_comp \<gamma> (f y) (g y))) has_real_derivative
  (-1)*(dMax_gamma_ds \<gamma> (?n_f x) (-Df) (?n_g x) (-Dg))) (at x)" 
    using Deriv.field_differentiable_minus by fastforce
  moreover have "(-1)*(dMax_gamma_ds \<gamma> (?n_f x) (-Df) (?n_g x) (-Dg)) 
= (-1)*((dMax_gamma_da \<gamma> (?n_f x) (?n_g x))*(-Df) + (dMax_gamma_db \<gamma> (?n_f x) (?n_g x))*(-Dg))" by simp
  hence "(-1)*(dMax_gamma_ds \<gamma> (?n_f x) (-Df) (?n_g x) (-Dg)) 
= (dMin_gamma_ds \<gamma> (f x) Df (g x) Dg)"
    using dMin_gamma_db_as_dMax dMin_gamma_da_as_dMax gamma_gt_zero by fastforce 
  ultimately show  ?thesis using DERIV_cong by simp
qed

lemma min_continuous:
  shows "continuous_on (UNIV::real set) min"
proof -
  {fix a :: real
    have "continuous_on UNIV (\<lambda>b. min a b)" 
    proof -
      have 0:"{a..}\<union>{..a} = UNIV"
        by auto 
      have 1:"continuous_on {..a} (\<lambda>b. if a \<le> b then a else b)"
        using continuous_on_topological atMost_iff
        by (smt (verit) verit_la_disequality)
      have "continuous_on {a..} (\<lambda>b. if a \<le> b then a else b)"
        using UNIV_I open_UNIV continuous_on_topological atLeast_iff
        by (smt (verit, best))
      then have "continuous_on UNIV (\<lambda>b. if a \<le> b then a else b)"
        using 0 1 closed_atLeast closed_atMost continuous_on_closed_Un
        by (metis (no_types, lifting))
      then show ?thesis 
        by (smt (z3))
    qed}
  {fix b :: real
    have "continuous_on UNIV (\<lambda>a. min a b)"
      by (meson \<open>\<And>a. continuous_on UNIV (min a)\<close> continuous_on_eq min.commute)}
  then show ?thesis
    using continuous_on_coordinatewise_then_product 
    by blast
qed

lemma Max_gamma_continuous_a:
  fixes \<gamma> b :: real
  shows "continuous_on UNIV (\<lambda>y. Max_gamma \<gamma> y b)"
proof (cases "\<gamma>>0")
  case True
  then show ?thesis
    using max_gamma2_deriv_wrt_a DERIV_continuous continuous_on_eq_continuous_within
    by metis
next
  case False
  then have "(\<lambda>y. Max_gamma \<gamma> y b) = (\<lambda>y. max y b)"
    by simp
  then show ?thesis 
    using max_continuous continuous_on_product_then_coordinatewise_UNIV
    by metis
qed

lemma Max_gamma_continuous_b:
  fixes \<gamma> a :: real
  shows "continuous_on UNIV (\<lambda>y. Max_gamma \<gamma> a y)"
proof (cases "\<gamma>>0")
  case True
  then show ?thesis
    using max_gamma2_deriv_wrt_b DERIV_continuous_on
    by metis
next
  case False
  then have "(\<lambda>y. Max_gamma \<gamma> a y) = (\<lambda>y. max a y)"
    by simp
  then show ?thesis 
    using max_continuous continuous_on_product_then_coordinatewise_UNIV continuous_on_cong
    by (smt (verit, best))
qed

lemma Max_gamma_continuous_ab:
  fixes \<gamma> :: real
  shows "continuous_on UNIV (\<lambda>x y. Max_gamma \<gamma> x y)"
  using Max_gamma_continuous_a Max_gamma_continuous_b continuous_on_coordinatewise_then_product
  by metis

lemma Max_gamma_continuous:"continuous_on UNIV Max_gamma"
  using Max_gamma_continuous_ab Max_gamma_continuous_gamma 
    continuous_on_coordinatewise_then_product 
  by metis

lemma Min_gamma_continuous_a:
  fixes \<gamma> b :: real
  shows "continuous_on UNIV (\<lambda>y. Min_gamma \<gamma> y b)"
proof (cases "\<gamma>>0")
  case True
  then show ?thesis
    using min_gamma2_deriv_wrt_a DERIV_continuous continuous_on_eq_continuous_within
    by metis
next
  case False
  then have "(\<lambda>y. Min_gamma \<gamma> y b) = (\<lambda>y. min y b)"
    by simp
  then show ?thesis 
    using min_continuous continuous_on_product_then_coordinatewise_UNIV
    by metis
qed

lemma Min_gamma_continuous_b:
  fixes \<gamma> a :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "continuous_on UNIV (\<lambda>y. Min_gamma \<gamma> a y)"
  using assms min_gamma2_deriv_wrt_b DERIV_continuous_on
  by metis

lemma Min_gamma_continuous_ab:
  fixes \<gamma> :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "continuous_on UNIV (\<lambda>x y. Min_gamma \<gamma> x y)"
  using Min_gamma_continuous_a Min_gamma_continuous_b
  using assms continuous_on_coordinatewise_then_product
  by metis

lemma Min_gamma_continuous:"continuous_on UNIV (\<lambda>\<gamma> x y. Min_gamma \<gamma> x y)"
  using Min_gamma_continuous_ab Min_gamma_continuous_gamma 
    continuous_on_coordinatewise_then_product
  by metis

lemma Max_gamma_works_chain:
  fixes \<epsilon> \<gamma> s :: real and f g :: "real \<Rightarrow> real"
  assumes "f \<midarrow>0\<rightarrow> L" "g \<midarrow>0\<rightarrow> M" "0<\<epsilon>" "0<\<gamma>" 
    "s = (SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm (max (f x) (g x) - max L M) < \<epsilon>/2))"
    "\<gamma> < min (\<epsilon>/(2 * ln 2)) s"
  shows "\<bar>Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max L M\<bar> < \<epsilon>"
proof -
  fix s2 :: real
  have eps_pos2:"\<epsilon>/2>0" using assms by simp
  then have eps_pos22:"\<epsilon>/(2 * ln 2)>0" by simp
  have "(\<lambda>\<gamma>. max (f \<gamma>) (g \<gamma>)) \<midarrow>0\<rightarrow> max L M"
    using tendsto_max assms(1) assms(2) 
    by blast
  then have max_lim:"\<exists>s. s \<in> {s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm (max (f x) (g x) - max L M) < \<epsilon>/2)}"
    using eps_pos2 LIM_eq [where ?f="\<lambda>\<gamma>. max (f \<gamma>) (g \<gamma>)" and ?a="0" and ?L="max L M"] 
    by blast
  then have s_defn:"\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm (max (f x) (g x) - max L M) < \<epsilon>/2"
    using assms(5)
    by (metis (mono_tags, lifting) mem_Collect_eq someI)
  have s2_less2:"\<gamma> < (\<epsilon>/(2 * ln 2))" using assms by simp
  obtain c::real and d::real where cd_defn:"c = max (f \<gamma>) (g \<gamma>) \<and> d = min (f \<gamma>) (g \<gamma>)" by simp
  have "(c = (f \<gamma>) \<and> d = (g \<gamma>)) \<or> (c = (g \<gamma>) \<and> d = (f \<gamma>))" using cd_defn by auto
  then have 1:"Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) = Max_gamma \<gamma> d c" using Max_gamma_comm by blast
  have 2:"\<And>x::real. exp x > 0" by simp
  have "d\<le>c" using cd_defn by simp
  then have 21:"exp (d/\<gamma>) \<le> exp (c/\<gamma>)" using assms  divide_right_mono by fastforce
  then have 3:"exp (d/\<gamma>)/exp (c/\<gamma>) \<le> 1" by simp
  then have 31:"exp (d/\<gamma>)/exp (c/\<gamma>) > 0" by simp
  have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c = \<gamma> * (ln (exp (d/\<gamma>) + exp (c/\<gamma>))) - c" using 1  assms by simp
  also have 4:"Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c = \<gamma> * (ln ((exp (d/\<gamma>)/exp(c/\<gamma>))*exp(c/\<gamma>) + exp (c/\<gamma>))) - c" 
    using calculation by auto
  moreover have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c \<le> \<gamma> * (ln (exp(c/\<gamma>) + exp (c/\<gamma>))) - c" using 3 
    by (smt calculation(2) divide_nonneg_nonneg  ln_less_cancel_iff mult_left_le_one_le 
        nonzero_eq_divide_eq not_exp_le_zero ordered_comm_semiring_class.comm_mult_left_mono assms)
  moreover have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c \<le> \<gamma> * (ln (2 * exp (c/\<gamma>))) - c" using calculation(3) by auto
  moreover have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c \<le> \<gamma> * (ln 2 + ln (exp (c/\<gamma>))) - c" 
    using ln_mult 2 calculation(3) by auto
  moreover have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c \<le> \<gamma> * ln 2 + \<gamma> * c/\<gamma> - c" 
    using  calculation(5) div_by_1 divide_divide_eq_right ln_exp 
        mult.left_neutral ring_class.ring_distribs(1)
    by (metis (no_types, opaque_lifting))
  ultimately have 5:"Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c \<le> \<gamma> * ln 2"
    using  assms by auto
  have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c > \<gamma> * (ln (exp (c/\<gamma>))) - c" using 31 4
    by (smt (verit, best)  ln_less_cancel_iff mult_le_cancel_left_pos mult_pos_pos not_exp_le_zero assms)
  moreover have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c > \<gamma> * c/\<gamma> - c" using calculation by auto
  ultimately have 6:"Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - c > 0" using  assms by auto
  have "Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max (f \<gamma>) (g \<gamma>) \<le> \<gamma> * ln 2 \<and> Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max (f \<gamma>) (g \<gamma>) > 0" 
    using cd_defn 5 6 by simp
  then have 7:"\<bar>Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max (f \<gamma>) (g \<gamma>)\<bar> \<le> \<epsilon>/2"
    using s2_less2
    by (simp add: less_divide_eq)
  then have "\<gamma> < s"
    using  assms 
    by argo
  then have "\<gamma>>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) \<le> \<gamma> \<longrightarrow> (norm (max (f x) (g x) - max L M) < \<epsilon>/2))"
    using assms s_defn
    by simp
  then have "norm (max (f \<gamma>) (g \<gamma>) - max L M) < \<epsilon>/2"
    by auto
  then have fineq:"norm (max (f \<gamma>) (g \<gamma>) - max L M) < \<epsilon>/2
    \<and> norm (Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max (f \<gamma>) (g \<gamma>)) \<le> \<epsilon>/2"
    using 7 by simp
  then have "\<bar>Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max L M\<bar> \<le> \<bar>max (f \<gamma>) (g \<gamma>) - max L M\<bar>
      + \<bar>Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max (f \<gamma>) (g \<gamma>)\<bar>"
    by argo
  then show "\<bar>Max_gamma \<gamma> (f \<gamma>) (g \<gamma>) - max L M\<bar> < \<epsilon>"
    using fineq
    by auto
qed

lemma Max_gamma_works_chain2:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<midarrow>0\<rightarrow> L" "g \<midarrow>0\<rightarrow> M"
  shows "(\<forall>r>0. \<forall>x. x > 0 \<and> x < min (r/(2 * ln 2)) (SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
    \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2)) \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) x - max L M\<bar> < r)"
proof -
  {fix r \<gamma> :: real
    assume 1:"r>0"
    assume 2:"\<gamma>>0"
    then have "(\<gamma> < min (r/(2 * ln 2)) (SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
    \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2)) \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) \<gamma> - max L M\<bar> < r)"
      using 1 assms Max_gamma_works_chain [where ?\<epsilon>="r" and ?s="(SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
      \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2))" and ?f="f" and ?g="g" and ?L="L" and ?M="M" and ?\<gamma>="\<gamma>"] 
      by presburger}
  then show ?thesis by presburger
qed

lemma Max_gamma_lim_chain:
  fixes f g :: "real \<Rightarrow> real"
  assumes flim:"f \<midarrow>0\<rightarrow> L" and glim:"g \<midarrow>0\<rightarrow> M" and
    f_const_bel0:"\<forall>x\<le>0. f x = L" and g_const_bel0:"\<forall>x\<le>0. g x = M"
  shows "(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) \<midarrow>0\<rightarrow> max L M"
proof -
  have "(\<lambda>\<gamma>. max (f \<gamma>) (g \<gamma>)) \<midarrow>0\<rightarrow> max L M"
    using tendsto_max assms(1) assms(2) 
    by blast
  then have max_lim:"\<And>r. r>0 \<Longrightarrow> (\<exists>s. s \<in> {s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm (max (f x) (g x) - max L M) < r)})"
    using LIM_eq [where ?f="\<lambda>\<gamma>. max (f \<gamma>) (g \<gamma>)" and ?a="0" and ?L="max L M"] 
    by simp
  have 1:"\<forall>(r::real)>0. (r/(2 * ln 2)) > 0" by simp
  have 2:"\<And>s. \<forall>r>0. s \<in> {s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm (max (f x) (g x) - max L M) < r)} \<longrightarrow> s > 0"
    using max_lim by blast
  have 3:"\<forall>r>0. \<exists>x. x>0 \<and> x < min (r/(2 * ln 2)) (SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
    \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2))"
  proof -
    {fix s r :: real
      assume "r>0"
      then have "r/2>0" by simp
      assume s_defn:"s=(SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
    \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2))"
      then have "s \<in> {s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2)}"
        using max_lim [where ?r="r/2"] \<open>r/2>0\<close>  mem_Collect_eq someI
        by (metis (no_types, lifting))
      then have "s>0"
        by blast
      then have "\<exists>x. x>0 \<and> x < min (r/(2 * ln 2)) s"
        using 1 dense \<open>r>0\<close> 
        by (simp add: \<open>0 < r\<close> field_lbound_gt_zero)}
    then have "\<And>r. r>0 \<Longrightarrow> \<exists>x. x>0 \<and> x < min (r/(2 * ln 2)) (SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
    \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2))"
      by meson
    then show ?thesis
      by blast
  qed
  have 4:"\<And>(x::real) (s::real). s>0 \<Longrightarrow> (x>0\<and>x<s \<longrightarrow> x\<noteq>0 \<and> norm (x - 0) < s)"
    by auto
  have "(\<forall>r>0. \<forall>x. x > 0 \<and> x < min (r/(2 * ln 2)) (SOME s. s>0 \<and> (\<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s 
    \<longrightarrow> norm (max (f x) (g x) - max L M) < r/2))  \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) x - max L M\<bar> < r)"
    using Max_gamma_works_chain2 assms 
    by presburger
  then have "\<forall>r>0. \<exists>s>0. \<forall>x. x > 0 \<and> x < s \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) x - max L M\<bar> < r"
    using ln_gt_zero one_less_numeral_iff semiring_norm(76) zero_less_divide_iff max_lim 3
    by force
  then have "\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> \<bar>(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) x - max L M\<bar> < r"
    using 4 f_const_bel0 g_const_bel0
    by force 
  then have 1:"\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow> norm ((\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) x - (max L M)) < r"
    by simp
  then show ?thesis 
    using LIM_eq by blast
qed

lemma Min_gamma_lim_chain:
  fixes f g :: "real \<Rightarrow> real"
  assumes flim:"f \<midarrow>0\<rightarrow> L" and glim:"g \<midarrow>0\<rightarrow> M" and
    f_const_bel0:"\<forall>x\<le>0. f x = L" and g_const_bel0:"\<forall>x\<le>0. g x = M"
  shows "(\<lambda>\<gamma>. Min_gamma \<gamma> (f \<gamma>) (g \<gamma>)) \<midarrow>0\<rightarrow> min L M"
proof -
  have 00:"\<And>(a::real) b. min a b = -(max (-a) (-b))"
    by auto
  have 0:"(\<lambda>x. -(f x)) \<midarrow>0\<rightarrow> -L \<and> (\<lambda>x. -(g x)) \<midarrow>0\<rightarrow> -M" 
    using tendsto_minus flim glim
    by auto
  have "\<And>g a b. Min_gamma g a b = -(Max_gamma g (-a) (-b))"
    by auto
  then have 1:"\<And>\<gamma>. (\<lambda>\<gamma>. Min_gamma \<gamma> (f \<gamma>) (g \<gamma>)) = (\<lambda>\<gamma>. -(Max_gamma \<gamma> (-(f \<gamma>)) (-(g \<gamma>))))"
    by auto
  then have "(\<lambda>\<gamma>. Max_gamma \<gamma> (-(f \<gamma>)) (-(g \<gamma>))) \<midarrow>0\<rightarrow> max (-L) (-M)"
    using 0 Max_gamma_lim_chain assms 
    by presburger
  then have "(\<lambda>\<gamma>. -(Max_gamma \<gamma> (-(f \<gamma>)) (-(g \<gamma>)))) \<midarrow>0\<rightarrow> -(max (-L) (-M))"
    by (simp add: tendsto_minus)
  then show ?thesis
    using 00 1 
    by presburger
qed

lemma Max_gamma_cont_0:
  fixes a b :: real
  shows "isCont (\<lambda>\<gamma>. Max_gamma \<gamma> a b) 0"
  using Max_gamma_continuous_gamma UNIV_I continuous_on_eq_continuous_within
  by metis

lemma Max_gamma_const_bel0:
  fixes a b :: real
  shows "\<forall>x\<le>0. Max_gamma x a b = Max_gamma 0 a b"
  by simp

lemma Min_gamma_cont_0:
  fixes a b :: real
  shows "isCont (\<lambda>\<gamma>. Min_gamma \<gamma> a b) 0"
  using Min_gamma_continuous_gamma UNIV_I continuous_on_eq_continuous_within
  by metis

lemma Min_gamma_const_bel0:
  fixes a b :: real
  shows "\<forall>x\<le>0. Min_gamma x a b = Min_gamma 0 a b"
  by simp

lemma Max_gamma_chain_cont_0:
  fixes f g :: "real \<Rightarrow> real"
  assumes "isCont f 0" "isCont g 0" "\<forall>x\<le>0. f x = f 0" "\<forall>x\<le>0. g x = g 0"
  shows "isCont (\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) 0"
proof -
  have "f \<midarrow>0\<rightarrow> f 0 \<and> g \<midarrow>0\<rightarrow> g 0"
    using assms isCont_def 
    by blast
  then have "(\<lambda>\<gamma>. Max_gamma \<gamma> (f \<gamma>) (g \<gamma>)) \<midarrow>0\<rightarrow> max (f 0) (g 0)"
    using Max_gamma_lim_chain assms 
    by blast
  then show ?thesis using isCont_def 
    by fastforce
qed

lemma Min_gamma_chain_cont_0:
  fixes f g :: "real \<Rightarrow> real"
  assumes "isCont f 0" "isCont g 0" "\<forall>x\<le>0. f x = f 0" "\<forall>x\<le>0. g x = g 0"
  shows "isCont (\<lambda>\<gamma>. Min_gamma \<gamma> (f \<gamma>) (g \<gamma>)) 0"
proof -
  have "f \<midarrow>0\<rightarrow> f 0 \<and> g \<midarrow>0\<rightarrow> g 0"
    using assms isCont_def 
    by blast
  then have "(\<lambda>\<gamma>. Min_gamma \<gamma> (f \<gamma>) (g \<gamma>)) \<midarrow>0\<rightarrow> min (f 0) (g 0)"
    using Min_gamma_lim_chain assms 
    by blast
  then show ?thesis using isCont_def 
    by fastforce
qed

lemma Max_gamma_chain_const_bel0:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<forall>x\<le>0. f x = f 0" "\<forall>x\<le>0. g x = g 0"
  shows "\<forall>x\<le>0. Max_gamma x (f x) (g x) = Max_gamma 0 (f 0) (g 0)"
  using Max_gamma_const_bel0 assms(1) assms(2) by presburger

lemma Min_gamma_chain_const_bel0:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<forall>x\<le>0. f x = f 0" "\<forall>x\<le>0. g x = g 0"
  shows "\<forall>x\<le>0. Min_gamma x (f x) (g x) = Min_gamma 0 (f 0) (g 0)"
  using Min_gamma_const_bel0 assms(1) assms(2) by presburger

end