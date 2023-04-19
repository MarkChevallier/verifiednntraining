theory STL
  imports Complex_Main

begin

datatype 'v::real_vector constraint = cMu "'v \<Rightarrow> real" real | cNot "'v constraint" 
  | cAnd "'v constraint" "'v constraint" | cUntil real real "'v constraint" "'v constraint"

fun valid_constraint :: "real \<Rightarrow> 'v::real_vector constraint \<Rightarrow> bool" where
"valid_constraint l (cMu f r) = (l \<ge> 0)"
| "valid_constraint l (cNot c) = (valid_constraint l c)"
| "valid_constraint l (cAnd c1 c2) = ((valid_constraint l c1 \<and> valid_constraint l c2))"
| "valid_constraint l (cUntil x y c1 c2) = 
  (x \<le> l \<and> y \<le> l \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l-x) c1 
    \<and> valid_constraint (l-y) c1
    \<and> valid_constraint (l-x) c2
    \<and> valid_constraint (l-y) c2))"

lemma vc_l:
  shows "valid_constraint l c \<longrightarrow> l\<ge>0"
proof (induct c)
  case (cMu f r)
  then show ?case 
    using valid_constraint.simps(1) 
    by blast
next
  case (cAnd c1 c2)
  then show ?case 
    by simp
next
  case (cNot c)
  then show ?case
    by simp
next
  case (cUntil x y c1 c2)
  then show ?case
    using valid_constraint.simps(4)
    by force
qed

lemma vc_longer:
  fixes l r :: real and c :: "'v::real_vector constraint"
  assumes "r\<ge>0" "valid_constraint l c"
  shows "valid_constraint (l+r) c"
proof (insert assms, induct c arbitrary:  l r)
  case (cMu f r)
  then show ?case 
    using valid_constraint.simps(1) 
    by auto
next
  case (cNot c)
  then show ?case
    using valid_constraint.simps(2)
    by blast
next
  case (cAnd c)
  then show ?case
    using valid_constraint.simps(3)
    by blast
next
  case (cUntil x y c1 c2)
  then have "(x \<le> l \<and> y \<le> l \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l-x) c1 
    \<and> valid_constraint (l-y) c1
    \<and> valid_constraint (l-x) c2
    \<and> valid_constraint (l-y) c2))"
    using valid_constraint.simps(4)
    by force
  then have "(x \<le> l+r \<and> y \<le> l+r \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l+r-x) c1 
    \<and> valid_constraint (l+r-y) c1
    \<and> valid_constraint (l+r-x) c2
    \<and> valid_constraint (l+r-y) c2))"
    using cUntil.hyps(1) cUntil.hyps(2) cUntil.prems(1)
    by (smt (verit, ccfv_SIG))
  then show ?case
    using valid_constraint.simps(4)
    by blast
qed

fun eval :: "(real \<Rightarrow> 'v::real_vector) \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"eval t l (cMu f r) = (valid_constraint l (cMu f r) \<and> ((f (t 0)) > r))"
| "eval t l (cNot c) = (valid_constraint l (cNot c) \<and> (\<not>(eval t l c)))"
| "eval t l (cAnd c1 c2) = (valid_constraint l (cAnd c1 c2) \<and> 
  ((eval t l c1) \<and> (eval t l c2)))"
| "eval t l (cUntil x y c1 c2) = 
  (valid_constraint l (cUntil x y c1 c2) \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> eval (\<lambda>r. t (r+t')) (l-t') c2 
    \<and> (\<forall>t''. t''\<ge>x\<and>t''\<le>t' \<longrightarrow> eval (\<lambda>r. t (r+t'')) (l-t'') c1)))"

lemma eval_vc:
  assumes "eval t l c"
  shows "valid_constraint l c"
  using eval.simps assms constraint.exhaust 
  by metis

definition cTrue :: "'v::real_vector constraint" where
"cTrue = cMu (\<lambda>r. 1) 0"

lemma cTrue_vc:"valid_constraint l cTrue = (l\<ge>0)"
  using valid_constraint.simps(1) cTrue_def
  by metis

lemma cTrue_eval: "eval t l cTrue = (l\<ge>0)"
  using cTrue_def eval.simps(1) zero_less_one cTrue_vc
  by metis

definition cOr :: "'v::real_vector constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
"cOr c1 c2 = cNot (cAnd (cNot c1) (cNot c2))"

lemma cOr_vc:"valid_constraint l (cOr c1 c2) = (valid_constraint l c1 \<and> valid_constraint l c2)"
  using valid_constraint.simps(2,3) cOr_def
  by metis

lemma cOr_eval:"eval t l (cOr c1 c2) = (valid_constraint l (cOr c1 c2) \<and> (eval t l c1 \<or> eval t l c2))"
  using valid_constraint.simps(2,3) cOr_def eval.simps(2,3)
  by metis

definition cEventually :: "real \<Rightarrow> real \<Rightarrow> 'v::real_vector constraint \<Rightarrow> 'v constraint" where
"cEventually x y c = cUntil x y cTrue c"

lemma cEventually_vc: "valid_constraint l (cEventually x y c) =   
  (x \<le> l \<and> y \<le> l \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l-x) c 
    \<and> valid_constraint (l-y) c))"
  using cEventually_def valid_constraint.simps(4) cTrue_vc vc_l
  by metis

lemma cEventually_vc': "valid_constraint l (cEventually x y c) = valid_constraint l (cUntil x y cTrue c)" 
  using cEventually_def
  by metis

lemma cEventually_eval: "eval t l (cEventually x y c) = (valid_constraint l (cEventually x y c) 
  \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> eval (\<lambda>r. t (r+t')) (l-t') c))"
proof -
  have "eval t l (cEventually x y c) = eval t l (cUntil x y cTrue c)"
    using cEventually_def
    by metis
  then have 1:"eval t l (cEventually x y c) = (valid_constraint l (cEventually x y c) 
      \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> eval (\<lambda>r. t (r+t')) (l-t') c
      \<and> (\<forall>t''. t''\<ge>x\<and>t''\<le>t' \<longrightarrow> eval (\<lambda>r. t (r+t'')) (l-t'') cTrue)))"
    using eval.simps(4) cEventually_vc' cEventually_vc valid_constraint.simps(4)
    by blast
  then show ?thesis
  proof -
    have 2:"eval t l (cEventually x y c) = (valid_constraint l (cEventually x y c)
    \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> eval (\<lambda>r. t (r+t')) (l-t') c
    \<and> t'\<le>l))"
      using 1 cTrue_eval valid_constraint.simps(4) cTrue_def
      by (smt (verit, ccfv_threshold))
    then have "\<forall>t'. eval (\<lambda>r. t (r+t')) (l-t') c \<longrightarrow> l-t'\<ge>0"
      using eval_vc vc_l
      by metis
    then show ?thesis
      using 2 
      by auto
  qed
qed

definition cAlways :: "real \<Rightarrow> real \<Rightarrow> 'v::real_vector constraint \<Rightarrow> 'v constraint" where
"cAlways x y c = cNot (cEventually x y (cNot c))"

lemma cAlways_vc:"valid_constraint l (cAlways x y c) = 
  (x \<le> l \<and> y \<le> l \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l-x) c 
    \<and> valid_constraint (l-y) c))"
  using cAlways_def cEventually_vc valid_constraint.simps cTrue_vc vc_l
  by (smt (verit, del_insts))

lemma cAlways_eval:"eval t l (cAlways x y c) =
  (valid_constraint l (cAlways x y c) \<and> (\<forall>t'\<ge>x. t'\<le>y \<longrightarrow> eval (\<lambda>r. t (r+t')) (l-t') c))"
proof -
  have "eval t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(eval t l (cEventually x y (cNot c)))))"
    using cAlways_def eval.simps(2)
    by metis
  then have "eval t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> eval (\<lambda>r. t (r+t')) (l-t') (cNot c))))"
    using cEventually_eval cAlways_vc cEventually_vc valid_constraint.simps(2)
    by blast
  then have 1:"eval t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> valid_constraint (l-t') c \<and> (\<not>(eval (\<lambda>r. t (r+t')) (l-t') c)))))"
    using eval.simps(2) valid_constraint.simps(2)
    by blast
  then have "eval t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> valid_constraint (l-x) c \<and> (\<not>(eval (\<lambda>r. t (r+t')) (l-t') c)))))"
    using vc_longer add_0 add_diff_cancel_left' add_le_cancel_left cAlways_vc diff_add_cancel
    by (metis 1)
  then have "eval t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> (\<not>(eval (\<lambda>r. t (r+t')) (l-t') c)))))"
    using cAlways_vc 
    by blast
  then have "eval t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> ((\<forall>t'\<ge>x. \<not>(t'\<le>y \<and> (\<not>(eval (\<lambda>r. t (r+t')) (l-t') c))))))"
    by blast
  then show ?thesis
    by blast
qed

end