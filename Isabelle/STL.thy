theory STL
  imports Complex_Main STLLoss_max_min Code_Real_Approx_By_Float_2

begin

datatype cterm = Get int | Const real | Add cterm cterm | Mult cterm cterm | Uminus cterm | Divide cterm cterm

primrec subcterm :: "cterm \<Rightarrow> cterm \<Rightarrow> bool" where
"subcterm (Get n) c = (c = (Get n))"
| "subcterm (Const r) c = (c = (Const r))"
| "subcterm (Add c1 c2) c = ((c = (Add c1 c2)) \<or> subcterm c1 c \<or> subcterm c2 c)"
| "subcterm (Mult c1 c2) c = ((c = (Mult c1 c2)) \<or> subcterm c1 c \<or> subcterm c2 c)"
| "subcterm (Uminus c1) c = ((c = (Uminus c1)) \<or> subcterm c1 c)"
| "subcterm (Divide c1 c2) c = ((c = (Divide c1 c2)) \<or> subcterm c1 c \<or> subcterm c2 c)"

lemma subcterm_trans:
  assumes "subcterm c1 c2" "subcterm c2 c3"
  shows "subcterm c1 c3"
proof (insert assms, induction c1)
  case (Get n)
  then show ?case 
    by simp
next
  case (Const r)
  then show ?case 
    by simp
next
  case (Add c1 c2)
  then show ?case
    by force
next 
  case (Mult c1 c2)
  then show ?case
    by force
next
  case (Uminus c)
  then show ?case
    by force
next
  case (Divide c1 c2)
  then show ?case
    by force
qed

primrec (nonexhaustive) nthint :: "'a list \<Rightarrow> int \<Rightarrow> 'a" where
nthint_Cons:"nthint (x # xs) n = (if eqint n 0 then x else nthint xs (n-1))"

lemma nthint_Cons_0:"nthint (x#xs) 0 = x"
  by simp

lemma nthint_Cons_plusone:"n\<ge>0 \<longrightarrow> nthint (x#xs) (n+1) = nthint xs n"
  by fastforce

lemma eqint_eq:
  fixes n :: int and m :: nat
  assumes "n>0"
  shows "eqint n m = (nat n = m)"
  using assms nth_def by auto
            
fun Feval :: "cterm \<Rightarrow> real list \<Rightarrow> real" where
"Feval (Get n) xs = nthint xs n"
| "Feval (Const r) xs = r"
| "Feval (Add c1 c2) xs = Feval c1 xs + Feval c2 xs"
| "Feval (Mult c1 c2) xs = Feval c1 xs * Feval c2 xs"
| "Feval (Uminus c) xs = -1 * (Feval c xs)"
| "Feval (Divide c1 c2) xs = Feval c1 xs / Feval c2 xs"

datatype 'v constraint = cMu "cterm \<Rightarrow> 'v \<Rightarrow> real" cterm real | cNot "'v constraint" 
  | cAnd "'v constraint" "'v constraint" | cUntil real real "'v constraint" "'v constraint"

datatype rconstraint = crMu cterm real | crNot rconstraint 
  | crAnd rconstraint rconstraint | crUntil real real rconstraint rconstraint

fun subconstraint :: "'v constraint \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"subconstraint c (cMu f ct r) = (c = cMu f ct r)"
| "subconstraint c (cNot c1) = (c = (cNot c1) \<or> c = c1 \<or> subconstraint c c1)"
| "subconstraint c (cAnd c1 c2) = (c = (cAnd c1 c2) \<or> c = c1 \<or> c = c2 \<or> subconstraint c c1 \<or> subconstraint c c2)"
| "subconstraint c (cUntil x y c1 c2) = (c = (cUntil x y c1 c2) \<or> c = c1 \<or> c = c2 \<or> subconstraint c c1 \<or> subconstraint c c2)"

fun valid_constraint :: "real \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"valid_constraint l (cMu f ct r) = (l \<ge> 0)"
| "valid_constraint l (cNot c) = (valid_constraint l c)"
| "valid_constraint l (cAnd c1 c2) = ((valid_constraint l c1 \<and> valid_constraint l c2))"
| "valid_constraint l (cUntil x y c1 c2) = 
  (x \<le> l \<and> y \<le> l \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l-x) c1 
    \<and> valid_constraint (l-y) c1
    \<and> valid_constraint (l-x) c2
    \<and> valid_constraint (l-y) c2))"

lemma vc_l:
  assumes "valid_constraint l c"
  shows "l\<ge>0"
proof (insert assms, induct c)
  case (cMu f ct r)
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
  fixes l r :: real and c :: "'v constraint"
  assumes "r\<ge>0" "valid_constraint l c"
  shows "valid_constraint (l+r) c"
proof (insert assms, induct c arbitrary:  l r)
  case (cMu f ct r)
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

lemma vc_subconstraint:
  fixes l :: real and c c1 :: "'v constraint"
  assumes "valid_constraint l c" "subconstraint c' c"
  shows "valid_constraint l c'"
proof (insert assms, induction c)
  case (cMu f ct r)
  then show ?case 
    using subconstraint.simps(1) valid_constraint.simps(1)
    by force
next
  case (cNot c)
  then show ?case
    using subconstraint.simps(2) valid_constraint.simps(2)
    by auto
next
  case (cAnd c1 c2)
  then show ?case
    using subconstraint.simps(3) valid_constraint.simps(3)
    by auto
next
  case (cUntil x y c1 c2)
  then show ?case
    using subconstraint.simps(4) valid_constraint.simps(4) vc_longer diff_add_cancel
    by metis
qed

fun evalvc :: "(real \<Rightarrow> 'v) \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"evalvc t l (cMu f ct r) = (valid_constraint l (cMu f ct r) \<and> ((f ct (t 0)) > r))"
| "evalvc t l (cNot c) = (valid_constraint l (cNot c) \<and> (\<not>(evalvc t l c)))"
| "evalvc t l (cAnd c1 c2) = (valid_constraint l (cAnd c1 c2) \<and> 
  ((evalvc t l c1) \<and> (evalvc t l c2)))"
| "evalvc t l (cUntil x y c1 c2) = 
  (valid_constraint l (cUntil x y c1 c2) \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> evalvc (\<lambda>r. t (r+t')) (l-t') c2 
    \<and> (\<forall>t''. t''\<ge>0\<and>t''\<le>t' \<longrightarrow> evalvc (\<lambda>r. t (r+t'')) (l-t'') c1)))"

fun eval :: "(real \<Rightarrow> 'v) \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"eval t l (cMu f ct r) = ((f ct (t 0)) > r)"
| "eval t l (cNot c) = (\<not>(eval t l c))"
| "eval t l (cAnd c1 c2) = ((eval t l c1) \<and> (eval t l c2))"
| "eval t l (cUntil x y c1 c2) = (\<exists>t'\<ge>x. t'\<le>y \<and> t'\<le>l \<and> eval (\<lambda>r. t (r+t')) (l-t') c2 
    \<and> (\<forall>t''. t''\<ge>0\<and>t''\<le>t' \<longrightarrow> eval (\<lambda>r. t (r+t'')) (l-t'') c1))"

lemma evalvc_vc:
  assumes "evalvc t l c"
  shows "valid_constraint l c"
  using evalvc.simps assms constraint.exhaust 
  by metis

definition cTrue :: "'v constraint" where
"cTrue = cMu (\<lambda>ct r. 1) (Const 1) 0"

lemma cTrue_vc:"valid_constraint l cTrue = (l\<ge>0)"
  using valid_constraint.simps(1) cTrue_def
  by metis

lemma cTrue_evalvc: "evalvc t l cTrue = (l\<ge>0)"
  using cTrue_def evalvc.simps(1) zero_less_one cTrue_vc
  by metis

lemma cTrue_eval:"eval t l cTrue"
  using cTrue_def eval.simps(1) zero_less_one
  by metis

definition cOr :: "'v constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
"cOr c1 c2 = cNot (cAnd (cNot c1) (cNot c2))"

lemma cOr_vc:"valid_constraint l (cOr c1 c2) = (valid_constraint l c1 \<and> valid_constraint l c2)"
  using valid_constraint.simps(2,3) cOr_def
  by metis

lemma cOr_evalvc:"evalvc t l (cOr c1 c2) = (valid_constraint l (cOr c1 c2) \<and> (evalvc t l c1 \<or> evalvc t l c2))"
  using valid_constraint.simps(2,3) cOr_def evalvc.simps(2,3)
  by metis

lemma cOr_eval:"eval t l (cOr c1 c2) = (eval t l c1 \<or> eval t l c2)"
  using cOr_def eval.simps(2,3) 
  by metis

definition cImplies :: "'v constraint \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
"cImplies c1 c2 = cOr (cNot c1) c2"

lemma cImplies_vc:"valid_constraint l (cImplies c1 c2) = (valid_constraint l c1 \<and> valid_constraint l c2)"
  using valid_constraint.simps(2,3) cImplies_def cOr_def
  by metis

lemma cImplies_evalvc:"evalvc t l (cImplies c1 c2) = (valid_constraint l (cImplies c1 c2) \<and> (evalvc t l c1 \<longrightarrow> evalvc t l c2))"
  using valid_constraint.simps(2,3) cOr_def evalvc.simps(2,3) cImplies_def
  by metis

lemma cImplies_eval:"eval t l (cImplies c1 c2) = (eval t l c1 \<longrightarrow> eval t l c2)"
  using cImplies_def eval.simps(2) cOr_eval
  by metis

definition cEventually :: "real \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
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

lemma cEventually_evalvc: "evalvc t l (cEventually x y c) = (valid_constraint l (cEventually x y c) 
  \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> evalvc (\<lambda>r. t (r+t')) (l-t') c))"
proof -
  have "evalvc t l (cEventually x y c) = evalvc t l (cUntil x y cTrue c)"
    using cEventually_def
    by metis
  then have 1:"evalvc t l (cEventually x y c) = (valid_constraint l (cEventually x y c) 
      \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> evalvc (\<lambda>r. t (r+t')) (l-t') c
      \<and> (\<forall>t''. t''\<ge>0\<and>t''\<le>t' \<longrightarrow> evalvc (\<lambda>r. t (r+t'')) (l-t'') cTrue)))"
    using evalvc.simps(4) cEventually_vc' cEventually_vc valid_constraint.simps(4)
    by blast
  then show ?thesis
  proof -
    have 2:"evalvc t l (cEventually x y c) = (valid_constraint l (cEventually x y c)
    \<and> (\<exists>t'\<ge>x. t'\<le>y \<and> evalvc (\<lambda>r. t (r+t')) (l-t') c
    \<and> t'\<le>l))"
      using 1 cTrue_evalvc valid_constraint.simps(4) cTrue_def cEventually_vc
      by (smt (verit, ccfv_threshold))
    then have "\<forall>t'. evalvc (\<lambda>r. t (r+t')) (l-t') c \<longrightarrow> l-t'\<ge>0"
      using evalvc_vc vc_l
      by metis
    then show ?thesis
      using 2 
      by auto
  qed
qed

lemma cEventually_eval: "eval t l (cEventually x y c) = (\<exists>t'\<ge>x. t'\<le>y \<and> t'\<le>l \<and> eval (\<lambda>r. t (r+t')) (l-t') c)"
  using cTrue_eval eval.simps(4) cEventually_def
  by metis

definition cAlways :: "real \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> 'v constraint" where
"cAlways x y c = cNot (cEventually x y (cNot c))"

lemma cAlways_vc:"valid_constraint l (cAlways x y c) = 
  (x \<le> l \<and> y \<le> l \<and> x \<ge> 0 \<and> y \<ge> 0 \<and> 
    (valid_constraint (l-x) c 
    \<and> valid_constraint (l-y) c))"
  using cAlways_def cEventually_vc valid_constraint.simps cTrue_vc vc_l
  by (smt (verit, del_insts))

lemma cAlways_evalvc:"evalvc t l (cAlways x y c) =
  (valid_constraint l (cAlways x y c) \<and> (\<forall>t'\<ge>x. t'\<le>y \<longrightarrow> evalvc (\<lambda>r. t (r+t')) (l-t') c))"
proof -
  have "evalvc t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(evalvc t l (cEventually x y (cNot c)))))"
    using cAlways_def evalvc.simps(2)
    by metis
  then have "evalvc t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> evalvc (\<lambda>r. t (r+t')) (l-t') (cNot c))))"
    using cEventually_evalvc cAlways_vc cEventually_vc valid_constraint.simps(2)
    by blast
  then have 1:"evalvc t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> valid_constraint (l-t') c \<and> (\<not>(evalvc (\<lambda>r. t (r+t')) (l-t') c)))))"
    using evalvc.simps(2) valid_constraint.simps(2)
    by blast
  have "evalvc t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> valid_constraint (l-x) c \<and> (\<not>(evalvc (\<lambda>r. t (r+t')) (l-t') c)))))"
    using vc_longer add_0 add_diff_cancel_left' add_le_cancel_left cAlways_vc diff_add_cancel
    by (metis 1)
  then have "evalvc t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> (\<not>(evalvc (\<lambda>r. t (r+t')) (l-t') c)))))"
    using cAlways_vc 
    by blast
  then have "evalvc t l (cAlways x y c) 
    = (valid_constraint l (cAlways x y c) 
      \<and> ((\<forall>t'\<ge>x. \<not>(t'\<le>y \<and> (\<not>(evalvc (\<lambda>r. t (r+t')) (l-t') c))))))"
    by blast
  then show ?thesis
    by blast
qed

lemma cAlways_eval:"eval t l (cAlways x y c) = (\<forall>t'\<ge>x. t'\<le>y \<and> t'\<le>l \<longrightarrow> eval (\<lambda>r. t (r+t')) (l-t') c)"
proof -
  have "eval t l (cAlways x y c) = (\<not>(\<exists>t'\<ge>x. t'\<le>y \<and> t'\<le>l \<and> eval (\<lambda>r. t (r+t')) (l-t') (cNot c)))"
    using cEventually_eval cAlways_def eval.simps(2)
    by metis
  then show ?thesis
    using eval.simps(2)
    by blast
qed

end