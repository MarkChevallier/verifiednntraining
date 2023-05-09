theory Scratch
  imports STL "List-Index.List_Index"

begin

definition valid_signal :: "(real \<times> 'v::real_vector) list \<Rightarrow> bool" where
"valid_signal xs = distinct (map fst xs)"

definition find_time :: "(real \<times> 'v::real_vector) list \<Rightarrow> real \<Rightarrow> 'v" where
"find_time xs r = (snd (the (find (\<lambda>x. fst x = r) xs)))"
(* remove None *)

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

  
  


end