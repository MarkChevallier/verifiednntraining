theory Signal
  imports Complex_Main

begin

fun Cons_sort :: "(real\<times>'v) \<Rightarrow> (real\<times>'v) list \<Rightarrow> (real\<times>'v) list" where
"Cons_sort y [] = [y]"
| "Cons_sort y (x#xs) = (if fst y < fst x then (y#(x#xs)) else (x#xs))"

lemma Cons_sort_works:
  fixes y :: "(real\<times>'v)" and ys :: "(real \<times> 'v) list"
  assumes "sorted_wrt (<) (map fst ys)"
  shows "sorted_wrt (<) (map fst (Cons_sort y ys))"
proof (cases "(fst y) < (fst (ys!0)) \<and> ys \<noteq> []")
  case True
  then show ?thesis
    using Cons_sort.elims assms in_set_conv_nth leI list.simps(9) not_less_zero nth_Cons_0 
      sorted_nth_mono strict_sorted_iff strict_sorted_simps(2)
    by (smt (verit, best))
next
  case False
  then show ?thesis
    using Cons_sort.simps(1) Cons_sort.elims assms list.simps(8,9) nth_Cons_0 sorted_wrt1
    by metis
qed

typedef 'v signal = "{xs::(real\<times>'v) list. sorted_wrt (<) (map fst xs)}"
  morphisms to_list to_sig 
  apply (rule_tac x=Nil in exI) 
  by force

declare to_sig_inverse [simp]
    and to_list_inverse [simp]

thm list.induct

setup_lifting type_definition_signal

lift_definition sNil :: "'v signal" is Nil by simp
lift_definition ssCons :: "(real\<times>'v) \<Rightarrow> 'v signal \<Rightarrow> (real\<times>'v) list" is Cons .
lift_definition ssmap :: "((real\<times>'v) \<Rightarrow> 'a) \<Rightarrow> 'v signal \<Rightarrow> 'a list" is "map" .
lift_definition srel :: "((real\<times>'v) \<Rightarrow> (real\<times>'v) \<Rightarrow> bool) \<Rightarrow> 'v signal \<Rightarrow> 'v signal \<Rightarrow> bool" is "list_all2" .
lift_definition spred :: "((real\<times>'v) \<Rightarrow> bool) \<Rightarrow> 'v signal \<Rightarrow> bool" is "list_all" .
lift_definition snth :: "'v signal \<Rightarrow> nat \<Rightarrow> (real\<times>'v)" (infixl "!!" 90) is "(!)" .
lift_definition slength :: "'v signal \<Rightarrow> nat" is "length" .
lift_definition shd :: "'v signal \<Rightarrow> (real\<times>'v)" is "hd" .
lift_definition stl :: "'v signal \<Rightarrow> 'v signal" is "tl"
  by (simp add: distinct_tl map_tl sorted_tl strict_sorted_iff)
lift_definition sCons :: "(real\<times>'v) \<Rightarrow> 'v signal \<Rightarrow> 'v signal" (infixl "##" 90) is Cons_sort 
  using Cons_sort_works by blast

lemma sCons_works: 
  fixes t1 :: "(real\<times>'v)" and t :: "'v signal"
  shows "sorted_wrt (<) (map fst (to_list (sCons t1 t)))"
  using Cons_sort_works to_list
  by fastforce

lemma signal_rep:
  "t = sNil \<or> (\<exists>p t'. (fst p < fst (t'!!0) \<or> t' = sNil) \<and> t = sCons p t')"
proof (cases "t=sNil")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
  proof (cases "slength t = 1")
    case True
    then have "t=sCons (shd t) sNil"
      using \<open>\<not>(t=sNil)\<close>
      

lemma [case_names sNil sCons, cases type: signal]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "(y = sNil \<Longrightarrow> P) \<Longrightarrow> (\<And>a signal. y = sCons a signal \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis order_less_irrefl sCons_def)

lemma [case_names sNil ssCons, induct type: signal]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "P sNil \<Longrightarrow> (\<And>a signal. P signal \<Longrightarrow> P (sCons a signal)) \<Longrightarrow> P signal"
proof -
  {assume "P sNil"
    assume "\<And>a signal. P signal \<Longrightarrow> P (sCons a signal)"
    have "P signal"
    proof (induct "slength signal")
      case 0
      then have "signal = sNil"
        using length_greater_0_conv list.size(3) sNil.abs_eq slength.rep_eq to_list_inverse
        by metis
      then show ?thesis
        using \<open>P sNil\<close>
        by blast
    next
      case (Suc n)
      then obtain p t' where "signal = sCons p t'"
        using order_less_irrefl sCons_def
        by metis
      then show ?thesis
      proof (cases "fst p \<le>
      have "slength t' = n"
        using Suc 
      then show ?thesis
        using \<open>\<And>a signal. P signal \<Longrightarrow> P (sCons a signal)\<close> Suc
        
        
  have "sorted_wrt (<) (map fst (to_list signal))"
    using to_list
    by blast
  have "P  (to_sig [])"
    using \<open>P sNil\<close> sNil_def
    by metis
  then have "(P \<circ> to_sig) []"
    by simp
  have 1:"\<And>a signal. P signal \<Longrightarrow> 
    P (if fst a < fst (signal!!0) then to_sig (a#(to_list signal)) else signal)"
    using \<open>\<And>a signal. P signal \<Longrightarrow> P (sCons a signal)\<close> sCons_def
    by (metis (full_types))
  {fix a :: "(real\<times>'a)" and signal :: "'a signal"
    {assume 2: "P (to_sig (to_list signal))"
      then have "P (sCons
    have "P (to_sig (to_list signal)) \<Longrightarrow> P (to_sig (a#(to_list signal)))"
    proof -
      {assume 2:
        
  
    

setup \<open>Sign.mandatory_path "signal"\<close>

lemmas inducts = signal.induct
lemmas recs = signal.rec
lemmas cases = signal.case

setup \<open>Sign.parent_path\<close>

lemmas set_simps = list.set (* legacy *)

definition smap :: "('v \<Rightarrow> 'a) \<Rightarrow> 'v signal \<Rightarrow> 'a signal" where
"smap f t = to_sig (map (\<lambda>x. (fst x, f (snd x))) (to_list t))"

definition sfind :: "real \<Rightarrow> 'v signal \<Rightarrow> 'v" where
"sfind x t = (snd (the (find (\<lambda>y. fst y = x) (to_list t))))"

lemma smap_nth:
  assumes "n<slength t"
  shows "snth (smap f t) n = (fst ((to_list t)!n), f (snd ((to_list t)!n)))"
proof -
  have 1:"distinct (map fst (to_list t)) \<and> sorted (map fst (to_list t))"
    using to_list strict_sorted_iff
    by auto
  have "\<forall>n<length (to_list t). fst ((map (\<lambda>x. (fst x, f (snd x))) (to_list t))!n) = fst ((to_list t)!n)"
    by force
  then have 2:"distinct (map fst (map (\<lambda>x. (fst x, f (snd x))) (to_list t))) 
    \<and> sorted (map fst (map (\<lambda>x. (fst x, f (snd x))) (to_list t)))"
    using 1 length_map list_eq_iff_nth_eq nth_map
    by (metis (mono_tags, lifting))
  have "\<And>t. snth t n = (to_list t)!n"
    by transfer simp
  then have "snth (smap f t) n = (to_list (smap f t))!n"
    by auto
  then have "snth (smap f t) n = (to_list (to_sig (map (\<lambda>x. (fst x, f (snd x))) (to_list t))))!n"
    using smap_def 
    by metis
  then have "snth (smap f t) n = (map (\<lambda>x. (fst x, f (snd x))) (to_list t))!n"
    using to_sig_inverse 2 strict_sorted_iff
    by fastforce
  then show ?thesis
    using assms length_map list_update_id map_update nth_list_update_eq slength.rep_eq
    by (metis (no_types, lifting))
qed

end