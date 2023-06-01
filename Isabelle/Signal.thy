theory Signal
  imports Complex_Main

begin

typedef 'v signal = "{xs::(real\<times>'v) list. distinct (map fst xs) \<and> sorted (map fst xs)}"
  morphisms to_list to_sig 
  apply (rule_tac x=Nil in exI) 
  by force

declare to_sig_inverse [simp]
    and to_list_inverse [simp]

setup_lifting type_definition_signal

lift_definition snth :: "'v signal \<Rightarrow> nat \<Rightarrow> (real\<times>'v)" (infixl "!!" 90) is "(!)" .
lift_definition slength :: "'v signal \<Rightarrow> nat" is "length" .
lift_definition shd :: "'v signal \<Rightarrow> (real\<times>'v)" is "hd" .
lift_definition stl :: "'v signal \<Rightarrow> 'v signal" is "tl"
  by (simp add: distinct_tl map_tl sorted_tl)

lemma tst: 
  fixes t1 :: "(real\<times>'v)" and t :: "'v signal"
  assumes "(fst t1) < (fst (t!!0))"
  shows "distinct (map fst (t1#(to_list t)))" "sorted (map fst (t1#(to_list t)))"
proof -
  have 1:"distinct (map fst (to_list t))" "sorted (map fst (to_list t))"
    using to_list
    by blast+
  then have "tl (map fst (t1#(to_list t))) = (map fst (to_list t))"
    by force
  then show "distinct (map fst (t1#(to_list t)))" "sorted (map fst (t1#(to_list t)))"
  proof -
    have "\<forall>n<length (to_list t). fst ((to_list t)!0) \<le> fst ((to_list t)!n)"
      using 1
      by (simp add: sorted_iff_nth_mono)
    then show "sorted (map fst (t1#(to_list t)))"
      using sorted_iff_nth_mono assms 
      sledgehammer

      

    

definition sCons :: "(real\<times>'v) \<Rightarrow> 'v signal \<Rightarrow> 'v signal" where
"sCons t1 t = (if ((fst t1) < (fst (t!!0))) then (to_sig (t1#(to_list t))) else (t1))"

lemma [case_names Nil Cons, cases type: signal]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "(y = [] \<Longrightarrow> P) \<Longrightarrow> (\<And>a list. y = a # list \<Longrightarrow> P) \<Longrightarrow> P"

definition smap :: "('v \<Rightarrow> 'a) \<Rightarrow> 'v signal \<Rightarrow> 'a signal" where
"smap f t = to_sig (map (\<lambda>x. (fst x, f (snd x))) (to_list t))"

definition sfind :: "real \<Rightarrow> 'v signal \<Rightarrow> 'v" where
"sfind x t = (snd (the (find (\<lambda>y. fst y = x) (to_list t))))"

lemma smap_nth:
  assumes "n<slength t"
  shows "snth (smap f t) n = (fst ((to_list t)!n), f (snd ((to_list t)!n)))"
proof -
  have 1:"distinct (map fst (to_list t)) \<and> sorted (map fst (to_list t))"
    using to_list 
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
    using to_sig_inverse 2
    by simp
  then show ?thesis
    using assms length_map list_update_id map_update nth_list_update_eq slength.rep_eq
    by (metis (no_types, lifting))
qed

end