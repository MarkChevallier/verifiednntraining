theory Nequal
  imports Tensor Tensor_Plus Tensor_Exp_Ln Tensor_Minus
  Tensor_Pow Tensor_Mul Max_Min Tensor_Scalar_Mult
begin


(* Single operation *)
fun Nzero :: "real \<Rightarrow> real" where "Nzero x = (if x=(0::real) then 1::real else 0::real)"

fun Bell_gamma :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Bell_gamma \<gamma> x = (if \<gamma>\<le>(0::real) then (Nzero x) else (1::real)/exp((x*x)/(\<gamma>+\<gamma>)))"

fun Bell_gamma_nc :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Bell_gamma_nc \<gamma> x = (if \<gamma>\<le>0 then (Nzero x) else 1/exp((x^2)/(2*\<gamma>)))"

lemma Bell_gamma_equiv:"Bell_gamma \<gamma> x = Bell_gamma_nc \<gamma> x"
  by (simp add: power2_eq_square)

definition Bell_gamma_unop :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Bell_gamma_unop \<gamma> x = (if \<gamma>\<le>(0::real) then (Nzero x) else exp((-x*x)/(\<gamma>+\<gamma>)))"

lemma Bell_gamma_unop_equiv:"Bell_gamma \<gamma> x = Bell_gamma_unop \<gamma> x"
  by (simp add: Bell_gamma_unop_def exp_minus inverse_eq_divide)

fun Nequal_gamma :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where 
"Nequal_gamma \<gamma> a b = Bell_gamma_unop \<gamma> (a-b)"


definition tensor_Nequal_gamma :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Nequal_gamma \<gamma> A B = unop (Bell_gamma_unop \<gamma>) (A-B)"


definition tensor_Nzero :: "real tensor \<Rightarrow> real tensor" where "tensor_Nzero A = unop Nzero A"

definition tensor_Bell_gamma_sep :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Bell_gamma_sep \<gamma> A = (if \<gamma> \<le>(0::real) then (tensor_Nzero A) else tensor_exp ((tensor_sqr A) \<div> (-(\<gamma>+\<gamma>))))"


lemma tensor_Bell_sep_equiv:
  shows "unop (Bell_gamma_unop \<gamma>) A = tensor_Bell_gamma_sep \<gamma> A"
proof (cases "\<gamma>\<le>0")
  case True
  then show ?thesis
    using Bell_gamma_unop_def tensor_Bell_gamma_sep_def tensor_Nzero_def by presburger 
next
  case A: False
  hence "tensor_Bell_gamma_sep \<gamma> A = tensor_exp (unop (\<lambda>x. (x*x) / (-(\<gamma>+\<gamma>))) A)" using tensor_Bell_gamma_sep_def
    unop_composition2[where ?f="\<lambda>x. x*x" and ?g="\<lambda>x. x / (-(\<gamma>+\<gamma>))"] tensor_sqr_def[where ?A="A"] sdiv_def[where ?\<alpha>="-(\<gamma>+\<gamma>)"] 
    by simp
  hence "tensor_Bell_gamma_sep \<gamma> A = unop (\<lambda>x. exp (x * x / - (\<gamma> + \<gamma>))) A" using tensor_exp_def unop_composition2 by simp
  moreover have "(\<lambda>x. exp (x * x / - (\<gamma> + \<gamma>))) = Bell_gamma_unop \<gamma>" using A Bell_gamma_unop_def by auto
  ultimately show ?thesis by simp
qed


definition tensor_Nequal_gamma_sep :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor"
  where "tensor_Nequal_gamma_sep \<gamma> A B = (tensor_Bell_gamma_sep \<gamma>) (A-B)"


lemma tensor_Nequal_gamma_sep_equiv:
  shows "tensor_Nequal_gamma_sep \<gamma> A B = tensor_Nequal_gamma \<gamma> A B"
  by (simp add: tensor_Bell_sep_equiv tensor_Nequal_gamma_def tensor_Nequal_gamma_sep_def)


fun dBell_gamma_dx :: "real \<Rightarrow> real \<Rightarrow> real" where
  "dBell_gamma_dx \<gamma> x = exp (-(x*x)/(\<gamma>+\<gamma>))*(-x/\<gamma>)"


definition tensor_dMax_gamma_ds :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor" where
  "tensor_dMax_gamma_ds \<gamma> A dA B dB = (repeat_subtensor (binop (dMax_gamma_da \<gamma>) A B) (take 2 (dims dA))) * dA + (repeat_subtensor (binop (dMax_gamma_db \<gamma>) A B) (take 2 (dims dB))) * dB"


definition tensor_dMin_gamma_ds :: "real \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor" where
  "tensor_dMin_gamma_ds \<gamma> A dA B dB = (repeat_subtensor (binop (dMin_gamma_da \<gamma>) A B) (take 2 (dims dA))) * dA + (repeat_subtensor (binop (dMin_gamma_db \<gamma>) A B) (take 2 (dims dB))) * dB"


end