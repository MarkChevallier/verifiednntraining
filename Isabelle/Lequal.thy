theory Lequal

imports Max_Min

begin

(** Rectified Linear Function **)
fun Rect :: "real \<Rightarrow> real" where "Rect x = max x 0"

(** Soft Approximation to Rectified Linear Function **)
fun Rect_gamma :: "real \<Rightarrow> real \<Rightarrow> real" where
"Rect_gamma \<gamma> x = Max_gamma \<gamma> x 0"

lemma Rect_gamma_comp_eq:
  shows "Rect_gamma \<gamma> x = Max_gamma \<gamma> x 0"
  using Max_gamma_comp_eq by simp

lemma Rect_gamma_works:
  fixes x :: real
  shows "(\<lambda>\<gamma>. Rect_gamma \<gamma> x) \<midarrow>0\<rightarrow> Rect x"
proof -
  have "(\<lambda>\<gamma>. Rect_gamma \<gamma> x) = (\<lambda>\<gamma>. Max_gamma \<gamma> x 0)"
    using Rect_gamma_comp_eq by blast
  then show ?thesis
    using Max_gamma_lim Rect.simps
    by auto
qed

(** Derivative of the Soft Approximation **)
fun dRect_gamma_dx :: "real \<Rightarrow> real \<Rightarrow> real" where
"dRect_gamma_dx \<gamma> x = (if \<gamma> \<le> 0 then (Rect x) else dMax_gamma_da \<gamma> x 0)"

fun Lequal_gamma :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where "Lequal_gamma \<gamma> a b = Rect_gamma \<gamma> (a-b)"

fun dLequal_gamma_ds :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "dLequal_gamma_ds \<gamma> a da b db = dRect_gamma_dx \<gamma> (a-b) * (da - db)"

fun dMin_gamma_ds :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dMin_gamma_ds \<gamma> a da b db = (dMin_gamma_da \<gamma> a b) * da + (dMin_gamma_db \<gamma> a b) * db"

lemma Rect_gamma_deriv:
  fixes x \<gamma> :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  shows "(Rect_gamma \<gamma> has_real_derivative dRect_gamma_dx \<gamma> x) (at x)"
proof -
  from assms have "((\<lambda>y. Max_gamma_comp \<gamma> y 0) has_real_derivative dMax_gamma_ds \<gamma> x 1 0 0) (at x)"
    using dMax_gamma_chain DERIV_const DERIV_ident
    by blast
  moreover have "dMax_gamma_ds \<gamma> x 1 0 0 = dRect_gamma_dx \<gamma> x" using gamma_gt_zero by simp
  ultimately have "((\<lambda>y. Max_gamma_comp \<gamma> y 0) has_real_derivative dRect_gamma_dx \<gamma> x) (at x)"
    using DERIV_cong by simp
  then have "((\<lambda>y. Max_gamma \<gamma> y 0) has_real_derivative dRect_gamma_dx \<gamma> x) (at x)"
    using Max_gamma_comp_eq by simp
  thus ?thesis using Rect_gamma_comp_eq by presburger
qed


theorem Lequal_gamma_chain:
  fixes f g :: "real \<Rightarrow> real" and Df Dg \<gamma> :: real
  assumes gamma_gt_zero: "\<gamma> > 0"
  and f_deriv: "(f has_real_derivative Df) (at x)"
and g_deriv: "(g has_real_derivative Dg) (at x)"
shows "((\<lambda>y. (Lequal_gamma \<gamma> (f y) (g y))) has_real_derivative (dLequal_gamma_ds \<gamma> (f x) Df (g x) Dg)) (at x)"
proof -
  from f_deriv and g_deriv have "((\<lambda>y. (f y) - (g y)) has_real_derivative (Df-Dg)) (at x)"
    using DERIV_diff by blast
  moreover have "(Rect_gamma \<gamma> has_field_derivative dRect_gamma_dx \<gamma> ((\<lambda>y. (f y) - (g y)) x)) (at ((\<lambda>y. (f y) - (g y)) x))"
    using gamma_gt_zero Rect_gamma_deriv by simp
  ultimately have 
"((\<lambda>x. Rect_gamma \<gamma> (f x - g x)) has_real_derivative dRect_gamma_dx \<gamma> (f x - g x) * (Df - Dg)) (at x)"
    using DERIV_chain2 [where ?f="(\<lambda>y. Rect_gamma \<gamma> y)" and ?g="(\<lambda>y. (f y) - (g y))"] by blast
  thus ?thesis using DERIV_cong by simp
qed

end