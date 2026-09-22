section \<open>Real analyticity of the logistic function\<close>

theory Sigmoid_Analytic
  imports Sigmoid_Definition "Real_and_Complex_Analytic.Complex_Analytic"
begin

text \<open>
  The logistic function is real-analytic on the whole line.  Because \<^const>\<open>sigmoid\<close> is
  defined at an arbitrary \<open>real_normed_field\<close> that is also a Banach space, the holomorphic
  extension required by \<^const>\<open>has_holo_extension_at\<close> is \<^emph>\<open>the same constant\<close> read at type
  \<^typ>\<open>complex\<close>; no separate complex version is introduced.

  The radius is \<open>\<pi>\<close>, and that is sharp: the poles of \<open>exp z / (1 + exp z)\<close> are exactly the
  points where \<open>exp z = -1\<close>, i.e. \<open>z = i\<pi>(2k+1)\<close>, all of which are purely imaginary and hence
  at distance \<open>\<pi>\<close> from every point of the real axis.

  Smoothness (\<open>smooth_sigmoid\<close> in theory \<open>Derivative_Identities_Smoothness\<close>) is obtained there
  from the derivative formula; the route below is independent and also yields it.
\<close>

(* Auxiliary: the denominator of the logistic function has no zero in the strip |Im z| < pi. *)
lemma sigmoid_denom_nonzero:
  fixes z :: complex
  assumes "\<bar>Im z\<bar> < pi"
  shows "1 + exp z \<noteq> 0"
proof
  assume "1 + exp z = 0"
  hence e: "exp z = -1" by (simp add: add.commute eq_neg_iff_add_eq_0)
  have "exp (Re z) * sin (Im z) = Im (exp z)" by (simp add: Im_exp)
  also have "\<dots> = 0" using e by simp
  finally have "sin (Im z) = 0" by simp
  hence "Im z = 0" using assms by (simp add: sin_eq_0_pi abs_less_iff)
  hence "Re (exp z) = exp (Re z)" by (simp add: Re_exp)
  with e have "exp (Re z) = -1" by simp
  thus False using exp_gt_zero [of "Re z"] by simp
qed

(* Auxiliary: every point of the pi-ball about a real centre lies in that strip. *)
lemma Im_small_in_ball:
  fixes z :: complex
  assumes "z \<in> ball (complex_of_real c) pi"
  shows "\<bar>Im z\<bar> < pi"
proof -
  have "\<bar>Im z\<bar> = \<bar>Im (z - complex_of_real c)\<bar>" by simp
  also have "\<dots> \<le> cmod (z - complex_of_real c)" by (rule abs_Im_le_cmod)
  also have "\<dots> < pi" using assms by (simp add: dist_norm norm_minus_commute)
  finally show ?thesis .
qed

(* The logistic function, read at type complex, is holomorphic on every pi-ball about a real point. *)
lemma sigmoid_holomorphic:
  "(sigmoid :: complex \<Rightarrow> complex) holomorphic_on ball (complex_of_real c) pi"
  unfolding sigmoid_def
  by (intro holomorphic_intros)
     (auto simp: sigmoid_denom_nonzero Im_small_in_ball)

(* The complex reading restricts to the real one along the embedding. *)
lemma sigmoid_of_real:
  "sigmoid (complex_of_real x) = complex_of_real (sigmoid x)"
  by (simp add: sigmoid_def exp_of_real)

(* The real logistic function extends holomorphically about every real point. *)
lemma sigmoid_has_holo_extension: "has_holo_extension_at sigmoid c"
  unfolding has_holo_extension_at_def
  using sigmoid_holomorphic sigmoid_of_real pi_gt_zero by blast

(* The logistic function is real-analytic on the whole line. *)
theorem sigmoid_real_analytic: "real_analytic_on (sigmoid::real \<Rightarrow> real) UNIV"
  by (simp add: real_analytic_on_1d_iff real_analytic_at_1d_iff_holo_extension
                sigmoid_has_holo_extension)

(* Analyticity recovers smoothness, independently of the derivative formula. *)
corollary sigmoid_Cinfinity: "Cinfinity_on (sigmoid::real \<Rightarrow> real) UNIV"
  by (rule real_analytic_imp_Cinfinity [OF sigmoid_real_analytic])

corollary "Ck_on k (sigmoid::real \<Rightarrow> real) UNIV"
    using sigmoid_Cinfinity by (rule Cinfinity_on_imp_Ck_on)

end
