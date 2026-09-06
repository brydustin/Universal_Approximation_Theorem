section \<open>Section 7: the numerical examples\<close>

theory Numerical_examples
  imports Translated_Lp_Approximation "HOL-Analysis.Interval_Integral"
begin

text \<open>
  Section 7 of Costarelli and Spigler~\cite{CostarelliSpigler} (pp.191--194) gives three
  worked examples.  Its content is of two kinds, and only one of them is formal.

  \<^emph>\<open>What is verified here.\<close>  The three functions of (7.1), (7.2) and Example 7.3 are defined
  exactly as printed; the derivative \<open>f'\<close> displayed on p.192 is proved to be the derivative of
  \<open>f\<close>; each function is shown to satisfy the hypotheses of the theorem the paper invokes for
  it; and the corresponding approximation statements are obtained by instantiating those
  theorems, so that each example is exhibited as a genuine instance rather than an assertion.

  \<^emph>\<open>What is not, and cannot be, verified here.\<close>  Figures 4--12 are plots, and the reported
  relative errors -- \<open>\<bar>\<bar>G\<^sub>N f - f\<bar>\<bar>\<^sub>\<infinity>/\<bar>\<bar>f\<bar>\<bar>\<^sub>\<infinity> \<approx> 1.08 \<times> 10\<^sup>-\<^sup>1\<close> for \<open>N = 25\<close> and so on -- are
  numerical measurements of a particular computation, stated to three significant figures with
  \<open>\<approx>\<close>.  Nothing below claims them.  The same applies to the comparative remarks ("the
  approximation improves as N increases", "better in case of the logistic function"), which
  are observations about those measurements.  The sup-norm estimates \<open>\<bar>\<bar>f\<bar>\<bar>\<^sub>\<infinity> \<approx> 15.13\<close> and
  \<open>\<bar>\<bar>f'\<bar>\<bar>\<^sub>\<infinity> \<approx> 5\<close> are likewise not claimed, though the second is explained below.
\<close>

subsection \<open>Example 7.1: a smooth target and its derivative\<close>

text \<open>Equation (7.1), p.191.\<close>
(* Equation (7.1): the target of Example 7.1. *)
definition example_f :: "real \<Rightarrow> real" where
  "example_f x = (cos x ^ 2 + 2) * sin x + 2 * x + x ^ 2 / 8 + 4"

text \<open>The derivative displayed on p.192, transcribed exactly as printed.\<close>
(* Example 7.1, p.192: the printed derivative of (7.1). *)
definition example_f' :: "real \<Rightarrow> real" where
  "example_f' x = (cos x ^ 2 + 2) * cos x - 2 * sin x ^ 2 * cos x + x / 4 + 2"

(* Auxiliary for Example 7.1: the second derivative, needed for the C^2 hypothesis. *)
definition example_f'' :: "real \<Rightarrow> real" where
  "example_f'' x = - 9 * cos x ^ 2 * sin x + 1 / 4"

text \<open>
  A small bridge used three times below: a function with a real derivative at every point of
  \<open>\<real>\<close> is differentiable on \<open>UNIV\<close> in the Frechet sense that \<^const>\<open>C_k_on\<close> is phrased with.
\<close>
(* Auxiliary for Examples 7.1-7.3; not a numbered result of the paper. *)
lemma differentiable_on_UNIV_of_DERIV:
  fixes F G :: "real \<Rightarrow> real"
  assumes D: "\<And>x. (F has_real_derivative G x) (at x)"
  shows "F differentiable_on UNIV"
proof (subst differentiable_on_eq_differentiable_at[OF open_UNIV], intro ballI)
  fix x :: real
  have "(F has_derivative (*) (G x)) (at x)"
    using D[of x] unfolding has_field_derivative_def .
  then show "F differentiable at x" by (rule differentiableI)
qed

text \<open>
  The paper's displayed \<open>f'\<close> is correct.  This is the one strictly mathematical assertion in
  Section 7, and the only thing in it that a proof assistant can settle.
\<close>
(* Example 7.1, p.192: the printed formula is indeed the derivative of (7.1). *)
lemma example_f_has_derivative:
  "(example_f has_real_derivative example_f' x) (at x)"
  unfolding example_f_def example_f'_def
  by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)

(* Auxiliary for Example 7.1: the derivative operator applied to (7.1). *)
lemma deriv_example_f: "deriv example_f = example_f'"
  by (rule ext) (rule DERIV_imp_deriv[OF example_f_has_derivative])

text \<open>
  The printed \<open>f'\<close> collapses to \<open>3cos\<^sup>3x + x/4 + 2\<close>.  This is worth recording because it
  explains the paper's \<open>\<bar>\<bar>f'\<bar>\<bar>\<^sub>\<infinity> \<approx> 5\<close>: the first summand is at most \<open>3\<close>, attained at \<open>x = 0\<close>,
  where the remaining terms contribute exactly \<open>2\<close>.
\<close>
(* Auxiliary for Example 7.1: closed form of the printed derivative. *)
lemma example_f'_alt: "example_f' x = 3 * cos x ^ 3 + x / 4 + 2"
proof -
  have sq: "sin x ^ 2 = 1 - cos x ^ 2"
    using sin_cos_squared_add[of x] by algebra
  show ?thesis
    unfolding example_f'_def sq
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
qed

(* Auxiliary for Example 7.1: the second derivative of (7.1). *)
lemma example_f'_has_derivative:
  "(example_f' has_real_derivative example_f'' x) (at x)"
proof -
  have eq: "example_f' = (\<lambda>x. 3 * cos x ^ 3 + x / 4 + 2)"
    by (rule ext) (rule example_f'_alt)
  show ?thesis
    unfolding eq example_f''_def
    by (auto intro!: derivative_eq_intros
             simp: power2_eq_square power3_eq_cube algebra_simps)
qed

(* Auxiliary for Example 7.1: the derivative operator applied to the printed derivative. *)
lemma deriv_example_f': "deriv example_f' = example_f''"
  by (rule ext) (rule DERIV_imp_deriv[OF example_f'_has_derivative])

(* Auxiliary for Example 7.1: continuity of the second derivative. *)
lemma example_f''_continuous: "continuous_on UNIV example_f''"
  unfolding example_f''_def by (intro continuous_intros)

text \<open>
  Hence \<open>f \<in> C\<^sup>2\<close> on an open set containing \<open>[-5,5]\<close>, which is the hypothesis
  \<open>\<^bold>C\<^sup>n\<^sup>+\<^sup>1[a,b]\<close> of Theorem 4.1 and Corollary 6.1 at \<open>n = 1\<close>.
\<close>
(* Example 7.1: (7.1) satisfies the smoothness hypothesis of Theorem 4.1 at n = 1. *)
lemma example_f_C2: "C_k_on 2 example_f UNIV"
proof (rule C2_on_open_U_def2[OF open_UNIV])
  show "example_f differentiable_on UNIV"
    by (rule differentiable_on_UNIV_of_DERIV[OF example_f_has_derivative])
  show "deriv example_f differentiable_on UNIV"
    unfolding deriv_example_f
    by (rule differentiable_on_UNIV_of_DERIV[OF example_f'_has_derivative])
  show "continuous_on UNIV (deriv (deriv example_f))"
    unfolding deriv_example_f deriv_example_f' by (rule example_f''_continuous)
qed

(* Example 7.1: (7.1) is continuous, the hypothesis of Theorems 2.1 and 3.1. *)
lemma example_f_continuous: "continuous_on S example_f"
  unfolding example_f_def by (intro continuous_intros) simp

subsection \<open>Example 7.2: an \<open>L\<^sup>1\<close> target with jump discontinuities\<close>

text \<open>Equation (7.2), p.192.\<close>
(* Equation (7.2): the target of Example 7.2. *)
definition example_g :: "real \<Rightarrow> real" where
  "example_g x =
     (if x < - 2 then 4 / (x\<^sup>2 - 2)
      else if x < 0 then - 3
      else if x < 2 then 5 / 2
      else (3 * x + 2) / (x ^ 3 - 1))"

(* Example 7.2: (7.2) is Borel measurable, which every Lp statement about it needs. *)
lemma example_g_measurable: "example_g \<in> borel_measurable borel"
  unfolding example_g_def by measurable

text \<open>
  A single integrable majorant valid on the whole line.  Each of the four branches of (7.2) is
  dominated by \<open>16/(1+x\<^sup>2)\<close>; the constant \<open>16\<close> is forced by the branch \<open>-2 \<le> x < 0\<close>, where
  \<open>\<bar>g\<bar> = 3\<close> while the kernel is as small as \<open>16/5\<close>.  Note that the two denominators of (7.2)
  vanish at \<open>\<plusminus>\<surd>2\<close> and at \<open>1\<close>, neither of which lies in the branch that uses it, so \<open>g\<close> has no
  pole; its only discontinuities are the three jumps at \<open>-2\<close>, \<open>0\<close> and \<open>2\<close>.
\<close>
(* Auxiliary for Example 7.2: the majorant's denominator is positive, hence nonzero. *)
lemma one_plus_square_pos: "0 < 1 + x\<^sup>2" for x :: real
  by (simp add: add_pos_nonneg)

(* Auxiliary for Example 7.2: the majorant's denominator never vanishes. *)
lemma one_plus_square_nonzero: "1 + x\<^sup>2 \<noteq> 0" for x :: real
  using one_plus_square_pos[of x] by linarith

(* Auxiliary for Example 7.2: the linear estimate behind the branch x >= 2 of (7.2). *)
lemma example_g_cubic_ineq:
  fixes u v y :: real
  assumes "2 * u \<le> v" and "4 * y \<le> v" and "8 \<le> v"
  shows "3 * y + 2 + 3 * v + 2 * u \<le> 16 * (v - 1)"
  using assms by (simp add: algebra_simps)

(* Example 7.2: the majorant witnessing that (7.2) lies in L^1(R). *)
lemma example_g_bound: "\<bar>example_g x\<bar> \<le> 16 / (1 + x\<^sup>2)"
proof -
  have p: "0 < 1 + x\<^sup>2" by (rule one_plus_square_pos)
  show ?thesis
  proof (cases "x < - 2")
    case True
    have n2: "(2::real) < - x" using True by simp
    have "(2::real) * 2 < (- x) * (- x)"
      by (rule mult_strict_mono[OF n2 n2]) (use n2 in auto)
    then have x2: "4 < x\<^sup>2" by (simp add: power2_eq_square)
    have d: "0 < x\<^sup>2 - 2" using x2 by simp
    have "\<bar>example_g x\<bar> = 4 / (x\<^sup>2 - 2)" using True d by (simp add: example_g_def)
    also have "\<dots> \<le> 16 / (1 + x\<^sup>2)"
    proof -
      have "4 * (1 + x\<^sup>2) = 4 + 4 * x\<^sup>2" by (simp add: algebra_simps)
      also have "\<dots> \<le> 16 * x\<^sup>2 - 32" using x2 by linarith
      also have "\<dots> = 16 * (x\<^sup>2 - 2)" by (simp add: algebra_simps)
      finally have "4 * (1 + x\<^sup>2) \<le> 16 * (x\<^sup>2 - 2)" .
      then show ?thesis using d p by (simp add: field_simps)
    qed
    finally show ?thesis .
  next
    case False
    then have xm2: "- 2 \<le> x" by simp
    show ?thesis
    proof (cases "x < 0")
      case True
      have sq: "x\<^sup>2 \<le> 4"
      proof -
        have "- x \<le> 2" using xm2 by simp
        moreover have "0 \<le> - x" using True by simp
        ultimately have "(- x) * (- x) \<le> 2 * 2" by (intro mult_mono) auto
        then show ?thesis by (simp add: power2_eq_square)
      qed
      have "(3::real) \<le> 16 / (1 + x\<^sup>2)"
        using sq p by (simp add: field_simps)
      then show ?thesis using False True by (simp add: example_g_def)
    next
      case False
      then have x0: "0 \<le> x" by simp
      show ?thesis
      proof (cases "x < 2")
        case True
        have sq: "x\<^sup>2 \<le> 4"
        proof -
          have "x \<le> 2" using True by simp
          then have "x * x \<le> 2 * 2" using x0 by (intro mult_mono) auto
          then show ?thesis by (simp add: power2_eq_square)
        qed
        have "(5::real) / 2 \<le> 16 / (1 + x\<^sup>2)"
          using sq p by (simp add: field_simps)
        then show ?thesis using xm2 False True by (simp add: example_g_def)
      next
        case False
        then have x2: "2 \<le> x" by simp
        have sq: "4 \<le> x\<^sup>2"
        proof -
          have "2 * 2 \<le> x * x" using x2 by (intro mult_mono) auto
          then show ?thesis by (simp add: power2_eq_square)
        qed
        have cube: "4 * x \<le> x ^ 3"
        proof -
          have "4 * x \<le> x\<^sup>2 * x" using sq x0 by (simp add: mult_right_mono)
          then show ?thesis by (simp add: power3_eq_cube power2_eq_square)
        qed
        have d: "0 < x ^ 3 - 1" using cube x2 by simp
        have "\<bar>example_g x\<bar> = (3 * x + 2) / (x ^ 3 - 1)"
          using xm2 \<open>\<not> x < 0\<close> False d x2 by (simp add: example_g_def)
        also have "\<dots> \<le> 16 / (1 + x\<^sup>2)"
        proof -
          have c1: "2 * x\<^sup>2 \<le> x ^ 3"
          proof -
            have "2 * x\<^sup>2 \<le> x * x\<^sup>2" using x2 by (simp add: mult_right_mono)
            then show ?thesis by (simp add: power3_eq_cube power2_eq_square)
          qed
          have c3: "8 \<le> x ^ 3" using cube x2 by linarith
          have "(3 * x + 2) * (1 + x\<^sup>2) \<le> 16 * (x ^ 3 - 1)"
          proof -
            have eq: "(3 * x + 2) * (1 + x\<^sup>2) = 3 * x + 2 + 3 * (x ^ 3) + 2 * x\<^sup>2"
              by (simp add: algebra_simps power3_eq_cube power2_eq_square)
            show ?thesis unfolding eq by (rule example_g_cubic_ineq[OF c1 cube c3])
          qed
          then show ?thesis using d p by (simp add: field_simps)
        qed
        finally show ?thesis .
      qed
    qed
  qed
qed

text \<open>
  The majorant is integrable over the whole line, by the fundamental theorem of calculus for
  improper interval integrals with antiderivative \<open>16 arctan\<close>, whose limits at \<open>\<plusminus>\<infinity>\<close> are
  \<open>\<plusminus>8\<pi>\<close>.
\<close>
(* Auxiliary for Example 7.2: the Cauchy kernel is Lebesgue integrable on R. *)
lemma integrable_cauchy_kernel: "integrable lborel (\<lambda>x::real. 16 / (1 + x\<^sup>2))"
proof -
  have bot: "((\<lambda>x::real. 16 * arctan x) \<longlongrightarrow> - (16 * (pi / 2))) at_bot"
  proof -
    have "((\<lambda>x::real. 16 * arctan x) \<longlongrightarrow> 16 * (- (pi / 2))) at_bot"
      by (rule tendsto_mult[OF tendsto_const tendsto_arctan_at_bot])
    then show ?thesis by simp
  qed
  have top: "((\<lambda>x::real. 16 * arctan x) \<longlongrightarrow> 16 * (pi / 2)) at_top"
    by (rule tendsto_mult[OF tendsto_const tendsto_arctan_at_top])
  have si: "set_integrable lborel (einterval (- \<infinity>) \<infinity>) (\<lambda>x::real. 16 / (1 + x\<^sup>2))"
  proof (rule interval_integral_FTC_nonneg(1)
      [where F = "\<lambda>x. 16 * arctan x" and A = "- (16 * (pi / 2))" and B = "16 * (pi / 2)"])
    show "(- \<infinity>::ereal) < \<infinity>" by simp
    show "\<And>x. - \<infinity> < ereal x \<Longrightarrow> ereal x < \<infinity> \<Longrightarrow>
            DERIV (\<lambda>x. 16 * arctan x) x :> 16 / (1 + x\<^sup>2)"
      by (auto intro!: derivative_eq_intros simp: field_simps)
    show "\<And>x. - \<infinity> < ereal x \<Longrightarrow> ereal x < \<infinity> \<Longrightarrow> isCont (\<lambda>x::real. 16 / (1 + x\<^sup>2)) x"
      by (intro continuous_intros) (simp add: one_plus_square_nonzero)
    show "AE x in lborel. - \<infinity> < ereal x \<longrightarrow> ereal x < \<infinity> \<longrightarrow> 0 \<le> 16 / (1 + x\<^sup>2)"
      by (intro AE_I2 impI) (simp add: add_pos_nonneg)
    show "(((\<lambda>x. 16 * arctan x) \<circ> real_of_ereal) \<longlongrightarrow> - (16 * (pi / 2))) (at_right (- \<infinity>))"
      using bot by (simp add: ereal_tendsto_simps)
    show "(((\<lambda>x. 16 * arctan x) \<circ> real_of_ereal) \<longlongrightarrow> 16 * (pi / 2)) (at_left \<infinity>)"
      using top by (simp add: ereal_tendsto_simps)
  qed
  have uni: "einterval (- \<infinity>) (\<infinity>::ereal) = (UNIV :: real set)"
    by (auto simp: einterval_iff)
  show ?thesis using si unfolding uni set_integrable_def by simp
qed

(* Example 7.2: (7.2) belongs to L^1(R), as the paper asserts when introducing it. *)
theorem example_g_L1: "integrable lborel example_g"
proof (rule Bochner_Integration.integrable_bound[OF integrable_cauchy_kernel])
  show "example_g \<in> borel_measurable lborel"
    using example_g_measurable by simp
  show "AE x in lborel. norm (example_g x) \<le> norm (16 / (1 + x\<^sup>2))"
  proof (intro AE_I2)
    fix x :: real
    have "0 \<le> 16 / (1 + x\<^sup>2)" by (simp add: add_pos_nonneg)
    then show "norm (example_g x) \<le> norm (16 / (1 + x\<^sup>2))"
      using example_g_bound[of x] by simp
  qed
qed

(* Example 7.2: (7.2) is in L^p of the approximation interval, the hypothesis of Theorem 3.2. *)
lemma example_g_Lp_integrable:
  assumes p: "1 \<le> p"
  shows "integrable (lebesgue_on {- 5..5}) (\<lambda>x. \<bar>example_g x\<bar> powr p)"
proof -
  have lm: "{- 5..(5::real)} \<in> lmeasurable"
    by (metis cbox_interval lmeasurable_cbox)
  have fin: "finite_measure (lebesgue_on {- 5..(5::real)})"
    using finite_measure_lebesgue_on[OF lm] .
  have gm: "example_g \<in> borel_measurable (lebesgue_on {- 5..5})"
    by (rule borel_measurable_lebesgue_onI[OF example_g_measurable])
  show ?thesis
  proof (rule finite_measure.integrable_const_bound[OF fin, where B = "16 powr p"])
    show "(\<lambda>x. \<bar>example_g x\<bar> powr p) \<in> borel_measurable (lebesgue_on {- 5..5})"
      using gm by measurable
    show "AE x in lebesgue_on {- 5..(5::real)}. norm (\<bar>example_g x\<bar> powr p) \<le> 16 powr p"
    proof (rule AE_I2)
      fix x assume "x \<in> space (lebesgue_on {- 5..(5::real)})"
      have pp: "0 < 1 + x\<^sup>2" by (simp add: add_pos_nonneg)
      have "\<bar>example_g x\<bar> \<le> 16 / (1 + x\<^sup>2)" by (rule example_g_bound)
      also have "\<dots> \<le> 16" by (subst pos_divide_le_eq[OF pp]) simp
      finally have "\<bar>example_g x\<bar> \<le> 16" .
      then have "\<bar>example_g x\<bar> powr p \<le> 16 powr p"
        using p by (intro powr_mono2) auto
      then show "norm (\<bar>example_g x\<bar> powr p) \<le> 16 powr p" by simp
    qed
  qed
qed

subsection \<open>Example 7.3: a bivariate target\<close>

text \<open>
  Example 7.3, p.193.  The paper's \<open>h : [-4,4] \<times> [-4,4] \<rightarrow> \<real>\<close> is rendered on
  \<open>(real, bool) vec\<close>, whose index type has exactly two elements, so that the box
  \<open>{z. \<forall>r. z $ r \<in> {-4..4}}\<close> is the paper's square; \<open>x\<close> is the \<open>True\<close> component and \<open>y\<close> the
  \<open>False\<close> one.

  The last summand's denominator looks as though it could vanish, but the first term is an
  \<^emph>\<open>even\<close> power and the second is an exponential, so the denominator is at least \<open>1/100\<close>
  everywhere and \<open>h\<close> is continuous on all of \<open>\<real>\<^sup>2\<close>, not merely on the square.
\<close>
(* Example 7.3, p.193: the bivariate target, with x the True and y the False component. *)
definition example_h :: "(real, bool) vec \<Rightarrow> real" where
  "example_h z =
     ((z $ False) ^ 4 - 2 * (z $ False)) * sin (z $ True)
      - (z $ True) * (z $ False) ^ 3
      + (z $ True) / 3
      + 1 / ((z $ True) ^ 16 / 30 + exp (- 3 * \<bar>z $ False\<bar>) / 50 + 1 / 100)"

(* Auxiliary for Example 7.3: the denominator of the last summand never vanishes. *)
lemma example_h_denom_pos:
  fixes z :: "(real, bool) vec"
  shows "0 < (z $ True) ^ 16 / 30 + exp (- 3 * \<bar>z $ False\<bar>) / 50 + 1 / 100"
proof -
  have "(0::real) \<le> ((z $ True) ^ 8)\<^sup>2" by simp
  then have "0 \<le> (z $ True) ^ 16"
    by (simp add: power_mult[symmetric])
  then have t1: "0 \<le> (z $ True) ^ 16 / 30" by simp
  have t2: "0 < exp (- 3 * \<bar>z $ False\<bar>) / 50" by simp
  have t3: "(0::real) < 1 / 100" by simp
  from t1 t2 t3 show ?thesis by linarith
qed

(* Auxiliary for Example 7.3: the same denominator, in the form the division rule needs. *)
lemma example_h_denom_nonzero:
  fixes z :: "(real, bool) vec"
  shows "(z $ True) ^ 16 / 30 + exp (- 3 * \<bar>z $ False\<bar>) / 50 + 1 / 100 \<noteq> 0"
  using example_h_denom_pos[of z] by linarith

(* Auxiliary for Example 7.3: each coordinate projection is continuous. *)
lemma continuous_on_vec_component:
  "continuous_on S (\<lambda>z :: (real, 'n::finite) vec. z $ i)"
  by (rule linear_continuous_on[OF bounded_linear_vec_nth])

(* Example 7.3: the target is continuous, the hypothesis of Theorems 5.1 and 5.3. *)
lemma example_h_continuous: "continuous_on S example_h"
  unfolding example_h_def
  by (intro continuous_intros continuous_on_vec_component)
     (use example_h_denom_nonzero in auto)

subsection \<open>The examples as instances of the theorems\<close>

text \<open>
  The logistic activation of Section 6, used throughout Section 7, satisfies everything the
  theorems ask of \<open>\<sigma>\<close>.
\<close>
(* Auxiliary for Section 7: continuity of the logistic activation. *)
lemma sigmoid_continuous_UNIV: "continuous_on UNIV sigmoid"
  using smooth_sigmoid[unfolded smooth_on_def, rule_format, of 0]
  by (simp add: C0_on_def)

(* Auxiliary for Section 7: the logistic activation is Borel measurable. *)
lemma sigmoid_measurable: "sigmoid \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI[OF sigmoid_continuous_UNIV])

(* Auxiliary for Example 7.1: the C^2 fact in the successor form the theorems match on. *)
lemma example_f_C_Suc1: "C_k_on (Suc 1) example_f UNIV"
  using example_f_C2 by (simp add: numeral_2_eq_2)

text \<open>
  Example 7.1, first part (Figs. 4--6): Theorem 2.1 applies to (7.1) on \<open>[-5,5]\<close>.
\<close>
(* Example 7.1: Theorem 2.1 instantiated at (7.1) with the logistic activation. *)
corollary example_71_uniform_approximation:
  assumes e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Sup ((\<lambda>x. \<bar>G_network sigmoid example_f (- 5) 5 N w x - example_f x\<bar>) ` {- 5..5}) < e"
  by (rule sigmoidal_uniform_approximation_sup
        [OF sigmoid_is_sigmoidal sigmoid_is_bounded_function _ example_f_continuous e]) simp

text \<open>
  Example 7.1, second part (Fig. 7): Corollary 6.1 applies, so one \<open>N\<close> and the prescribed
  logistic weight approximate (7.1) and its derivative at once.  The second conclusion is
  stated against \<^const>\<open>example_f'\<close>, the formula printed on p.192, which
  \<open>deriv_example_f\<close> identifies with \<open>deriv example_f\<close>.
\<close>
(* Example 7.1: Corollary 6.1 instantiated at (7.1) on [-5,5] with n = 1. *)
corollary example_71_joint_approximation:
  assumes e: "0 < e" and d: "0 < delta"
  shows "\<exists>N. 1 + 3 < N \<and> 0 < logistic_paper_weight (- 5) 5 delta N \<and>
      Sup ((\<lambda>x. \<bar>G_network sigmoid example_f (- 5) 5 N
             (logistic_paper_weight (- 5) 5 delta N) x - example_f x\<bar>) ` {- 5..5}) < e \<and>
      Sup ((\<lambda>x. \<bar>Gj_network sigmoid example_f (unif_part (- 5) 5 N) ((5 - - 5) / real N) N 1
             (logistic_paper_weight (- 5) 5 delta N) x - example_f' x\<bar>) ` {- 5..5}) < e"
proof -
  have ab: "(- 5::real) < 5" by simp
  have key: "\<exists>N. 1 + 3 < N \<and> 0 < logistic_paper_weight (- 5) 5 delta N \<and>
      Sup ((\<lambda>x. \<bar>G_network sigmoid example_f (- 5) 5 N
             (logistic_paper_weight (- 5) 5 delta N) x - example_f x\<bar>) ` {- 5..5}) < e \<and>
      (\<forall>j\<in>{1..1}. Sup ((\<lambda>x. \<bar>Gj_network sigmoid example_f (unif_part (- 5) 5 N)
             ((5 - - 5) / real N) N j (logistic_paper_weight (- 5) 5 delta N) x
             - (deriv ^^ j) example_f x\<bar>) ` {- 5..5}) < e)"
    by (rule logistic_paper_joint_approximation[OF ab example_f_C_Suc1 subset_UNIV _ e d]) simp
  show ?thesis using key by (simp add: deriv_example_f)
qed

text \<open>
  Example 7.2 (Figs. 8--10): the constructive form of Theorem 3.2 applies to (7.2), so the
  network approximating it is the one whose coefficients are the mollifier integrals of (3.4)
  -- which is exactly the family \<open>G\<^sub>N(\<rho>\<^sub>n * g)\<close> for the zero extension of \<open>g\<close> the paper plots.
\<close>
(* Example 7.2: the constructive Theorem 3.2 instantiated at (7.2) on [-5,5]. *)
corollary example_72_mollifier_approximation:
  assumes p: "1 \<le> p" and e: "0 < e"
  shows "\<exists>K>0. \<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {- 5..5})
      (\<lambda>x. mollifier_network sigmoid example_g (- 5) 5 k N w x - example_g x) < ennreal e"
proof -
  have ab: "(- 5::real) < 5" by simp
  have gm: "example_g \<in> borel_measurable (lebesgue_on {- 5..5})"
    by (rule borel_measurable_lebesgue_onI[OF example_g_measurable])
  show ?thesis
    by (rule mollifier_approximation[OF sigmoid_is_sigmoidal sigmoid_is_bounded_function
          sigmoid_measurable ab p gm example_g_Lp_integrable[OF p] e])
qed

text \<open>
  Example 7.3 (Figs. 11--12): Theorem 5.1 applies to \<open>h\<close> on the square, for either choice of
  the distinguished coordinate -- the paper's (5.1) and the transposed (5.3) of Remark 5.2.
\<close>
(* Example 7.3: Theorem 5.1 instantiated at the bivariate target on [-4,4]^2. *)
corollary example_73_uniform_approximation:
  fixes r0 :: bool
  assumes e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Sup ((\<lambda>z. \<bar>multivariate_network sigmoid example_h r0 (unif_part (- 4) 4 N) N w z
              - example_h z\<bar>) ` {z. \<forall>r. z $ r \<in> {- 4..4}}) < e"
  by (rule multivariate_uniform_approximation_sup
        [OF sigmoid_is_sigmoidal sigmoid_is_bounded_function _ example_h_continuous e]) simp

end
