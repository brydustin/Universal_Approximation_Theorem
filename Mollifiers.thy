section \<open>The mollifier of equation (3.3) and its approximate identity\<close>

theory Mollifiers
  imports Lp_Density Lp_Restriction "Smooth_Manifolds.Bump_Function"
begin

text \<open>
  Costarelli and Spigler prove Theorems 3.2 and 5.4 by mollifying the target: the smooth
  comparison function is \<open>convolution (mollifier k) (zero_extension S f)\<close>, the convolution of \<open>f\<close> extended by zero outside its
  domain (equations (3.1)/(5.4)) with the normalized scaled bump of equation (3.3).  This
  theory builds exactly that object and proves the properties the paper uses.

  Everything is stated over \<open>'a::euclidean_space\<close>, so the same construction serves the
  one-dimensional Theorem 3.2 at \<^typ>\<open>real\<close> and the multivariate Theorem 5.4 at
  \<open>(real,'n) vec\<close>; the radial extension described after Theorem 5.4 is the same formula read
  at the larger type.  The seed is AFP \<open>Smooth_Manifolds\<close>'s \<open>Bump_Function.f\<close>, from which
  \<open>mollifier_bump\<close> is the paper's \<open>exp(1/(inner x x-1))\<close> profile and \<open>mollifier\<close>
  the normalized family with support shrinking as \<open>k \<rightarrow> \<infinity>\<close>.

  The results proved here are: normalization \<open>\<integral>\<rho>\<^sub>k = 1\<close>, the \<open>L\<^sup>p\<close> contraction
  \<open>\<bar>\<bar>\<rho>\<^sub>k*g\<bar>\<bar>\<^sub>p \<le> \<bar>\<bar>g\<bar>\<bar>\<^sub>p\<close>, and approximate-identity convergence
  \<open>\<rho>\<^sub>k*g \<rightarrow> g\<close> in \<open>L\<^sup>p\<close> -- first for continuous compactly supported \<open>g\<close>, then for an
  arbitrary \<open>L\<^sup>p\<close> target, locally and on the whole space.  \<open>mollified_target\<close> is the
  paper's smoothed target itself, and \<open>mollified_target_Lp\<close> collects the three facts the
  approximation theorems consume: it is continuous everywhere, the error \<open>\<bar>\<rho>\<^sub>k*f - f\<bar>\<^sup>p\<close>
  is integrable, and its \<open>L\<^sup>p\<close> seminorm tends to \<open>0\<close>.

  Density of continuous functions (\<^file>\<open>Lp_Density.thy\<close>) is used once, inside
  \<open>compact_continuous_dense\<close>, to produce compactly supported continuous comparison functions;
  it is not an alternative to this construction but an ingredient of it.
\<close>

(* Equation (3.3); radial extension described after Theorem 5.4. *)
definition mollifier_bump :: "'a::euclidean_space \<Rightarrow> real" where
  "mollifier_bump x = Bump_Function.f (1 - inner x x)"

(* Equation (3.3): the literal exponential formula, with zero outside the unit ball. *)
lemma mollifier_bump_formula:
  fixes x :: "'a::euclidean_space"
  shows "mollifier_bump x = (if norm x < 1 then exp (1 / (norm x ^ 2 - 1)) else 0)"
proof -
  have sq: "inner x x = norm x ^ 2" by (simp add: power2_norm_eq_inner)
  have lt: "norm x ^ 2 < 1 \<longleftrightarrow> norm x < 1"
    by (simp add: abs_square_less_1)
  show ?thesis unfolding mollifier_bump_def Bump_Function.f_def sq
    using lt by (simp add: divide_simps)
qed

(* Auxiliary for (3.3)-(3.4) and Theorem 5.4: smoothness of the exact paper bump. *)
lemma mollifier_bump_smooth:
  "k-smooth_on UNIV (mollifier_bump :: 'a::euclidean_space \<Rightarrow> real)"
  unfolding mollifier_bump_def
  by (intro Bump_Function.f_compose_smooth_on smooth_on_minus smooth_on_const
      smooth_on_inner smooth_on_id) auto

(* Auxiliary for (3.3)-(3.4): continuity of the exact paper bump. *)
lemma mollifier_bump_continuous:
  "continuous_on UNIV (mollifier_bump :: 'a::euclidean_space \<Rightarrow> real)"
  by (rule smooth_on_imp_continuous_on[OF mollifier_bump_smooth[of 0]])

(* Auxiliary for (3.3)-(3.4): measurability of the exact paper bump. *)
lemma mollifier_bump_measurable [measurable]:
  "(mollifier_bump :: 'a::euclidean_space \<Rightarrow> real) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI[OF mollifier_bump_continuous])

(* Auxiliary for (3.3)-(3.4): nonnegativity and the support condition. *)
lemma mollifier_bump_nonneg:
  fixes x :: "'a::euclidean_space"
  shows "0 \<le> mollifier_bump x"
  unfolding mollifier_bump_def by (rule Bump_Function.f_nonneg)

(* Auxiliary for (3.3)-(3.4): the support lies in the closed unit ball. *)
lemma mollifier_bump_zero:
  fixes x :: "'a::euclidean_space"
  assumes "1 \<le> norm x"
  shows "mollifier_bump x = 0"
  using assms by (simp add: mollifier_bump_formula)

(* Auxiliary for (3.3)-(3.4): positivity in the open unit ball. *)
lemma mollifier_bump_pos:
  fixes x :: "'a::euclidean_space"
  assumes "norm x < 1"
  shows "0 < mollifier_bump x"
  using assms by (simp add: mollifier_bump_formula)

(* Auxiliary for (3.3)-(3.4): a uniform upper bound for integration. *)
lemma mollifier_bump_le_one:
  fixes x :: "'a::euclidean_space"
  shows "mollifier_bump x \<le> 1"
  unfolding mollifier_bump_def Bump_Function.f_def
  by (auto intro: exp_le_one_iff[THEN iffD2])

(* Auxiliary for (3.3)-(3.4): integrability of the compactly supported bump. *)
lemma mollifier_bump_integrable:
  "integrable lborel (mollifier_bump :: 'a::euclidean_space \<Rightarrow> real)"
proof -
  have ind: "integrable lborel (indicator (cball (0::'a) 1) :: 'a \<Rightarrow> real)"
    by (rule integrable_real_indicator) (simp, rule emeasure_lborel_cball_finite)
  show ?thesis
    by (rule Bochner_Integration.integrable_bound[OF ind])
       (measurable, intro AE_I2,
        auto simp: indicator_def mollifier_bump_nonneg intro: mollifier_bump_le_one
        dest!: not_le_imp_less[THEN less_imp_le, THEN mollifier_bump_zero])
qed

(* Normalizing constant following Equation (3.4), also in the paragraph after Theorem 5.4. *)
definition mollifier_bump_mass :: "'a::euclidean_space itself \<Rightarrow> real" where
  "mollifier_bump_mass T = (\<integral>(x::'a). mollifier_bump x \<partial>lborel)"

(* Auxiliary for (3.4): the normalization denominator is strictly positive. *)
lemma mollifier_bump_mass_pos:
  "0 < mollifier_bump_mass (TYPE('a::euclidean_space))"
proof -
  have nn: "AE x::'a in lborel. 0 \<le> mollifier_bump x"
    by (intro AE_I2 mollifier_bump_nonneg)
  have nonneg: "0 \<le> mollifier_bump_mass TYPE('a)"
    unfolding mollifier_bump_mass_def by (rule integral_nonneg_AE[OF nn])
  have nz: "mollifier_bump_mass TYPE('a) \<noteq> 0"
  proof
    assume zero: "mollifier_bump_mass TYPE('a) = 0"
    have ae: "AE x::'a in lborel. mollifier_bump x = 0"
      using zero integral_nonneg_eq_0_iff_AE[OF mollifier_bump_integrable nn]
      unfolding mollifier_bump_mass_def by simp
    have outside: "AE x::'a in lborel. x \<notin> ball 0 1"
      using ae by eventually_elim (auto simp: dest: mollifier_bump_pos)
    have "emeasure lborel (ball (0::'a) 1) = 0"
      using emeasure_eq_0_AE[OF outside] by (simp add: ball_def)
    then have "measure lborel (ball (0::'a) 1) = 0" by (simp add: measure_def)
    moreover have "0 < measure lborel (ball (0::'a) 1)"
      by (rule content_ball_pos) simp
    ultimately show False by simp
  qed
  show ?thesis using nonneg nz by linarith
qed

(* Equation (3.4); k^dimension scaling is the extension after Theorem 5.4. *)
definition mollifier :: "nat \<Rightarrow> 'a::euclidean_space \<Rightarrow> real" where
  "mollifier k x =
    real k ^ DIM('a) * mollifier_bump (real k *\<^sub>R x) / mollifier_bump_mass TYPE('a)"

(* Equation (3.2) and the unnumbered convolution in the proof of Theorem 5.4. *)
definition convolution ::
  "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "convolution rho f x = (\<integral>y. rho (x-y) * f y \<partial>lborel)"

(* Auxiliary for (3.4): smoothness of every scaled normalized kernel. *)
lemma mollifier_smooth:
  "n-smooth_on UNIV (mollifier k :: 'a::euclidean_space \<Rightarrow> real)"
proof -
  have lin: "n-smooth_on UNIV (\<lambda>x::'a. real k *\<^sub>R x)"
    by (rule bounded_linear.smooth_on[OF bounded_linear_scaleR_right])
  have comp: "n-smooth_on UNIV (\<lambda>x::'a. mollifier_bump (real k *\<^sub>R x))"
    using smooth_on_compose[OF mollifier_bump_smooth lin open_UNIV open_UNIV subset_UNIV]
    by (simp add: o_def)
  then show ?thesis unfolding mollifier_def
    by (intro smooth_on_divide smooth_on_mult smooth_on_const comp)
       (use mollifier_bump_mass_pos[where 'a='a] in auto)
qed

(* Auxiliary for (3.4): continuity of every scaled normalized kernel. *)
lemma mollifier_continuous:
  "continuous_on UNIV (mollifier k :: 'a::euclidean_space \<Rightarrow> real)"
  by (rule smooth_on_imp_continuous_on[OF mollifier_smooth[of 0]])

(* Auxiliary for (3.4): measurability of every scaled normalized kernel. *)
lemma mollifier_measurable [measurable]:
  "(mollifier k :: 'a::euclidean_space \<Rightarrow> real) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI[OF mollifier_continuous])

(* Auxiliary for (3.4): nonnegative kernels. *)
lemma mollifier_nonneg:
  fixes x :: "'a::euclidean_space"
  shows "0 \<le> mollifier k x"
  unfolding mollifier_def
  by (intro divide_nonneg_pos mult_nonneg_nonneg mollifier_bump_nonneg mollifier_bump_mass_pos) simp

(* Auxiliary for (3.4): the paper's exact support radius 1/k. *)
lemma mollifier_support:
  fixes x :: "'a::euclidean_space"
  assumes k: "0 < k" and x: "1 / real k \<le> norm x"
  shows "mollifier k x = 0"
proof -
  have "1 \<le> norm (real k *\<^sub>R x)" using k x by (simp add: field_simps)
  then show ?thesis unfolding mollifier_def
    by (simp add: mollifier_bump_zero)
qed

(* Auxiliary for (3.4): finite bound for each kernel, without a bound on the target. *)
lemma mollifier_bound:
  fixes x :: "'a::euclidean_space"
  shows "mollifier k x \<le> real k ^ DIM('a) / mollifier_bump_mass TYPE('a)"
  unfolding mollifier_def
  by (intro divide_right_mono)
     (use mult_left_mono[OF mollifier_bump_le_one, of "real k ^ DIM('a)"]
       mollifier_bump_mass_pos[where 'a='a] in auto)

(* Auxiliary for (3.4): integrability of the scaled bump. *)
lemma mollifier_bump_scaled_integrable:
  fixes k :: nat
  assumes k: "0 < k"
  shows "integrable lborel (\<lambda>x::'a::euclidean_space. mollifier_bump (real k *\<^sub>R x))"
proof (rule integrableI_bounded_set[where A="cball 0 (1 / real k)" and B=1])
  show "cball (0::'a) (1 / real k) \<in> sets lborel" by simp
  show "(\<lambda>x::'a. mollifier_bump (real k *\<^sub>R x)) \<in> borel_measurable lborel"
    by measurable
  show "emeasure lborel (cball (0::'a) (1 / real k)) < \<infinity>"
    by (rule emeasure_lborel_cball_finite)
  show "AE x::'a in lborel. x \<in> cball 0 (1 / real k) \<longrightarrow>
      norm (mollifier_bump (real k *\<^sub>R x)) \<le> 1"
    by (intro AE_I2) (simp add: mollifier_bump_nonneg mollifier_bump_le_one)
  show "AE x::'a in lborel. x \<notin> cball 0 (1 / real k) \<longrightarrow>
      mollifier_bump (real k *\<^sub>R x) = 0"
  proof (intro AE_I2 impI)
    fix x::'a assume "x \<notin> cball 0 (1 / real k)"
    then have "1 \<le> norm (real k *\<^sub>R x)" using k by (simp add: field_simps)
    then show "mollifier_bump (real k *\<^sub>R x) = 0" by (rule mollifier_bump_zero)
  qed
qed

(* Auxiliary for (3.4): integrability of each normalized kernel. *)
lemma mollifier_integrable:
  fixes k :: nat
  assumes "0 < k"
  shows "integrable lborel (mollifier k :: 'a::euclidean_space \<Rightarrow> real)"
  unfolding mollifier_def
  using mollifier_bump_scaled_integrable[OF assms, where 'a='a] by simp

(* Equation (3.4): the normalized kernel has total integral one. *)
lemma mollifier_integral_one:
  fixes k :: nat
  assumes k: "0 < k"
  shows "(\<integral>(x::'a::euclidean_space). mollifier k x \<partial>lborel) = 1"
proof -
  have nz: "real k \<noteq> 0" using k by simp
  have scaling: "mollifier_bump_mass TYPE('a) =
      real k ^ DIM('a) * (\<integral>(x::'a). mollifier_bump (real k *\<^sub>R x) \<partial>lborel)"
    using lborel_integral_scaleR_euclidean[OF nz mollifier_bump_integrable, where 'a='a]
    by (simp add: mollifier_bump_mass_def)
  have eq: "(\<integral>(x::'a). mollifier k x \<partial>lborel) =
      (real k ^ DIM('a) * (\<integral>(x::'a). mollifier_bump (real k *\<^sub>R x) \<partial>lborel)) /
      mollifier_bump_mass TYPE('a)"
    unfolding mollifier_def
    by (simp only: integral_divide_zero integral_mult_right_zero)
  have massnz: "mollifier_bump_mass TYPE('a) \<noteq> 0"
    using mollifier_bump_mass_pos[where 'a='a] by simp
  show ?thesis using eq unfolding scaling[symmetric] by (simp add: massnz)
qed

(* Auxiliary for Theorems 3.2 and 5.4: bounded kernels can convolve arbitrary L1 targets. *)
lemma bounded_kernel_integrable:
  fixes rho f :: "'a::euclidean_space \<Rightarrow> real"
  assumes rm: "rho \<in> borel_measurable borel"
    and rb: "\<And>x. \<bar>rho x\<bar> \<le> C" and fi: "integrable lborel f"
  shows "integrable lborel (\<lambda>y. rho (x-y) * f y)"
proof -
  have fm: "f \<in> borel_measurable borel" using fi by measurable
  have C: "0 \<le> C" using rb[of 0] by linarith
  have dom: "integrable lborel (\<lambda>y. C * \<bar>f y\<bar>)" using fi by simp
  show ?thesis
    by (rule Bochner_Integration.integrable_bound[OF dom])
       (use rm fm in measurable, intro AE_I2,
        use rb C in \<open>auto simp: abs_mult intro: mult_right_mono\<close>)
qed

(* Auxiliary for (3.2) and Theorem 5.4: continuity after mollification, no bounded-target premise. *)
lemma bounded_kernel_convolution_continuous:
  fixes rho f :: "'a::euclidean_space \<Rightarrow> real"
  assumes rc: "continuous_on UNIV rho" and rb: "\<And>x. \<bar>rho x\<bar> \<le> C"
    and fi: "integrable lborel f"
  shows "continuous_on UNIV (convolution rho f)"
proof (rule continuous_on_sequentiallyI)
  fix u::"nat \<Rightarrow> 'a" and x::'a assume ux: "u \<longlonglongrightarrow> x"
  have rm: "rho \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF rc])
  have fm: "f \<in> borel_measurable borel" using fi by measurable
  have rcont: "\<And>z. isCont rho z"
    using rc by (simp add: continuous_on_eq_continuous_at)
  have dom: "integrable lborel (\<lambda>y. C * \<bar>f y\<bar>)" using fi by simp
  have lim: "AE y in lborel. (\<lambda>n. rho (u n-y) * f y) \<longlonglongrightarrow> rho (x-y) * f y"
    by (intro AE_I2 tendsto_mult isCont_tendsto_compose[OF rcont] tendsto_diff ux tendsto_const)
  have bound: "\<And>n. AE y in lborel. norm (rho (u n-y) * f y) \<le> C * \<bar>f y\<bar>"
    by (intro AE_I2) (simp add: abs_mult mult_right_mono rb)
  show "(\<lambda>n. convolution rho f (u n)) \<longlonglongrightarrow> convolution rho f x"
    unfolding convolution_def
    by (rule integral_dominated_convergence[OF _ _ dom lim bound];
        use rm fm in measurable)
qed

(* Auxiliary for Theorems 3.2 and 5.4: Jensen's power estimate for a normalized finite measure. *)
lemma normalized_integral_power_bound:
  fixes M :: "'a measure" and f :: "'a \<Rightarrow> real" and p :: real
  assumes fin: "finite_measure M" and mass: "measure M (space M) = 1"
    and p: "1 \<le> p" and fi: "integrable M f"
    and fpi: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "\<bar>integral\<^sup>L M f\<bar> powr p \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
proof (cases "p = 1")
  case True
  then show ?thesis using integral_abs_bound[of M f] by simp
next
  case False
  have pg: "1 < p" using p False by linarith
  let ?q = "p / (p-1)"
  have q: "1 < ?q" using pg by (simp add: less_divide_eq)
  have conj: "1/p + 1/?q = 1" using pg by (simp add: field_simps)
  have fm: "f \<in> borel_measurable M" using fi by measurable
  have one: "integrable M (\<lambda>x. \<bar>1::real\<bar> powr ?q)"
    using finite_measure.integrable_const[OF fin, of 1] by simp
  have h: "(\<integral>x. \<bar>f x\<bar> \<partial>M) \<le> Lp_seminorm p M f"
    using Lp_Holder_inequality[OF pg q conj fm _ fpi one]
    by (simp add: Lp_seminorm_def mass)
  have bd: "\<bar>integral\<^sup>L M f\<bar> \<le> Lp_seminorm p M f"
    using integral_abs_bound[of M f] h by linarith
  have "\<bar>integral\<^sup>L M f\<bar> powr p \<le> Lp_seminorm p M f powr p"
    by (rule powr_mono2) (use p bd in auto)
  also have "\<dots> = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
    unfolding Lp_seminorm_def using pg
    by (simp add: powr_powr integral_nonneg)
  finally show ?thesis .
qed

(* Auxiliary for Theorems 3.2 and 5.4: reflection and translation preserve integrability. *)
lemma integrable_reflect_translate:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes fi: "integrable lborel f"
  shows "integrable lborel (\<lambda>y. f (x-y))"
proof -
  have eq: "distr lborel borel (\<lambda>y::'a. x-y) = lborel"
    using lborel_affine[of "-1::real" x] by (simp add: density_1)
  show ?thesis by (rule integrable_distr[where M'=borel])
    (measurable, simp add: eq fi)
qed

(* Auxiliary for Theorems 3.2 and 5.4: a normalized nonnegative kernel defines a probability measure. *)
lemma kernel_density:
  fixes rho :: "'a::euclidean_space \<Rightarrow> real"
  assumes ri: "integrable lborel rho" and rn: "\<And>x. 0 \<le> rho x"
    and r1: "integral\<^sup>L lborel rho = 1"
  shows "finite_measure (density lborel rho)"
    "measure (density lborel rho) (space (density lborel rho)) = 1"
proof -
  have rm: "rho \<in> borel_measurable lborel" using ri by measurable
  have rm': "(\<lambda>x. ennreal (rho x)) \<in> borel_measurable lborel" using rm by measurable
  have em_eq: "emeasure (density lborel rho) UNIV = (\<integral>\<^sup>+x. ennreal (rho x) \<partial>lborel)"
    using emeasure_density[OF rm', of UNIV] by simp
  have em: "emeasure (density lborel rho) (space (density lborel rho)) = 1"
    using nn_integral_eq_integral[OF ri] rn r1
    by (simp add: em_eq)
  have em_uni: "emeasure (density lborel rho) UNIV = 1" using em by simp
  show "finite_measure (density lborel rho)"
    by (rule finite_measureI) (simp add: em_uni)
  show "measure (density lborel rho) (space (density lborel rho)) = 1"
    by (simp add: measure_def em_uni)
qed

(* Auxiliary for Theorems 3.2 and 5.4: the pointwise power estimate underlying convolution contraction. *)
lemma convolution_power_bound:
  fixes rho f :: "'a::euclidean_space \<Rightarrow> real"
  assumes ri: "integrable lborel rho" and rn: "\<And>x. 0 \<le> rho x"
    and rb: "\<And>x. \<bar>rho x\<bar> \<le> C" and r1: "integral\<^sup>L lborel rho = 1"
    and p: "1 \<le> p" and fi: "integrable lborel f"
    and fpi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "\<bar>convolution rho f x\<bar> powr p \<le>
    convolution rho (\<lambda>y. \<bar>f y\<bar> powr p) x"
proof -
  let ?r = "\<lambda>y. rho (x-y)"
  let ?D = "density lborel ?r"
  have rm: "rho \<in> borel_measurable borel" using ri by measurable
  have fm: "f \<in> borel_measurable lborel" using fi by measurable
  have fpm: "(\<lambda>y. \<bar>f y\<bar> powr p) \<in> borel_measurable lborel" using fpi by measurable
  have rmi: "?r \<in> borel_measurable lborel" using rm by measurable
  have rnn: "AE y in lborel. 0 \<le> ?r y" using rn by simp
  have rint: "integrable lborel ?r" by (rule integrable_reflect_translate[OF ri])
  have mass: "integral\<^sup>L lborel ?r = 1"
    using lborel_integral_reflect_translate[OF rm, of x] r1 by simp
  have fin: "finite_measure ?D" by (rule kernel_density(1)[OF rint rn mass])
  have m1: "measure ?D (space ?D) = 1" by (rule kernel_density(2)[OF rint rn mass])
  have intf: "integrable ?D f"
    unfolding integrable_density[OF fm rmi rnn]
    using bounded_kernel_integrable[OF rm rb fi, of x] by simp
  have intfp: "integrable ?D (\<lambda>y. \<bar>f y\<bar> powr p)"
    unfolding integrable_density[OF fpm rmi rnn]
    using bounded_kernel_integrable[OF rm rb fpi, of x] by simp
  show ?thesis
    using normalized_integral_power_bound[OF fin m1 p intf intfp]
    unfolding integral_density[OF fm rmi rnn] integral_density[OF fpm rmi rnn]
      convolution_def by simp
qed

(* Auxiliary for Theorems 3.2 and 5.4: Fubini evaluation of the integrated convolution majorant. *)
lemma convolution_integral:
  fixes rho f :: "'a::euclidean_space \<Rightarrow> real"
  assumes ri: "integrable lborel rho" and rn: "\<And>x. 0 \<le> rho x"
    and r1: "integral\<^sup>L lborel rho = 1"
    and fi: "integrable lborel f" and fn: "\<And>x. 0 \<le> f x"
  shows "integrable lborel (convolution rho f)"
    "integral\<^sup>L lborel (convolution rho f) = integral\<^sup>L lborel f"
proof -
  have PS: "pair_sigma_finite (lborel::'a measure) (lborel::'a measure)" by standard
  have rm: "rho \<in> borel_measurable borel" using ri by measurable
  have fm: "f \<in> borel_measurable borel" using fi by measurable
  have transi: "\<And>y. integrable lborel (\<lambda>x. rho (x-y))"
  proof -
    fix y::'a
    have eq: "distr lborel borel ((+) (-y)) = lborel" by (rule lborel_distr_plus)
    have "integrable lborel (\<lambda>x. rho (-y+x))"
      by (rule integrable_distr[where M'=borel and f=rho and T="(+) (-y)"])
         (measurable, simp add: eq ri)
    then show "integrable lborel (\<lambda>x. rho (x-y))" by (simp add: add.commute)
  qed
  have trans: "\<And>y. (\<integral>x. rho (x-y) \<partial>lborel) = 1"
  proof -
    fix y::'a
    show "(\<integral>x. rho (x-y) \<partial>lborel) = 1"
      using lborel_integral_translation[OF rm, of "-y"] r1 by (simp add: add.commute)
  qed
  have im: "(\<lambda>(y,x). rho (x-y) * f y) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using rm fm by measurable
  have inner: "\<And>y. integrable lborel (\<lambda>x. rho (x-y) * f y)"
    using transi by simp
  have val: "\<And>y. (\<integral>x. norm (rho (x-y) * f y) \<partial>lborel) = f y"
    using rn fn trans by (simp add: abs_mult)
  have pair: "integrable (lborel \<Otimes>\<^sub>M lborel) (\<lambda>(y,x). rho (x-y) * f y)"
  proof (rule pair_sigma_finite.Fubini_integrable[OF PS im])
    show "integrable lborel (\<lambda>y. \<integral>x. norm (case (y,x) of (y,x) \<Rightarrow> rho (x-y)*f y) \<partial>lborel)"
      by (simp only: prod.case val) (rule fi)
    show "AE y in lborel. integrable lborel (\<lambda>x. case (y,x) of (y,x) \<Rightarrow> rho (x-y)*f y)"
      by (intro AE_I2) (simp only: prod.case, rule inner)
  qed
  have int: "integrable lborel (\<lambda>x. \<integral>y. rho (x-y) * f y \<partial>lborel)"
    by (rule pair_sigma_finite.integrable_snd[OF PS pair])
  show "integrable lborel (convolution rho f)"
    using int unfolding convolution_def .
  have "(\<integral>x. (\<integral>y. rho (x-y) * f y \<partial>lborel) \<partial>lborel) =
      (\<integral>y. (\<integral>x. rho (x-y) * f y \<partial>lborel) \<partial>lborel)"
    by (rule pair_sigma_finite.Fubini_integral[OF PS pair])
  also have "\<dots> = integral\<^sup>L lborel f"
    by (simp add: trans)
  finally show "integral\<^sup>L lborel (convolution rho f) = integral\<^sup>L lborel f"
    unfolding convolution_def .
qed

(* Auxiliary for Theorems 3.2 and 5.4: convolution is an Lp contraction for general L1 intersect Lp targets. *)
theorem convolution_Lp_contraction:
  fixes rho f :: "'a::euclidean_space \<Rightarrow> real"
  assumes rc: "continuous_on UNIV rho" and ri: "integrable lborel rho"
    and rn: "\<And>x. 0 \<le> rho x" and rb: "\<And>x. \<bar>rho x\<bar> \<le> C"
    and r1: "integral\<^sup>L lborel rho = 1"
    and p: "1 \<le> p" and fi: "integrable lborel f"
    and fpi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "integrable lborel (\<lambda>x. \<bar>convolution rho f x\<bar> powr p)"
    "Lp_seminorm p lborel (convolution rho f) \<le> Lp_seminorm p lborel f"
proof -
  let ?F = "convolution rho f"
  let ?G = "convolution rho (\<lambda>x. \<bar>f x\<bar> powr p)"
  have fc: "continuous_on UNIV ?F" by (rule bounded_kernel_convolution_continuous[OF rc rb fi])
  have fm: "?F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF fc])
  have gi: "integrable lborel ?G"
    by (rule convolution_integral(1)[OF ri rn r1 fpi]) simp
  have gint: "integral\<^sup>L lborel ?G = (\<integral>x. \<bar>f x\<bar> powr p \<partial>lborel)"
    by (rule convolution_integral(2)[OF ri rn r1 fpi]) simp
  have gn: "\<And>x. 0 \<le> ?G x"
    unfolding convolution_def
    by (intro Bochner_Integration.integral_nonneg mult_nonneg_nonneg rn) simp
  have bd: "\<And>x. \<bar>?F x\<bar> powr p \<le> ?G x"
    by (rule convolution_power_bound[OF ri rn rb r1 p fi fpi])
  have int: "integrable lborel (\<lambda>x. \<bar>?F x\<bar> powr p)"
    by (rule Bochner_Integration.integrable_bound[OF gi])
       (use fm in measurable, intro AE_I2, simp add: gn bd)
  show "integrable lborel (\<lambda>x. \<bar>?F x\<bar> powr p)" by (rule int)
  have le: "(\<integral>x. \<bar>?F x\<bar> powr p \<partial>lborel) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>lborel)"
    using integral_mono[OF int gi bd] gint by simp
  show "Lp_seminorm p lborel ?F \<le> Lp_seminorm p lborel f"
    unfolding Lp_seminorm_def by (rule powr_mono2) (use p le in auto)
qed

(* Auxiliary for (3.2): the integral defining the paper convolution. *)
lemma convolution_apply:
  "convolution rho f x = (\<integral>y. rho (x-y) * f y \<partial>lborel)"
  by (simp only: convolution_def)

(* Auxiliary for Theorems 3.2 and 5.4: bounded targets give integrable convolution integrands. *)
lemma convolution_integrand_integrable:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and x :: 'a
  assumes k: "0 < k" and fb: "\<And>y. \<bar>f y\<bar> \<le> M"
    and fm: "f \<in> borel_measurable borel"
  shows "integrable lborel (\<lambda>y. mollifier k (x-y) * f y)"
proof -
  have base: "integrable lborel (\<lambda>y. f (x-y) * mollifier k y)"
    by (rule bounded_kernel_integrable[OF fm fb mollifier_integrable[OF k]])
  have "integrable lborel (\<lambda>y. f (x-(x-y)) * mollifier k (x-y))"
    by (rule integrable_reflect_translate[OF base])
  then show ?thesis by (simp add: mult.commute)
qed

(* Auxiliary for Theorems 3.2 and 5.4: a weaker support estimate reused by the limit proof. *)
lemma mollifier_support_two:
  fixes x :: "'a::euclidean_space"
  assumes k: "0 < k" and x: "2 / real k \<le> norm x"
  shows "mollifier k x = 0"
  by (rule mollifier_support[OF k])
     (use k x in \<open>auto simp: field_simps\<close>)

(* Auxiliary for (3.2) and Theorem 5.4: continuity for arbitrary integrable targets. *)
lemma mollified_continuous:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes fi: "integrable lborel f"
  shows "continuous_on UNIV (convolution (mollifier k) f)"
  by (rule bounded_kernel_convolution_continuous[OF mollifier_continuous _ fi,
        where C="real k ^ DIM('a) / mollifier_bump_mass TYPE('a)"])
     (simp add: mollifier_nonneg mollifier_bound)

(* Auxiliary for Theorems 3.2 and 5.4: uniform bound for the exact normalized paper kernels. *)
lemma mollifier_convolution_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and k :: nat and M :: real and x :: "'a"
  assumes k_pos: "k > 0"
  assumes f_bdd: "\<And>y. \<bar>f y\<bar> \<le> M"
  assumes f_meas: "f \<in> borel_measurable borel"
  shows "\<bar>(convolution (mollifier k) f) x\<bar> \<le> M"
proof -
  have M_nonneg: "M \<ge> 0" using f_bdd[of 0] by simp
  have shift_int: "(\<integral>y. mollifier k y \<partial>lborel) = (\<integral>y. mollifier k (x - y) \<partial>lborel)"
    using lborel_integral_reflect_translate[OF mollifier_measurable[of k], where t = x]
    by (simp add: k_pos mollifier_integral_one)
  have const_bdd: "\<And>y :: 'a. \<bar>(1::real)\<bar> \<le> 1" by simp
  have const_meas: "(\<lambda>_::'a. (1::real)) \<in> borel_measurable borel" by simp
  have int_one: "integrable lborel (\<lambda>y. mollifier k (x - y) * (1::real))"
    using convolution_integrand_integrable[OF k_pos const_bdd const_meas, of x] .
  have int_shift: "integrable lborel (\<lambda>y. mollifier k (x - y))"
    using int_one by simp
  have int_scaled: "integrable lborel (\<lambda>y. mollifier k (x - y) * M)"
    using int_shift by simp
  have int_base: "integrable lborel (\<lambda>y. mollifier k (x - y) * f y)"
    using convolution_integrand_integrable[OF k_pos f_bdd f_meas] .
  have int_abs_f: "integrable lborel (\<lambda>y. mollifier k (x - y) * \<bar>f y\<bar>)"
    using int_base mollifier_nonneg[of k]
    by (metis (no_types, lifting) ext abs_mult abs_of_nonneg integrable_abs)
  have "\<bar>(convolution (mollifier k) f) x\<bar> = \<bar>\<integral>y. mollifier k (x - y) * f y \<partial>lborel\<bar>"
    unfolding convolution_apply ..
  also have "\<dots> \<le> \<integral>y. \<bar>mollifier k (x - y) * f y\<bar> \<partial>lborel"
    by simp
  also have "\<dots> = \<integral>y. mollifier k (x - y) * \<bar>f y\<bar> \<partial>lborel"
    by (simp add: abs_mult mollifier_nonneg)
  also have "\<dots> \<le> \<integral>y. mollifier k (x - y) * M \<partial>lborel"
  proof (rule integral_mono_AE[OF int_abs_f int_scaled])
    show "AE y in lborel. mollifier k (x - y) * \<bar>f y\<bar> \<le> mollifier k (x - y) * M"
      using f_bdd mollifier_nonneg[of k] by (intro AE_I2 mult_left_mono) auto
  qed
  also have "\<dots> = M * (\<integral>y. mollifier k (x - y) \<partial>lborel)"
    by simp
  also have "\<dots> \<le> M"
    by (metis k_pos mollifier_integral_one mult_cancel_left1 nle_le shift_int)
  finally show ?thesis.
qed

(* Auxiliary mollifier fact for the construction in Theorems 3.2 and 5.4; not separately numbered. *)
lemma mollifier_pointwise_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and x :: "'a" and M :: real
  assumes f_bdd: "\<And>y. \<bar>f y\<bar> \<le> M"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_cont: "continuous (at x) f"
  shows "(\<lambda>k. (convolution (mollifier k) f) x) \<longlonglongrightarrow> f x"
proof (rule tendstoI)
  fix eps :: real
  assume eps_pos: "eps > 0"
  have M_nonneg: "M \<ge> 0" using f_bdd[of 0] by simp
  define eps' where "eps' = eps / 2"
  have eps'_pos: "eps' > 0" using eps_pos unfolding eps'_def by simp
  obtain delta where delta_pos: "delta > 0"
    and delta_prop': "\<And>y. dist y x < delta \<Longrightarrow> dist (f y) (f x) < eps'"
    using Elementary_Metric_Spaces.continuous_at_eps_delta eps'_pos f_cont by blast
  have delta_prop: "\<And>y. dist y x < delta \<Longrightarrow> \<bar>f y - f x\<bar> < eps'"
    using delta_prop' by (simp add: dist_real_def)
  obtain n where n_prop: "inverse (of_nat (Suc n)) < delta / 2"
    using reals_Archimedean[of "delta / 2"] delta_pos by auto
  define K where "K = Suc n"
  have K_pos: "K > 0" unfolding K_def by simp
  have K_delta: "2 / real K < delta"
    using n_prop unfolding K_def by (simp add: field_simps)
  show "eventually (\<lambda>k. dist ((convolution (mollifier k) f) x) (f x) < eps) sequentially"
    unfolding eventually_sequentially
  proof (intro exI[of _ K] allI impI)
    fix k assume k_ge: "K \<le> k"
    then have k_pos: "k > 0" using K_pos by simp
    have k_real_pos: "(0::real) < real k" using k_pos by simp
    have K_real_pos: "(0::real) < real K" using K_pos by simp
    have k_real_ge: "real K \<le> real k" using k_ge by simp
    have k_delta: "2 / real k < delta"
    proof -
      have "2 / real k \<le> 2 / real K"
        using k_real_pos K_real_pos k_real_ge by (simp add: divide_simps)
      then show ?thesis using K_delta by simp
    qed
    have int_base: "integrable lborel (\<lambda>y. mollifier k (x - y) * f y)"
      using convolution_integrand_integrable[OF k_pos f_bdd f_meas] .
    have fx_bdd: "\<And>y :: 'a. \<bar>f x\<bar> \<le> \<bar>f x\<bar>" by simp
    have fx_meas: "(\<lambda>_::'a. f x) \<in> borel_measurable borel" by simp
    have int_fx: "integrable lborel (\<lambda>y. mollifier k (x - y) * f x)"
      using convolution_integrand_integrable[OF k_pos fx_bdd fx_meas, of x] .
    have shift_int: "(\<integral>y. mollifier k y \<partial>lborel) = (\<integral>y. mollifier k (x - y) \<partial>lborel)"
      using lborel_integral_reflect_translate[OF mollifier_measurable[of k], where t = x]
      by (simp only: k_pos mollifier_integral_one)
    have moll_int_one: "integral\<^sup>L (lborel :: 'a measure) (mollifier k) = 1"
      by (rule mollifier_integral_one[OF k_pos])
    have shift_one: "(\<integral>y. mollifier k (x - y) \<partial>lborel) = 1"
      by (metis moll_int_one shift_int)
    have fx_eq: "f x = f x * (\<integral>y. mollifier k (x - y) \<partial>lborel)"
      using shift_one by simp
    have diff_eq: "(convolution (mollifier k) f) x - f x
        = \<integral>y. mollifier k (x - y) * (f y - f x) \<partial>lborel"
    proof -
      have step1: "(convolution (mollifier k) f) x - f x
          = (\<integral>y. mollifier k (x - y) * f y \<partial>lborel) - f x * (\<integral>y. mollifier k (x - y) \<partial>lborel)"
        unfolding convolution_apply using fx_eq by simp
      have step2: "f x * (\<integral>y. mollifier k (x - y) \<partial>lborel) = (\<integral>y. mollifier k (x - y) * f x \<partial>lborel)"
        by simp
      have step3: "(\<integral>y. mollifier k (x - y) * f y \<partial>lborel) - (\<integral>y. mollifier k (x - y) * f x \<partial>lborel)
          = \<integral>y. (mollifier k (x - y) * f y - mollifier k (x - y) * f x) \<partial>lborel"
        using int_base int_fx by (simp only: Bochner_Integration.integral_diff)
      have step4: "\<And>y. mollifier k (x - y) * f y - mollifier k (x - y) * f x
          = mollifier k (x - y) * (f y - f x)"
        by (simp add: right_diff_distrib)
      show ?thesis using step1 step2 step3 step4 by simp
    qed
    have bound_pt: "\<And>y. \<bar>mollifier k (x - y) * (f y - f x)\<bar> \<le> mollifier k (x - y) * eps'"
    proof -
      fix y :: "'a"
      show "\<bar>mollifier k (x - y) * (f y - f x)\<bar> \<le> mollifier k (x - y) * eps'"
      proof (cases "mollifier k (x - y) = 0")
        case True
        then show ?thesis using eps'_pos by simp
      next
        case False
        then have not_far: "\<not> (norm (x - y) \<ge> 2 / real k)"
          using mollifier_support_two[OF k_pos, of "x - y"] by auto
        have near: "norm (x - y) < 2 / real k" using not_far by simp
        have dist_lt: "dist y x < delta"
          using near k_delta by (simp add: dist_norm norm_minus_commute)
        have fy_close: "\<bar>f y - f x\<bar> < eps'"
          using delta_prop[OF dist_lt] .
        have moll_nn: "mollifier k (x - y) \<ge> 0" using mollifier_nonneg[of k "x - y"] .
        have eq1: "\<bar>mollifier k (x - y) * (f y - f x)\<bar> = mollifier k (x - y) * \<bar>f y - f x\<bar>"
        proof -
          have "\<bar>mollifier k (x - y) * (f y - f x)\<bar>
              = \<bar>mollifier k (x - y)\<bar> * \<bar>f y - f x\<bar>"
            by (rule abs_mult)
          also have "\<dots> = mollifier k (x - y) * \<bar>f y - f x\<bar>"
            using moll_nn by (simp only: abs_of_nonneg)
          finally show ?thesis .
        qed
        show ?thesis
          unfolding eq1 using fy_close moll_nn by (intro mult_left_mono, simp)
      qed
    qed
    have eps'_bdd: "\<And>y::'a. \<bar>eps'\<bar> \<le> eps'" using eps'_pos by simp
    have eps'_meas: "(\<lambda>_::'a. eps') \<in> borel_measurable borel" by simp
    have int_diff_eps: "integrable lborel (\<lambda>y. mollifier k (x - y) * eps')"
      using convolution_integrand_integrable[OF k_pos eps'_bdd eps'_meas, of x] .
    have int_diff: "integrable lborel (\<lambda>y. mollifier k (x - y) * (f y - f x))"
    proof -
      have eq: "(\<lambda>y. mollifier k (x - y) * (f y - f x))
          = (\<lambda>y. mollifier k (x - y) * f y - mollifier k (x - y) * f x)"
        by (auto simp: right_diff_distrib)
      show ?thesis unfolding eq using int_base int_fx by simp
    qed
    have final_bound: "\<bar>(convolution (mollifier k) f) x - f x\<bar> \<le> eps'"
    proof -
      have s1: "\<bar>(convolution (mollifier k) f) x - f x\<bar>
          = \<bar>\<integral>y. mollifier k (x - y) * (f y - f x) \<partial>lborel\<bar>"
        using diff_eq by simp
      have s2: "\<bar>\<integral>y. mollifier k (x - y) * (f y - f x) \<partial>lborel\<bar>
          \<le> \<integral>y. \<bar>mollifier k (x - y) * (f y - f x)\<bar> \<partial>lborel"
        by simp
      have s3: "(\<integral>y. \<bar>mollifier k (x - y) * (f y - f x)\<bar> \<partial>lborel)
          \<le> (\<integral>y. mollifier k (x - y) * eps' \<partial>lborel)"
        by (rule integral_mono_AE[OF integrable_abs[OF int_diff] int_diff_eps])
           (intro AE_I2 bound_pt)
      have s4: "(\<integral>y. mollifier k (x - y) * eps' \<partial>lborel) = eps' * (\<integral>y. mollifier k (x - y) \<partial>lborel)"
        by simp
      have "eps' = eps' * (LBINT v. mollifier k (x - v))"
          by (simp add: shift_one)
      then show ?thesis using s1 s2 s3 s4 shift_one by argo
    qed
    have eps'_lt: "eps' < eps" unfolding eps'_def using eps_pos by simp
    show "dist ((convolution (mollifier k) f) x) (f x) < eps"
      unfolding dist_real_def using final_bound eps'_lt by linarith
  qed
qed

(* Auxiliary for Theorems 3.2 and 5.4: bounded continuous-target base case for the exact kernel. *)
theorem mollifier_continuous_Lp_convergence:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and Q :: "'a set" and M p :: real
  assumes p_pos: "p > 0"
  assumes f_bdd: "\<And>y. \<bar>f y\<bar> \<le> M"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_cont: "\<And>x. continuous (at x) f"
  assumes f_int: "integrable lborel f"
  assumes Q_bounded: "bounded Q"
  assumes Q_meas: "Q \<in> sets lebesgue"
  shows "(\<lambda>k. \<integral>x. \<bar>(convolution (mollifier k) f) x - f x\<bar> powr p \<partial>(lebesgue_on Q)) \<longlonglongrightarrow> 0"
proof -
  have p_nonneg: "p \<ge> 0" using p_pos by simp
  have Q_lmeas: "Q \<in> lmeasurable" using bounded_set_imp_lmeasurable[OF Q_bounded Q_meas] .
  have fm_Q: "finite_measure (lebesgue_on Q)" using finite_measure_lebesgue_on[OF Q_lmeas] .

  define s where "s = (\<lambda>k x. \<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar> powr p)"
  define w where "w = (\<lambda>x::'a. (2 * M) powr p)"

  have powr_cont: "continuous_on UNIV (\<lambda>t::real. \<bar>t\<bar> powr p)"
  proof (rule continuous_on_powr')
    show "continuous_on UNIV (\<lambda>t::real. \<bar>t\<bar>)" by (intro continuous_intros)
    show "continuous_on UNIV (\<lambda>t::real. p)" by (intro continuous_intros)
    show "\<forall>t\<in>(UNIV::real set). \<bar>t\<bar> \<ge> 0 \<and> (\<bar>t\<bar> = 0 \<longrightarrow> p > 0)" using p_pos by simp
  qed
  have powr_meas: "(\<lambda>t::real. \<bar>t\<bar> powr p) \<in> borel_measurable borel"
    using borel_measurable_continuous_onI[OF powr_cont] .

  have s_meas: "\<And>k. s k \<in> borel_measurable (lebesgue_on Q)"
  proof -
    fix k :: nat
    have conv_cont: "continuous_on UNIV (convolution (mollifier (Suc k)) f)"
      by (rule mollified_continuous[OF f_int])
    have conv_meas: "(convolution (mollifier (Suc k)) f) \<in> borel_measurable borel"
      using borel_measurable_continuous_onI[OF conv_cont] .
    have diff_meas: "(\<lambda>x. (convolution (mollifier (Suc k)) f) x - f x) \<in> borel_measurable borel"
      using conv_meas f_meas by measurable
    have "s k \<in> borel_measurable borel"
      unfolding s_def using diff_meas powr_meas by measurable
    then show "s k \<in> borel_measurable (lebesgue_on Q)"
      by (rule borel_measurable_lebesgue_onI)
  qed

  have w_int: "integrable (lebesgue_on Q) w"
    unfolding w_def using finite_measure.integrable_const[OF fm_Q] .

  have lim_pt: "\<And>x. (\<lambda>k. s k x) \<longlonglongrightarrow> 0"
  proof -
    fix x :: "'a"
    have p1: "(\<lambda>k. (convolution (mollifier k) f) x) \<longlonglongrightarrow> f x"
      by (rule mollifier_pointwise_limit[OF f_bdd f_meas f_cont])
    have base: "(\<lambda>k. (convolution (mollifier k) f) x - f x) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>k. (convolution (mollifier k) f) x - f x) \<longlonglongrightarrow> f x - f x"
        using p1 by (intro tendsto_diff tendsto_const)
      then show ?thesis by simp
    qed
    have shift: "(\<lambda>k. (convolution (mollifier (Suc k)) f) x - f x) \<longlonglongrightarrow> 0"
      using LIMSEQ_Suc[OF base] .
    have abs_shift: "(\<lambda>k. \<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar>) \<longlonglongrightarrow> 0"
      using tendsto_rabs[OF shift] by simp
    have nonneg_ev: "\<forall>\<^sub>F k in sequentially. (0::real) \<le> \<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar>"
      by simp
    show "(\<lambda>k. s k x) \<longlonglongrightarrow> 0"
      unfolding s_def
      using tendsto_zero_powrI[OF abs_shift tendsto_const nonneg_ev p_pos] .
  qed

  have bound: "\<And>k. AE x in lebesgue_on Q. norm (s k x) \<le> w x"
  proof -
    fix k :: nat
    show "AE x in lebesgue_on Q. norm (s k x) \<le> w x"
    proof (intro AE_I2)
      fix x :: "'a"
      have k_pos: "Suc k > 0" by simp
      have b1: "\<bar>(convolution (mollifier (Suc k)) f) x\<bar> \<le> M"
        using mollifier_convolution_bound[OF k_pos f_bdd f_meas] .
      have b2: "\<bar>f x\<bar> \<le> M" using f_bdd .
      have tri: "\<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar> \<le> \<bar>(convolution (mollifier (Suc k)) f) x\<bar> + \<bar>f x\<bar>"
        by (rule abs_triangle_ineq4)
      have diff_bound: "\<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar> \<le> 2 * M"
        using tri b1 b2 by linarith
      have diff_nonneg: "(0::real) \<le> \<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar>" by simp
      have "\<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar> powr p \<le> (2 * M) powr p"
        by (rule powr_mono2[OF p_nonneg diff_nonneg diff_bound])
      then show "norm (s k x) \<le> w x"
        unfolding s_def w_def by simp
    qed
  qed

  have main: "(\<lambda>k. \<integral>x. s k x \<partial>(lebesgue_on Q)) \<longlonglongrightarrow> \<integral>x. (0::real) \<partial>(lebesgue_on Q)"
  proof (rule integral_dominated_convergence[where w = w])
    show "(\<lambda>x::'a. (0::real)) \<in> borel_measurable (lebesgue_on Q)" by simp
    show "\<And>k. s k \<in> borel_measurable (lebesgue_on Q)" using s_meas .
    show "integrable (lebesgue_on Q) w" using w_int .
    show "AE x in lebesgue_on Q. (\<lambda>k. s k x) \<longlonglongrightarrow> 0" using lim_pt by simp
    show "\<And>k. AE x in lebesgue_on Q. norm (s k x) \<le> w x" using bound .
  qed

  have shifted: "(\<lambda>k. \<integral>x. \<bar>(convolution (mollifier (Suc k)) f) x - f x\<bar> powr p \<partial>(lebesgue_on Q)) \<longlonglongrightarrow> 0"
    using main unfolding s_def by simp

  show ?thesis
    using filterlim_sequentially_Suc[THEN iffD1, OF shifted] .
qed

(* Auxiliary for Theorems 3.2 and 5.4: continuous compactly supported functions are bounded and integrable. *)
lemma compact_continuous_bounds:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes gc: "continuous_on UNIV g" and gs: "\<And>x. R < norm x \<Longrightarrow> g x = 0"
    and p: "0 < p"
  shows "\<exists>M>0. (\<forall>x. \<bar>g x\<bar> \<le> M) \<and>
    integrable lborel g \<and> integrable lborel (\<lambda>x. \<bar>g x\<bar> powr p)"
proof -
  have c: "continuous_on (cball 0 R) g" by (rule continuous_on_subset[OF gc]) simp
  have b: "bounded (g ` cball 0 R)"
    by (rule compact_imp_bounded[OF compact_continuous_image[OF c compact_cball]])
  obtain B where B: "\<And>x. x \<in> cball 0 R \<Longrightarrow> \<bar>g x\<bar> \<le> B"
    using b unfolding bounded_iff by force
  let ?M = "max 1 B"
  have M: "0 < ?M" by simp
  have bd: "\<And>x. \<bar>g x\<bar> \<le> ?M"
    using B gs by (metis abs_zero le_max_iff_disj mem_cball_0 not_le zero_le_one)
  have gm: "g \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF gc])
  have gi: "integrable lborel g"
    by (rule integrableI_bounded_set[where A="cball 0 R" and B="?M"])
       (simp, use gm in measurable, rule emeasure_lborel_cball_finite,
        simp add: bd, use gs in auto)
  have gpi: "integrable lborel (\<lambda>x. \<bar>g x\<bar> powr p)"
    by (rule integrableI_bounded_set[where A="cball 0 R" and B="?M powr p"])
       (simp, use gm in measurable, rule emeasure_lborel_cball_finite,
        intro AE_I2, use bd p in \<open>auto intro: powr_mono2\<close>,
        use gs p in auto)
  show ?thesis by (intro exI[where x="?M"]) (use M bd gi gpi in blast)
qed

(* Auxiliary for Theorems 3.2 and 5.4: compactly supported comparison functions for the convergence proof. *)
lemma compact_continuous_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes p: "1 \<le> p" and fm: "f \<in> borel_measurable borel"
    and fi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
    and R: "0 \<le> R" and fs: "\<And>x. R < norm x \<Longrightarrow> f x = 0"
    and e: "0 < e"
  shows "\<exists>g. continuous_on UNIV g \<and> (\<forall>x. R+1 < norm x \<longrightarrow> g x = 0) \<and>
    integrable lborel (\<lambda>x. \<bar>g x-f x\<bar> powr p) \<and>
    Lp_seminorm p lborel (\<lambda>x. g x-f x) < e"
proof -
  obtain h where hc: "continuous_on UNIV h"
    and hi: "integrable lborel (\<lambda>x. \<bar>h x-f x\<bar> powr p)"
    and he: "Lp_seminorm p lborel (\<lambda>x. h x-f x) < e"
    using continuous_dense_Lp[OF p fm fi e] by blast
  let ?t = "tent (cball (0::'a) R) 1"
  let ?g = "\<lambda>x. ?t x * h x"
  have gc: "continuous_on UNIV ?g"
    by (intro continuous_intros tent_continuous hc) simp
  have hm: "h \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF hc])
  have gm: "?g \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF gc])
  have ne: "cball (0::'a) R \<noteq> {}" using R by simp
  have gs: "\<And>x. R+1 < norm x \<Longrightarrow> ?g x = 0"
    using tent_eq_zero_far[OF compact_cball ne zero_less_one, of R] by auto
  have bd: "\<And>x. \<bar>?g x-f x\<bar> \<le> \<bar>h x-f x\<bar>"
  proof -
    fix x::'a
    show "\<bar>?g x-f x\<bar> \<le> \<bar>h x-f x\<bar>"
    proof (cases "x \<in> cball 0 R")
      case True then show ?thesis by (simp add: tent_eq_one)
    next
      case False
      then have fx: "f x = 0" by (intro fs) auto
      have t: "0 \<le> ?t x" "?t x \<le> 1" by (rule tent_nonneg, rule tent_le_one, simp)
      have "?t x * \<bar>h x\<bar> \<le> 1 * \<bar>h x\<bar>" by (rule mult_right_mono[OF t(2)]) simp
      then show ?thesis using t by (simp add: fx abs_mult)
    qed
  qed
  have bd_p: "\<And>x. \<bar>?g x-f x\<bar> powr p \<le> \<bar>h x-f x\<bar> powr p"
    by (rule powr_mono2) (use p bd in auto)
  have gi: "integrable lborel (\<lambda>x. \<bar>?g x-f x\<bar> powr p)"
    by (rule Bochner_Integration.integrable_bound[OF hi])
       (use gm fm in measurable, intro AE_I2, simp add: bd_p)
  have le: "(\<integral>x. \<bar>?g x-f x\<bar> powr p \<partial>lborel) \<le>
      (\<integral>x. \<bar>h x-f x\<bar> powr p \<partial>lborel)"
    by (rule integral_mono[OF gi hi bd_p])
  have "Lp_seminorm p lborel (\<lambda>x. ?g x-f x) \<le> Lp_seminorm p lborel (\<lambda>x. h x-f x)"
    unfolding Lp_seminorm_def by (rule powr_mono2) (use p le in auto)
  then have ge: "Lp_seminorm p lborel (\<lambda>x. ?g x-f x) < e" using he by linarith
  show ?thesis by (intro exI[where x="?g"]) (use gc gs gi ge in blast)
qed

(* Auxiliary for Theorems 3.2 and 5.4: linearity of mollification for integrable targets. *)
lemma mollified_diff:
  fixes f g :: "'a::euclidean_space \<Rightarrow> real"
  assumes fi: "integrable lborel f" and gi: "integrable lborel g"
  shows "convolution (mollifier k) (\<lambda>x. f x-g x) =
    (\<lambda>x. convolution (mollifier k) f x -
      convolution (mollifier k) g x)"
proof -
  have bd: "\<And>x::'a. \<bar>mollifier k x\<bar> \<le> real k ^ DIM('a) / mollifier_bump_mass TYPE('a)"
    by (simp add: mollifier_nonneg mollifier_bound)
  have ifi: "\<And>x. integrable lborel (\<lambda>y. mollifier k (x-y) * f y)"
    by (rule bounded_kernel_integrable[OF mollifier_measurable bd fi])
  have igi: "\<And>x. integrable lborel (\<lambda>y. mollifier k (x-y) * g y)"
    by (rule bounded_kernel_integrable[OF mollifier_measurable bd gi])
  show ?thesis by (rule ext)
    (simp only: convolution_def right_diff_distrib Bochner_Integration.integral_diff[OF ifi igi])
qed

(* Auxiliary for Theorems 3.2 and 5.4: the exact paper kernel is an Lp contraction. *)
lemma mollified_Lp_bounds:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes k: "0 < k" and p: "1 \<le> p" and fi: "integrable lborel f"
    and fpi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "integrable lborel (\<lambda>x. \<bar>convolution (mollifier k) f x\<bar> powr p)"
    "Lp_seminorm p lborel (convolution (mollifier k) f) \<le> Lp_seminorm p lborel f"
proof -
  have bd: "\<And>x::'a. \<bar>mollifier k x\<bar> \<le> real k ^ DIM('a) / mollifier_bump_mass TYPE('a)"
    by (simp add: mollifier_nonneg mollifier_bound)
  show "integrable lborel (\<lambda>x. \<bar>convolution (mollifier k) f x\<bar> powr p)"
    by (rule convolution_Lp_contraction(1)[OF mollifier_continuous
        mollifier_integrable[OF k] mollifier_nonneg bd
        mollifier_integral_one[OF k] p fi fpi])
  show "Lp_seminorm p lborel (convolution (mollifier k) f) \<le> Lp_seminorm p lborel f"
    by (rule convolution_Lp_contraction(2)[OF mollifier_continuous
        mollifier_integrable[OF k] mollifier_nonneg bd
        mollifier_integral_one[OF k] p fi fpi])
qed

(* Auxiliary for Theorems 3.2 and 5.4: closure of Lp under subtraction. *)
lemma Lp_diff_integrable:
  fixes f g :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and fm: "f \<in> borel_measurable M" and gm: "g \<in> borel_measurable M"
    and fi: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
    and gi: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "integrable M (\<lambda>x. \<bar>f x-g x\<bar> powr p)"
proof -
  have ng: "(\<lambda>x. -g x) \<in> borel_measurable M" using gm by measurable
  have ngi: "integrable M (\<lambda>x. \<bar>-g x\<bar> powr p)" using gi by simp
  show ?thesis using Lp_Minkowski_integrable[OF p fm ng fi ngi] by simp
qed

(* Auxiliary for Theorems 3.2 and 5.4: three-term error splitting in the approximate-identity proof. *)
lemma Lp_triangle_three:
  fixes A B C :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and Am: "A \<in> borel_measurable M"
    and Bm: "B \<in> borel_measurable M" and Cm: "C \<in> borel_measurable M"
    and Ai: "integrable M (\<lambda>x. \<bar>A x\<bar> powr p)"
    and Bi: "integrable M (\<lambda>x. \<bar>B x\<bar> powr p)"
    and Ci: "integrable M (\<lambda>x. \<bar>C x\<bar> powr p)"
  shows "Lp_seminorm p M (\<lambda>x. A x+B x+C x) \<le>
    Lp_seminorm p M A + Lp_seminorm p M B + Lp_seminorm p M C"
proof -
  have ABm: "(\<lambda>x. A x+B x) \<in> borel_measurable M" using Am Bm by measurable
  have ABi: "integrable M (\<lambda>x. \<bar>A x+B x\<bar> powr p)"
    by (rule Lp_Minkowski_integrable[OF p Am Bm Ai Bi])
  show ?thesis
    using Lp_Minkowski_inequality[OF p ABm Cm ABi Ci]
      Lp_Minkowski_inequality[OF p Am Bm Ai Bi] by linarith
qed

(* Proofs of Theorems 3.2 and 5.4: explicit mollification converges for unbounded compactly supported Lp targets. *)
theorem mollifier_Lp_convergence:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and S :: "'a set"
  assumes p: "1 \<le> p" and fm: "f \<in> borel_measurable borel"
    and fi: "integrable lborel f" and fpi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
    and R: "0 \<le> R" and fs: "\<And>x. R < norm x \<Longrightarrow> f x = 0"
    and Sb: "bounded S" and Sm: "S \<in> sets borel"
  shows "(\<lambda>k. Lp_seminorm p (lebesgue_on S)
      (\<lambda>x. convolution (mollifier k) f x-f x)) \<longlonglongrightarrow> 0"
proof (rule tendstoI)
  fix e::real assume e: "0 < e"
  have pp: "0 < p" using p by simp
  have e4: "0 < e/4" using e by simp
  obtain g where gc: "continuous_on UNIV g"
    and gs: "\<And>x. R+1 < norm x \<Longrightarrow> g x = 0"
    and gfi: "integrable lborel (\<lambda>x. \<bar>g x-f x\<bar> powr p)"
    and gfe: "Lp_seminorm p lborel (\<lambda>x. g x-f x) < e/4"
    using compact_continuous_dense[OF p fm fpi R fs e4] by blast
  obtain M where M: "0 < M" and gb: "\<And>x. \<bar>g x\<bar> \<le> M"
    and gi: "integrable lborel g" and gpi: "integrable lborel (\<lambda>x. \<bar>g x\<bar> powr p)"
    using compact_continuous_bounds[OF gc gs pp] by blast
  have gm: "g \<in> borel_measurable borel" by (rule borel_measurable_continuous_onI[OF gc])
  have gfm: "(\<lambda>x. g x-f x) \<in> borel_measurable borel" using gm fm by measurable
  have fgm: "(\<lambda>x. f x-g x) \<in> borel_measurable borel" using gm fm by measurable
  have fgi: "integrable lborel (\<lambda>x. \<bar>f x-g x\<bar> powr p)"
    using gfi by (simp add: abs_minus_commute)
  have fg1: "integrable lborel (\<lambda>x. f x-g x)" using fi gi by simp
  have fge: "Lp_seminorm p lborel (\<lambda>x. f x-g x) < e/4"
    using gfe by (simp add: Lp_seminorm_def abs_minus_commute)
  have gci: "\<And>x. continuous (at x) g"
    using gc by (simp add: continuous_on_eq_continuous_at)
  have SL: "S \<in> sets lebesgue" using Sm by simp
  have base: "(\<lambda>k. \<integral>x. \<bar>convolution (mollifier k) g x-g x\<bar> powr p
      \<partial>(lebesgue_on S)) \<longlonglongrightarrow> 0"
    by (rule mollifier_continuous_Lp_convergence[OF pp gb gm gci gi Sb SL])
  have normlim: "(\<lambda>k. Lp_seminorm p (lebesgue_on S)
      (\<lambda>x. convolution (mollifier k) g x-g x)) \<longlonglongrightarrow> 0"
    unfolding Lp_seminorm_def
    by (rule tendsto_zero_powrI[OF base tendsto_const]) (use pp in auto)
  have ev: "\<forall>\<^sub>F k in sequentially. Lp_seminorm p (lebesgue_on S)
      (\<lambda>x. convolution (mollifier k) g x-g x) < e/4"
    using order_tendstoD(2)[OF normlim e4] .
  show "\<forall>\<^sub>F k in sequentially.
    dist (Lp_seminorm p (lebesgue_on S) (\<lambda>x. convolution (mollifier k) f x-f x)) 0 < e"
    using ev eventually_gt_at_top[of 0]
  proof eventually_elim
    fix k assume k: "0 < k" and Be: "Lp_seminorm p (lebesgue_on S)
      (\<lambda>x. convolution (mollifier k) g x-g x) < e/4"
    let ?A = "convolution (mollifier k) (\<lambda>x. f x-g x)"
    let ?B = "\<lambda>x. convolution (mollifier k) g x-g x"
    let ?C = "\<lambda>x. g x-f x"
    let ?Q = "lebesgue_on S"
    have Ac: "continuous_on UNIV ?A" by (rule mollified_continuous[OF fg1])
    have Am: "?A \<in> borel_measurable borel" by (rule borel_measurable_continuous_onI[OF Ac])
    have Aig: "integrable lborel (\<lambda>x. \<bar>?A x\<bar> powr p)"
      by (rule mollified_Lp_bounds(1)[OF k p fg1 fgi])
    have Ale: "Lp_seminorm p lborel ?A \<le> Lp_seminorm p lborel (\<lambda>x. f x-g x)"
      by (rule mollified_Lp_bounds(2)[OF k p fg1 fgi])
    have Ae: "Lp_seminorm p ?Q ?A < e/4"
      using Lp_seminorm_restrict_le[OF pp Sm Am Aig] Ale fge by linarith
    have cg: "continuous_on UNIV (convolution (mollifier k) g)"
      by (rule mollified_continuous[OF gi])
    have cgm: "convolution (mollifier k) g \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF cg])
    have Bm: "?B \<in> borel_measurable borel" using cgm gm by measurable
    have cgi: "integrable lborel (\<lambda>x. \<bar>convolution (mollifier k) g x\<bar> powr p)"
      by (rule mollified_Lp_bounds(1)[OF k p gi gpi])
    have Big: "integrable lborel (\<lambda>x. \<bar>?B x\<bar> powr p)"
      by (rule Lp_diff_integrable[OF p _ _ cgi gpi]) (use cgm gm in measurable)
    have Ce: "Lp_seminorm p ?Q ?C < e/4"
      using Lp_seminorm_restrict_le[OF pp Sm gfm gfi] gfe by linarith
    have Ai: "integrable ?Q (\<lambda>x. \<bar>?A x\<bar> powr p)"
      by (rule integrable_powr_restrict_gen[OF pp Sm Am Aig])
    have Bi: "integrable ?Q (\<lambda>x. \<bar>?B x\<bar> powr p)"
      by (rule integrable_powr_restrict_gen[OF pp Sm Bm Big])
    have Ci: "integrable ?Q (\<lambda>x. \<bar>?C x\<bar> powr p)"
      by (rule integrable_powr_restrict_gen[OF pp Sm gfm gfi])
    have AmQ: "?A \<in> borel_measurable ?Q" by (rule borel_measurable_lebesgue_onI[OF Am])
    have BmQ: "?B \<in> borel_measurable ?Q" by (rule borel_measurable_lebesgue_onI[OF Bm])
    have CmQ: "?C \<in> borel_measurable ?Q" by (rule borel_measurable_lebesgue_onI[OF gfm])
    have split: "(\<lambda>x. ?A x+?B x+?C x) =
        (\<lambda>x. convolution (mollifier k) f x-f x)"
      by (simp add: mollified_diff[OF fi gi])
    have le: "Lp_seminorm p ?Q (\<lambda>x. convolution (mollifier k) f x-f x) \<le>
        Lp_seminorm p ?Q ?A + Lp_seminorm p ?Q ?B + Lp_seminorm p ?Q ?C"
      using Lp_triangle_three[OF p AmQ BmQ CmQ Ai Bi Ci] by (simp only: split)
    show "dist (Lp_seminorm p ?Q (\<lambda>x. convolution (mollifier k) f x-f x)) 0 < e"
      using le Ae Be Ce e by (simp add: dist_real_def Lp_seminorm_nonneg; linarith)
  qed
qed

(* Equations (3.1) and (5.4): extend the target by zero outside its approximation domain. *)
definition zero_extension :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "zero_extension S f x = (if x \<in> S then f x else 0)"

(* Equation (3.2) and the convolution in Theorem 5.4, written as an integral over the original domain. *)
definition mollified_target ::
  "'a::euclidean_space set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "mollified_target S f k x = (\<integral>y. mollifier k (x-y)*f y \<partial>(lebesgue_on S))"

(* Equation (3.2), with (3.1); also the unnumbered convolution following (5.4). *)
lemma mollified_target_zero_extension:
  fixes S :: "'a::euclidean_space set"
  assumes S: "S \<in> sets borel"
  shows "mollified_target S f k x =
    (\<integral>y. mollifier k (x-y)*zero_extension S f y \<partial>lebesgue)"
proof -
  have SL: "S \<inter> space lebesgue \<in> sets lebesgue" using S by simp
  have "mollified_target S f k x =
      (\<integral>y. indicator S y *\<^sub>R (mollifier k (x-y)*f y) \<partial>lebesgue)"
    unfolding mollified_target_def by (rule integral_restrict_space[OF SL])
  also have "\<dots> = (\<integral>y. mollifier k (x-y)*zero_extension S f y \<partial>lebesgue)"
    by (rule Bochner_Integration.integral_cong[OF refl])
       (simp add: indicator_def zero_extension_def split: if_splits)
  finally show ?thesis .
qed

(* Auxiliary for Theorems 3.2 and 5.4: compact support makes every Lp target integrable for p >= 1. *)
lemma compact_Lp_imp_L1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes p: "1 \<le> p" and fm: "f \<in> borel_measurable borel"
    and fpi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
    and fs: "\<And>x. R < norm x \<Longrightarrow> f x = 0"
  shows "integrable lborel f"
proof -
  have ind: "integrable lborel (indicator (cball (0::'a) R) :: 'a \<Rightarrow> real)"
    by (rule integrable_real_indicator) (simp, rule emeasure_lborel_cball_finite)
  have dom: "integrable lborel (\<lambda>x. indicator (cball 0 R) x + \<bar>f x\<bar> powr p)"
    using ind fpi by simp
  have pow: "\<And>x. \<bar>f x\<bar> \<le> 1 + \<bar>f x\<bar> powr p"
  proof -
    fix x
    show "\<bar>f x\<bar> \<le> 1 + \<bar>f x\<bar> powr p"
    proof (cases "\<bar>f x\<bar> \<le> 1")
      case True then show ?thesis using powr_ge_zero[of "\<bar>f x\<bar>" p] by linarith
    next
      case False
      have "\<bar>f x\<bar> powr 1 \<le> \<bar>f x\<bar> powr p"
        by (rule powr_mono) (use p False in auto)
      then show ?thesis by (simp; linarith)
    qed
  qed
  show ?thesis
    by (rule Bochner_Integration.integrable_bound[OF dom])
       (use fm in measurable, intro AE_I2,
        use pow fs p in \<open>auto simp: indicator_def\<close>)
qed

(* Auxiliary for Theorems 3.2 and 5.4: the coefficient integrals are independent of the Borel representative. *)
lemma mollified_target_representative:
  fixes S :: "'a::euclidean_space set" and f g :: "'a \<Rightarrow> real"
  assumes S: "S \<in> sets borel" and gm: "g \<in> borel_measurable borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and eq: "AE x in lebesgue_on S. f x = g x"
  shows "mollified_target S f k =
    convolution (mollifier k) (zero_extension S g)"
proof (rule ext)
  fix x
  have gmS: "g \<in> borel_measurable (lebesgue_on S)"
    by (rule borel_measurable_lebesgue_onI[OF gm])
  have rmS: "(\<lambda>y. mollifier k (x-y)) \<in> borel_measurable (lebesgue_on S)"
    by (rule borel_measurable_lebesgue_onI) measurable
  have eqint: "mollified_target S f k x = mollified_target S g k x"
    unfolding mollified_target_def
    by (rule Bochner_Integration.integral_cong_AE)
       (use rmS fm in measurable, use rmS gmS in measurable,
        use eq in eventually_elim, simp)
  have meas: "(\<lambda>y. mollifier k (x-y)*zero_extension S g y)
      \<in> borel_measurable lborel"
    unfolding zero_extension_def using gm S by measurable
  have "mollified_target S f k x = mollified_target S g k x" by (rule eqint)
  also have "\<dots> = (\<integral>y. mollifier k (x-y)*zero_extension S g y \<partial>lebesgue)"
    by (rule mollified_target_zero_extension[OF S])
  also have "\<dots> = convolution (mollifier k) (zero_extension S g) x"
    unfolding convolution_def by (rule integral_completion[OF meas])
  finally show "mollified_target S f k x =
      convolution (mollifier k) (zero_extension S g) x" .
qed

(* Auxiliary for Theorems 3.2 and 5.4: a Borel zero extension used only internally to prove the original target's integral formulas. *)
lemma zero_extension_representative:
  fixes S :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and Sb: "bounded S" and Sm: "S \<in> sets borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and fpi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "\<exists>F R. F \<in> borel_measurable borel \<and> integrable lborel F \<and>
    integrable lborel (\<lambda>x. \<bar>F x\<bar> powr p) \<and>
    0 \<le> R \<and> (\<forall>x. R < norm x \<longrightarrow> F x = 0) \<and>
    (AE x in lebesgue_on S. f x = F x) \<and>
    (\<forall>k. mollified_target S f k = convolution (mollifier k) F) \<and>
    zero_extension S f \<in> borel_measurable lebesgue \<and>
    (AE x in lebesgue. zero_extension S f x = F x)"
proof -
  have pp: "0 < p" using p by simp
  obtain g where gm: "g \<in> borel_measurable borel"
    and eq: "AE x in lebesgue_on S. f x = g x"
    by (rule Lp_borel_representative_on[OF Sm fm]) blast
  have gmS: "g \<in> borel_measurable (lebesgue_on S)"
    by (rule borel_measurable_lebesgue_onI[OF gm])
  have gi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>g x\<bar> powr p)"
    by (rule Lp_representative_integrable[OF fpi gmS eq])
  let ?F = "zero_extension S g"
  have Fm: "?F \<in> borel_measurable borel"
    unfolding zero_extension_def using Sm gm by measurable
  have Fpi: "integrable lborel (\<lambda>x. \<bar>?F x\<bar> powr p)"
    unfolding zero_extension_def
    by (rule integrable_powr_zero_extension_gen[OF pp Sm gm gi])
  obtain B where B: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
    using Sb unfolding bounded_iff by blast
  let ?R = "max 0 B"
  have R: "0 \<le> ?R" by simp
  have Fs: "\<And>x. ?R < norm x \<Longrightarrow> ?F x = 0"
    unfolding zero_extension_def using B by force
  have Fi: "integrable lborel ?F" by (rule compact_Lp_imp_L1[OF p Fm Fpi Fs])
  have Feq: "AE x in lebesgue_on S. f x = ?F x"
    using eq AE_space[of "lebesgue_on S"]
    by eventually_elim (simp add: zero_extension_def)
  have conv: "\<And>k. mollified_target S f k = convolution (mollifier k) ?F"
    by (rule mollified_target_representative[OF Sm gm fm eq])
  have SL: "S \<inter> space lebesgue \<in> sets lebesgue" using Sm by simp
  have zm: "(\<lambda>x. indicator S x *\<^sub>R f x) \<in> borel_measurable lebesgue"
    using borel_measurable_restrict_space_iff[OF SL, of f] fm by simp
  have zdef: "zero_extension S f = (\<lambda>x. indicator S x *\<^sub>R f x)"
    by (rule ext) (simp add: zero_extension_def indicator_def split: if_splits)
  have Zm: "zero_extension S f \<in> borel_measurable lebesgue" by (simp only: zdef zm)
  have ae: "AE x in lebesgue. x \<in> S \<longrightarrow> f x = g x"
    using eq unfolding AE_restrict_space_iff[OF SL] by simp
  have Zeq: "AE x in lebesgue. zero_extension S f x = ?F x"
    using ae by eventually_elim (simp add: zero_extension_def)
  show ?thesis by (intro exI[where x="?F"] exI[where x="?R"])
    (use Fm Fi Fpi R Fs Feq conv Zm Zeq in blast)
qed

(* Proofs of Theorems 3.2 and 5.4: the paper's actual integral formula for arbitrary Lebesgue Lp targets. *)
theorem mollified_target_Lp:
  fixes S :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and Sb: "bounded S" and Sm: "S \<in> sets borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and fpi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "\<And>k. continuous_on UNIV (mollified_target S f k)"
    "\<And>k. 0 < k \<Longrightarrow> integrable (lebesgue_on S) (\<lambda>x. \<bar>mollified_target S f k x-f x\<bar> powr p)"
    "(\<lambda>k. Lp_seminorm p (lebesgue_on S) (\<lambda>x. mollified_target S f k x-f x)) \<longlonglongrightarrow> 0"
proof -
  have pp: "0 < p" using p by simp
  obtain F R where Fm: "F \<in> borel_measurable borel" and Fi: "integrable lborel F"
    and Fpi: "integrable lborel (\<lambda>x. \<bar>F x\<bar> powr p)"
    and R: "0 \<le> R" and Fs: "\<And>x. R < norm x \<Longrightarrow> F x = 0"
    and Feq: "AE x in lebesgue_on S. f x = F x"
    and conv: "\<And>k. mollified_target S f k = convolution (mollifier k) F"
    using zero_extension_representative[OF p Sb Sm fm fpi] by blast
  have cont: "\<And>k. continuous_on UNIV (mollified_target S f k)"
    unfolding conv by (rule mollified_continuous[OF Fi])
  show "\<And>k. continuous_on UNIV (mollified_target S f k)" by (rule cont)
  have cm: "\<And>k. mollified_target S f k \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF cont])
  show "\<And>k. 0 < k \<Longrightarrow> integrable (lebesgue_on S) (\<lambda>x. \<bar>mollified_target S f k x-f x\<bar> powr p)"
  proof -
    fix k::nat assume k: "0 < k"
    have ci: "integrable lborel (\<lambda>x. \<bar>mollified_target S f k x\<bar> powr p)"
      unfolding conv by (rule mollified_Lp_bounds(1)[OF k p Fi Fpi])
    have cq: "integrable (lebesgue_on S) (\<lambda>x. \<bar>mollified_target S f k x\<bar> powr p)"
      by (rule integrable_powr_restrict_gen[OF pp Sm cm ci])
    have cmq: "mollified_target S f k \<in> borel_measurable (lebesgue_on S)"
      by (rule borel_measurable_lebesgue_onI[OF cm])
    show "integrable (lebesgue_on S) (\<lambda>x. \<bar>mollified_target S f k x-f x\<bar> powr p)"
      by (rule Lp_diff_integrable[OF p cmq fm cq fpi])
  qed
  have same: "\<And>k. Lp_seminorm p (lebesgue_on S) (\<lambda>x. mollified_target S f k x-f x) =
      Lp_seminorm p (lebesgue_on S) (\<lambda>x. convolution (mollifier k) F x-F x)"
  proof -
    fix k::nat
    have cmq: "convolution (mollifier k) F \<in> borel_measurable (lebesgue_on S)"
      using borel_measurable_lebesgue_onI[OF cm[of k]] by (simp only: conv)
    have Fmq: "F \<in> borel_measurable (lebesgue_on S)"
      by (rule borel_measurable_lebesgue_onI[OF Fm])
    have eq: "(\<integral>x. \<bar>convolution (mollifier k) F x-f x\<bar> powr p \<partial>(lebesgue_on S)) =
      (\<integral>x. \<bar>convolution (mollifier k) F x-F x\<bar> powr p \<partial>(lebesgue_on S))"
      by (rule Bochner_Integration.integral_cong_AE)
         (use cmq fm in measurable, use cmq Fmq in measurable,
          use Feq in eventually_elim, simp)
    show "Lp_seminorm p (lebesgue_on S) (\<lambda>x. mollified_target S f k x-f x) =
      Lp_seminorm p (lebesgue_on S) (\<lambda>x. convolution (mollifier k) F x-F x)"
      unfolding conv Lp_seminorm_def by (simp only: eq)
  qed
  show "(\<lambda>k. Lp_seminorm p (lebesgue_on S) (\<lambda>x. mollified_target S f k x-f x)) \<longlonglongrightarrow> 0"
    unfolding same by (rule mollifier_Lp_convergence[OF p Fm Fi Fpi R Fs Sb Sm])
qed

(* Auxiliary for Theorems 3.2 and 5.4: the smoothed zero extension remains compactly supported. *)
lemma mollified_support:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and x :: 'a
  assumes k: "0 < k" and fs: "\<And>y. R < norm y \<Longrightarrow> f y = 0"
    and far: "R+1 < norm x"
  shows "convolution (mollifier k) f x = 0"
proof -
  have zero: "\<And>y. mollifier k (x-y)*f y = 0"
  proof -
    fix y::'a
    show "mollifier k (x-y)*f y = 0"
    proof (cases "R < norm y")
      case True then show ?thesis by (simp add: fs)
    next
      case False
      have tri: "norm x \<le> norm (x-y)+norm y"
        using norm_triangle_ineq[of "x-y" y] by simp
      have kd: "1 / real k \<le> 1" using k by simp
      have "1 / real k \<le> norm (x-y)" using tri far False kd by linarith
      then have "mollifier k (x-y) = 0" by (rule mollifier_support[OF k])
      then show ?thesis by simp
    qed
  qed
  show ?thesis unfolding convolution_def by (simp only: zero integral_zero)
qed

(* Auxiliary for Theorems 3.2 and 5.4: a supported function has the same local and global Lp seminorm. *)
lemma Lp_seminorm_supported:
  fixes h :: "'a::euclidean_space \<Rightarrow> real" and S :: "'a set"
  assumes p: "0 < p" and Sm: "S \<in> sets borel"
    and hm: "h \<in> borel_measurable borel" and hs: "\<And>x. x \<notin> S \<Longrightarrow> h x = 0"
  shows "Lp_seminorm p (lebesgue_on S) h = Lp_seminorm p lborel h"
proof -
  have SL: "S \<inter> space lebesgue \<in> sets lebesgue" using Sm by simp
  have hp: "(\<lambda>x. \<bar>h x\<bar> powr p) \<in> borel_measurable lborel" using hm by measurable
  have eq: "(\<lambda>x. indicator S x *\<^sub>R (\<bar>h x\<bar> powr p)) = (\<lambda>x. \<bar>h x\<bar> powr p)"
    by (rule ext) (use p hs in \<open>auto simp: indicator_def\<close>)
  have "(\<integral>x. \<bar>h x\<bar> powr p \<partial>(lebesgue_on S)) =
      (\<integral>x. indicator S x *\<^sub>R (\<bar>h x\<bar> powr p) \<partial>lebesgue)"
    by (rule integral_restrict_space[OF SL])
  also have "\<dots> = (\<integral>x. \<bar>h x\<bar> powr p \<partial>lborel)"
    unfolding eq by (rule integral_completion[OF hp])
  finally show ?thesis unfolding Lp_seminorm_def by simp
qed

(* Proofs of Theorems 3.2 and 5.4: convergence of the mollified zero extension in Lp of the whole ambient space. *)
theorem mollifier_global_Lp_convergence:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes p: "1 \<le> p" and fm: "f \<in> borel_measurable borel"
    and fi: "integrable lborel f" and fpi: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
    and R: "0 \<le> R" and fs: "\<And>x. R < norm x \<Longrightarrow> f x = 0"
  shows "(\<lambda>k. Lp_seminorm p lborel
    (\<lambda>x. convolution (mollifier k) f x-f x)) \<longlonglongrightarrow> 0"
proof -
  let ?S = "cball (0::'a) (R+1)"
  have pp: "0 < p" using p by simp
  have Sm: "?S \<in> sets borel" by simp
  have lim: "(\<lambda>k. Lp_seminorm p (lebesgue_on ?S)
      (\<lambda>x. convolution (mollifier k) f x-f x)) \<longlonglongrightarrow> 0"
    by (rule mollifier_Lp_convergence[OF p fm fi fpi R fs bounded_cball Sm])
  have same: "\<forall>\<^sub>F k in sequentially.
      Lp_seminorm p (lebesgue_on ?S) (\<lambda>x. convolution (mollifier k) f x-f x) =
      Lp_seminorm p lborel (\<lambda>x. convolution (mollifier k) f x-f x)"
    using eventually_gt_at_top[of 0]
  proof eventually_elim
    fix k::nat assume k: "0 < k"
    have cm: "convolution (mollifier k) f \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF mollified_continuous[OF fi]])
    have hm: "(\<lambda>x. convolution (mollifier k) f x-f x) \<in> borel_measurable borel"
      using cm fm by measurable
    have hs: "\<And>x. x \<notin> ?S \<Longrightarrow> convolution (mollifier k) f x-f x = 0"
    proof -
      fix x assume x: "x \<notin> ?S"
      have far: "R+1 < norm x" using x by simp
      have fx: "f x = 0" by (rule fs) (use far in linarith)
      show "convolution (mollifier k) f x-f x = 0"
        by (simp add: mollified_support[OF k fs far] fx)
    qed
    show "Lp_seminorm p (lebesgue_on ?S) (\<lambda>x. convolution (mollifier k) f x-f x) =
      Lp_seminorm p lborel (\<lambda>x. convolution (mollifier k) f x-f x)"
      by (rule Lp_seminorm_supported[OF pp Sm hm hs])
  qed
  show ?thesis by (rule Lim_transform_eventually[OF lim same])
qed

(* Proofs of Theorems 3.2 and 5.4: whole-space Lp convergence to the original completed-Lebesgue zero extension. *)
theorem mollified_target_global_Lp:
  fixes S :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and Sb: "bounded S" and Sm: "S \<in> sets borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and fpi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "\<And>k. 0 < k \<Longrightarrow> integrable lebesgue
      (\<lambda>x. \<bar>mollified_target S f k x-zero_extension S f x\<bar> powr p)"
    "(\<lambda>k. Lp_seminorm p lebesgue
      (\<lambda>x. mollified_target S f k x-zero_extension S f x)) \<longlonglongrightarrow> 0"
proof -
  obtain F R where Fm: "F \<in> borel_measurable borel" and Fi: "integrable lborel F"
    and Fpi: "integrable lborel (\<lambda>x. \<bar>F x\<bar> powr p)"
    and R: "0 \<le> R" and Fs: "\<And>x. R < norm x \<Longrightarrow> F x = 0"
    and conv: "\<And>k. mollified_target S f k = convolution (mollifier k) F"
    and Zm: "zero_extension S f \<in> borel_measurable lebesgue"
    and Zeq: "AE x in lebesgue. zero_extension S f x = F x"
    using zero_extension_representative[OF p Sb Sm fm fpi] by blast
  have cm: "\<And>k. convolution (mollifier k) F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF mollified_continuous[OF Fi]])
  have cmL: "\<And>k. convolution (mollifier k) F \<in> borel_measurable lebesgue"
    by (rule measurable_completion) (use cm in measurable)
  have FmL: "F \<in> borel_measurable lebesgue"
    by (rule measurable_completion) (use Fm in measurable)
  show "\<And>k. 0 < k \<Longrightarrow> integrable lebesgue
      (\<lambda>x. \<bar>mollified_target S f k x-zero_extension S f x\<bar> powr p)"
  proof -
    fix k::nat assume k: "0 < k"
    have ci: "integrable lborel (\<lambda>x. \<bar>convolution (mollifier k) F x\<bar> powr p)"
      by (rule mollified_Lp_bounds(1)[OF k p Fi Fpi])
    have di: "integrable lborel (\<lambda>x. \<bar>convolution (mollifier k) F x-F x\<bar> powr p)"
      by (rule Lp_diff_integrable[OF p _ _ ci Fpi]) (use cm Fm in measurable)
    have dm: "(\<lambda>x. \<bar>convolution (mollifier k) F x-F x\<bar> powr p)
        \<in> borel_measurable lborel" using cm Fm by measurable
    have diL: "integrable lebesgue (\<lambda>x. \<bar>convolution (mollifier k) F x-F x\<bar> powr p)"
      using di by (simp only: integrable_completion[OF dm])
    show "integrable lebesgue (\<lambda>x. \<bar>mollified_target S f k x-zero_extension S f x\<bar> powr p)"
      unfolding conv by (rule integrable_cong_AE_imp[OF diL])
        (use cmL Zm in measurable, use Zeq in eventually_elim, simp)
  qed
  have same: "\<And>k. Lp_seminorm p lebesgue
      (\<lambda>x. mollified_target S f k x-zero_extension S f x) =
      Lp_seminorm p lborel (\<lambda>x. convolution (mollifier k) F x-F x)"
  proof -
    fix k::nat
    have eq: "(\<integral>x. \<bar>convolution (mollifier k) F x-zero_extension S f x\<bar> powr p \<partial>lebesgue) =
      (\<integral>x. \<bar>convolution (mollifier k) F x-F x\<bar> powr p \<partial>lebesgue)"
      by (rule Bochner_Integration.integral_cong_AE)
         (use cmL Zm in measurable, use cmL FmL in measurable,
          use Zeq in eventually_elim, simp)
    have dm: "(\<lambda>x. \<bar>convolution (mollifier k) F x-F x\<bar> powr p)
        \<in> borel_measurable lborel" using cm Fm by measurable
    show "Lp_seminorm p lebesgue (\<lambda>x. mollified_target S f k x-zero_extension S f x) =
      Lp_seminorm p lborel (\<lambda>x. convolution (mollifier k) F x-F x)"
      unfolding conv Lp_seminorm_def by (simp only: eq integral_completion[OF dm])
  qed
  show "(\<lambda>k. Lp_seminorm p lebesgue
      (\<lambda>x. mollified_target S f k x-zero_extension S f x)) \<longlonglongrightarrow> 0"
    unfolding same by (rule mollifier_global_Lp_convergence[OF p Fm Fi Fpi R Fs])
qed

(* Auxiliary for the coefficient formulas after (3.4) and in Theorem 5.4: every coefficient integral is genuinely integrable. *)
lemma mollified_target_integrand_integrable:
  fixes S :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> real" and x :: 'a
  assumes p: "1 \<le> p" and Sb: "bounded S" and Sm: "S \<in> sets borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and fpi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "integrable (lebesgue_on S) (\<lambda>y. mollifier k (x-y)*f y)"
proof -
  obtain F where Fi: "integrable lborel F"
    and eq: "AE y in lebesgue_on S. f y = F y"
    using zero_extension_representative[OF p Sb Sm fm fpi] by blast
  have bd: "\<And>y::'a. \<bar>mollifier k y\<bar> \<le> real k ^ DIM('a) / mollifier_bump_mass TYPE('a)"
    by (simp add: mollifier_nonneg mollifier_bound)
  let ?h = "\<lambda>y. mollifier k (x-y)*F y"
  have hi: "integrable lborel ?h"
    by (rule bounded_kernel_integrable[OF mollifier_measurable bd Fi])
  have hm: "?h \<in> borel_measurable lborel" using hi by measurable
  have hiL: "integrable lebesgue ?h" using hi by (simp only: integrable_completion[OF hm])
  have SL: "S \<inter> space lebesgue \<in> sets lebesgue" using Sm by simp
  have hiS: "integrable (lebesgue_on S) ?h"
    unfolding integrable_restrict_space[OF SL]
    by (rule integrable_mult_indicator) (use Sm in simp, rule hiL)
  have rm: "(\<lambda>y. mollifier k (x-y)) \<in> borel_measurable (lebesgue_on S)"
    by (rule borel_measurable_lebesgue_onI) measurable
  show ?thesis by (rule integrable_cong_AE_imp[OF hiS])
    (use rm fm in measurable, use eq in eventually_elim, simp)
qed

end
