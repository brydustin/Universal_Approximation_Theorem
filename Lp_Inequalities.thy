section \<open>Hölder and Minkowski inequalities for a Bochner-integral \<open>L\<^sup>p\<close> seminorm\<close>

theory Lp_Inequalities
  imports "HOL-Analysis.Analysis"
begin

text \<open>
  This theory is deliberately independent of \<open>Smooth_Manifolds\<close>/\<open>Bump_Function\<close> and of any
  other theory in this project, importing only \<open>HOL-Analysis.Analysis\<close> -- it exists to supply
  Hölder's and Minkowski's inequalities for the elementary Bochner-integral \<open>L\<^sup>p\<close> seminorm used
  throughout this project (\<open>Lp_norm\<close> in \<open>Lp_Approximation.thy\<close>, \<open>multivariate_Lp_norm\<close> in
  \<open>Multivariate_Approximation.thy\<close>), neither of which is available from HOL-Analysis or any
  AFP entry already used here (the AFP \<open>Lp\<close> entry has both, but hard-clashes with
  \<open>Smooth_Manifolds\<close> on a \<open>scaleR\<close> instantiation for function types -- see the project's own
  \<open>afp-lp-smooth-manifolds-scaler-clash\<close> note). The proofs below follow the standard textbook
  route (Young's inequality \<open>\<rightarrow>\<close> Hölder \<open>\<rightarrow>\<close> Minkowski), reusing \<open>Youngs_inequality\<close> from
  \<open>HOL-Analysis.Convex\<close>, which is already proved there via concavity of \<open>ln\<close>.
\<close>

text \<open>
  A Borel-measurable function is measurable for \<open>lebesgue_on S\<close>, for any \<open>S\<close>.  This is the
  single general form used throughout the project, at \<^typ>\<open>real\<close> and at
  \<open>(real,'n) vec\<close> alike; it is stated here, in the lowest layer, because
  \<^file>\<open>Lp_Approximation.thy\<close> needs it and does not import the mollifier development.
\<close>
(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma borel_measurable_lebesgue_onI:
  fixes h :: "'a::euclidean_space \<Rightarrow> real" and S :: "'a set"
  assumes h_meas: "h \<in> borel_measurable borel"
  shows "h \<in> borel_measurable (lebesgue_on S)"
proof -
  have h_lborel: "h \<in> borel_measurable lborel"
    using h_meas unfolding measurable_def by (simp add: sets_lborel)
  have h_lebesgue: "h \<in> borel_measurable lebesgue"
    using measurable_completion[OF h_lborel] .
  show ?thesis
    using measurable_restrict_space1[OF h_lebesgue] .
qed

definition Lp_seminorm :: "real \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "Lp_seminorm p M g = (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1 / p)"

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma Lp_seminorm_nonneg: "Lp_seminorm p M g \<ge> 0"
  unfolding Lp_seminorm_def by simp

subsection \<open>Hölder's inequality\<close>

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma Lp_Holder_integrable:
  fixes M :: "'a measure" and f g :: "'a \<Rightarrow> real" and p q :: real
  assumes p_gt1: "p > 1" and q_gt1: "q > 1" and pq_conj: "1 / p + 1 / q = 1"
  assumes f_meas: "f \<in> borel_measurable M" and g_meas: "g \<in> borel_measurable M"
  assumes f_intp: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes g_intq: "integrable M (\<lambda>x. \<bar>g x\<bar> powr q)"
  shows "integrable M (\<lambda>x. f x * g x)"
proof -
  have dom_int: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q)"
    using f_intp g_intq by simp
  have fg_meas: "(\<lambda>x. f x * g x) \<in> borel_measurable M"
    using f_meas g_meas by measurable
  have young_pt: "\<And>x. \<bar>f x\<bar> * \<bar>g x\<bar> \<le> \<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q"
  proof -
    fix x
    show "\<bar>f x\<bar> * \<bar>g x\<bar> \<le> \<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q"
      using Youngs_inequality[of p q "\<bar>f x\<bar>" "\<bar>g x\<bar>"] p_gt1 q_gt1 pq_conj by simp
  qed
  have bound_pt: "\<And>x. norm (f x * g x) \<le> norm (\<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q)"
  proof -
    fix x
    have step1: "norm (f x * g x) = \<bar>f x\<bar> * \<bar>g x\<bar>"
      by (simp add: abs_mult)
    have step2: "\<bar>f x\<bar> * \<bar>g x\<bar> \<le> \<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q"
      using young_pt by simp
    have nn: "\<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q \<ge> 0"
      using p_gt1 q_gt1 by simp
    have step3: "\<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q = norm (\<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q)"
      using nn by simp
    show "norm (f x * g x) \<le> norm (\<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q)"
      using step1 step2 step3 by linarith
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF dom_int fg_meas])
    show "AE x in M. norm (f x * g x) \<le> norm (\<bar>f x\<bar> powr p / p + \<bar>g x\<bar> powr q / q)"
      using bound_pt by (intro AE_I2) simp
  qed
qed

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
theorem Lp_Holder_inequality:
  fixes M :: "'a measure" and f g :: "'a \<Rightarrow> real" and p q :: real
  assumes p_gt1: "p > 1" and q_gt1: "q > 1" and pq_conj: "1 / p + 1 / q = 1"
  assumes f_meas: "f \<in> borel_measurable M" and g_meas: "g \<in> borel_measurable M"
  assumes f_intp: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes g_intq: "integrable M (\<lambda>x. \<bar>g x\<bar> powr q)"
  shows "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> Lp_seminorm p M f * Lp_seminorm q M g"
proof -
  define A where "A = Lp_seminorm p M f"
  define B where "B = Lp_seminorm q M g"
  have A_nonneg: "A \<ge> 0" unfolding A_def by (rule Lp_seminorm_nonneg)
  have B_nonneg: "B \<ge> 0" unfolding B_def by (rule Lp_seminorm_nonneg)
  have Ap_eq: "A powr p = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
    unfolding A_def Lp_seminorm_def using p_gt1 by (simp add: powr_powr)
  have Bq_eq: "B powr q = (\<integral>x. \<bar>g x\<bar> powr q \<partial>M)"
    unfolding B_def Lp_seminorm_def using q_gt1 by (simp add: powr_powr)
  have fg_int: "integrable M (\<lambda>x. f x * g x)"
    using Lp_Holder_integrable[OF p_gt1 q_gt1 pq_conj f_meas g_meas f_intp g_intq] .
  have fg_abs_int: "integrable M (\<lambda>x. \<bar>f x * g x\<bar>)"
    using fg_int by simp
  have goal_eq: "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> A * B \<Longrightarrow> ?thesis"
    unfolding A_def B_def by simp
  consider (zeroA) "A = 0" | (zeroB) "A \<noteq> 0 \<and> B = 0" | (pos) "A > 0 \<and> B > 0"
    using A_nonneg B_nonneg by linarith
  then have "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> A * B"
  proof cases
    case zeroA
    have "(\<integral>x. \<bar>f x\<bar> powr p \<partial>M) = 0"
      using zeroA Ap_eq by simp
    then have "AE x in M. \<bar>f x\<bar> powr p = 0"
      using f_intp integral_nonneg_eq_0_iff_AE[OF f_intp] by simp
    then have "AE x in M. f x = 0"
      by simp
    then have "AE x in M. \<bar>f x * g x\<bar> = 0"
      by (auto elim: eventually_mono)
    then have "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) = 0"
      by (rule integral_eq_zero_AE)
    then show ?thesis using zeroA A_nonneg B_nonneg by simp
  next
    case zeroB
    have "(\<integral>x. \<bar>g x\<bar> powr q \<partial>M) = 0"
      using zeroB Bq_eq by simp
    then have "AE x in M. \<bar>g x\<bar> powr q = 0"
      using g_intq integral_nonneg_eq_0_iff_AE[OF g_intq] by simp
    then have "AE x in M. g x = 0"
      by simp
    then have "AE x in M. \<bar>f x * g x\<bar> = 0"
      by (auto elim: eventually_mono)
    then have "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) = 0"
      by (rule integral_eq_zero_AE)
    then show ?thesis using zeroB A_nonneg B_nonneg by simp
  next
    case pos
    then have A_pos: "A > 0" and B_pos: "B > 0" by auto
    define F where "F = (\<lambda>x. \<bar>f x\<bar> / A)"
    define G where "G = (\<lambda>x. \<bar>g x\<bar> / B)"
    have F_nonneg: "\<And>x. F x \<ge> 0" unfolding F_def using A_pos by simp
    have G_nonneg: "\<And>x. G x \<ge> 0" unfolding G_def using B_pos by simp
    have F_meas: "F \<in> borel_measurable M"
      unfolding F_def using f_meas by measurable
    have G_meas: "G \<in> borel_measurable M"
      unfolding G_def using g_meas by measurable
    have Fp_eq: "\<And>x. F x powr p = \<bar>f x\<bar> powr p / A powr p"
      unfolding F_def using A_pos by (simp add: powr_divide)
    have Gq_eq: "\<And>x. G x powr q = \<bar>g x\<bar> powr q / B powr q"
      unfolding G_def using B_pos by (simp add: powr_divide)
    have Fp_int: "integrable M (\<lambda>x. F x powr p)"
      using f_intp Fp_eq by simp
    have Gq_int: "integrable M (\<lambda>x. G x powr q)"
      using g_intq Gq_eq by simp
    have Fp_integral: "(\<integral>x. F x powr p \<partial>M) = 1"
    proof -
      have "(\<integral>x. F x powr p \<partial>M) = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) / A powr p"
        by (simp add: Fp_eq)
      also have "\<dots> = A powr p / A powr p"
        using Ap_eq by simp
      also have "\<dots> = 1"
        using A_pos by simp
      finally show ?thesis .
    qed
    have Gq_integral: "(\<integral>x. G x powr q \<partial>M) = 1"
    proof -
      have "(\<integral>x. G x powr q \<partial>M) = (\<integral>x. \<bar>g x\<bar> powr q \<partial>M) / B powr q"
        by (simp add: Gq_eq)
      also have "\<dots> = B powr q / B powr q"
        using Bq_eq by simp
      also have "\<dots> = 1"
        using B_pos by simp
      finally show ?thesis .
    qed
    have young_pt: "\<And>x. F x * G x \<le> F x powr p / p + G x powr q / q"
    proof -
      fix x
      show "F x * G x \<le> F x powr p / p + G x powr q / q"
        using Youngs_inequality[of p q "F x" "G x"] p_gt1 q_gt1 pq_conj F_nonneg G_nonneg
        by simp
    qed
    have rhs_int: "integrable M (\<lambda>x. F x powr p / p + G x powr q / q)"
      using Fp_int Gq_int by simp
    have FG_meas: "(\<lambda>x. F x * G x) \<in> borel_measurable M"
      using F_meas G_meas by measurable
    have bound_pt_FG: "\<And>x. norm (F x * G x) \<le> norm (F x powr p / p + G x powr q / q)"
    proof -
      fix x
      have step1: "norm (F x * G x) = F x * G x"
        using F_nonneg G_nonneg by simp
      have step2: "F x * G x \<le> F x powr p / p + G x powr q / q"
        using young_pt by simp
      have nn: "F x powr p / p + G x powr q / q \<ge> 0"
        using p_gt1 q_gt1 by simp
      have step3: "F x powr p / p + G x powr q / q = norm (F x powr p / p + G x powr q / q)"
        using nn by simp
      show "norm (F x * G x) \<le> norm (F x powr p / p + G x powr q / q)"
        using step1 step2 step3 by linarith
    qed
    have FG_int: "integrable M (\<lambda>x. F x * G x)"
    proof (rule Bochner_Integration.integrable_bound[OF rhs_int FG_meas])
      show "AE x in M. norm (F x * G x) \<le> norm (F x powr p / p + G x powr q / q)"
        using bound_pt_FG by (intro AE_I2) simp
    qed
    have FG_bound: "(\<integral>x. F x * G x \<partial>M) \<le> (\<integral>x. F x powr p / p + G x powr q / q \<partial>M)"
      using FG_int rhs_int young_pt by (intro integral_mono_AE, auto intro:)
    have rhs_eq: "(\<integral>x. F x powr p / p + G x powr q / q \<partial>M) = 1"
      using Fp_integral Gq_integral Fp_int Gq_int p_gt1 q_gt1 pq_conj by simp
    have FG_le_1: "(\<integral>x. F x * G x \<partial>M) \<le> 1"
      using FG_bound rhs_eq by simp
    have FG_eq: "(\<integral>x. F x * G x \<partial>M) = (\<integral>x. \<bar>f x * g x\<bar> \<partial>M) / (A * B)"
    proof -
      have "\<And>x. F x * G x = \<bar>f x * g x\<bar> / (A * B)"
        unfolding F_def G_def using A_pos B_pos by (simp add: abs_mult)
      then show ?thesis by simp
    qed
    have ratio_le_1: "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) / (A * B) \<le> 1"
      using FG_le_1 FG_eq by simp
    show ?thesis
      using ratio_le_1 A_pos B_pos by (simp add: divide_le_eq)
  qed
  then show ?thesis using goal_eq by simp
qed

subsection \<open>Minkowski's inequality\<close>

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma sum_powr_le_two_powr:
  fixes a b p :: real
  assumes p_ge1: "p \<ge> 1" and a_nonneg: "a \<ge> 0" and b_nonneg: "b \<ge> 0"
  shows "(a + b) powr p \<le> 2 powr (p - 1) * (a powr p + b powr p)"
proof -
  have two_pow_ge1: "(2::real) powr (p - 1) \<ge> 1"
  proof -
    have "(2::real) powr 0 \<le> 2 powr (p - 1)"
      by (rule powr_mono) (use p_ge1 in auto)
    then show ?thesis by simp
  qed
  show ?thesis
  proof (cases "a = 0 \<or> b = 0")
    case True
    then show ?thesis
    proof
      assume a0: "a = 0"
      have e1: "(a + b) powr p = b powr p" using a0 by simp
      have step: "1 * b powr p \<le> 2 powr (p - 1) * b powr p"
      proof (rule mult_right_mono)
        show "(1::real) \<le> 2 powr (p - 1)" using two_pow_ge1 by simp
        show "0 \<le> b powr p" by simp
      qed
      have e2: "b powr p \<le> 2 powr (p - 1) * b powr p" using step by simp
      have e3: "2 powr (p - 1) * b powr p \<le> 2 powr (p - 1) * (a powr p + b powr p)"
        using a0 by simp
      show ?thesis using e1 e2 e3 by linarith
    next
      assume b0: "b = 0"
      have e1: "(a + b) powr p = a powr p" using b0 by simp
      have step: "1 * a powr p \<le> 2 powr (p - 1) * a powr p"
      proof (rule mult_right_mono)
        show "(1::real) \<le> 2 powr (p - 1)" using two_pow_ge1 by simp
        show "0 \<le> a powr p" by simp
      qed
      have e2: "a powr p \<le> 2 powr (p - 1) * a powr p" using step by simp
      have e3: "2 powr (p - 1) * a powr p \<le> 2 powr (p - 1) * (a powr p + b powr p)"
        using b0 by simp
      show ?thesis using e1 e2 e3 by linarith
    qed
  next
    case False
    then have a_pos: "a > 0" and b_pos: "b > 0" using a_nonneg b_nonneg by auto
    have conv: "(a / 2 + b / 2) powr p \<le> (a powr p + b powr p) / 2"
    proof -
      have raw: "((1 - (1/2)) *\<^sub>R a + (1/2) *\<^sub>R b) powr p
          \<le> (1 - (1/2)) * (a powr p) + (1/2) * (b powr p)"
        by (rule convex_onD[OF powr_convex[OF p_ge1]]) (use a_pos b_pos in auto)
      then show ?thesis by simp
    qed
    have conv': "((a + b) / 2) powr p \<le> (a powr p + b powr p) / 2"
    proof -
      have arg_eq: "(a + b) / 2 = a / 2 + b / 2" by simp
      have lhs_eq: "((a + b) / 2) powr p = (a / 2 + b / 2) powr p"
        using arg_cong[OF arg_eq, of "\<lambda>t. t powr p"] .
      show ?thesis using lhs_eq conv by simp
    qed
    have e1: "2 powr p * ((a + b) / 2) powr p = (a + b) powr p"
    proof -
      have s2: "(2::real) * ((a + b) / 2) = a + b" by simp
      have s1: "(2 * ((a + b) / 2)) powr p = (a + b) powr p"
        using arg_cong[OF s2, of "\<lambda>t. t powr p"] .
      have s3: "2 powr p * ((a + b) / 2) powr p = (2 * ((a + b) / 2)) powr p"
        by (rule powr_mult[symmetric])
      show ?thesis using s1 s3 by simp
    qed
    have e2: "2 powr p * ((a + b) / 2) powr p \<le> 2 powr p * ((a powr p + b powr p) / 2)"
    proof (rule mult_left_mono)
      show "((a + b) / 2) powr p \<le> (a powr p + b powr p) / 2" using conv' .
      show "(0::real) \<le> 2 powr p" by simp
    qed
    have e3: "2 powr p * ((a powr p + b powr p) / 2) = 2 powr (p - 1) * (a powr p + b powr p)"
    proof -
      have s1: "(2::real) powr p = 2 * 2 powr (p - 1)"
      proof -
        have "2 powr ((p - 1) + 1) = 2 powr (p - 1) * 2 powr 1"
          by (rule powr_add)
        then show ?thesis by simp
      qed
      have lhs_eq: "2 powr p * ((a powr p + b powr p) / 2)
          = (2 * 2 powr (p - 1)) * ((a powr p + b powr p) / 2)"
        using arg_cong[OF s1, of "\<lambda>t. t * ((a powr p + b powr p) / 2)"] .
      show ?thesis using lhs_eq by (simp add: field_simps)
    qed
    show ?thesis using e1 e2 e3 by linarith
  qed
qed

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
theorem Lp_Minkowski_integrable:
  fixes M :: "'a measure" and f g :: "'a \<Rightarrow> real" and p :: real
  assumes p_ge1: "p \<ge> 1"
  assumes f_meas: "f \<in> borel_measurable M" and g_meas: "g \<in> borel_measurable M"
  assumes f_intp: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes g_intp: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "integrable M (\<lambda>x. \<bar>f x + g x\<bar> powr p)"
proof -
  have dom_meas: "(\<lambda>x. \<bar>f x + g x\<bar> powr p) \<in> borel_measurable M"
    using f_meas g_meas by measurable
  have dom_int: "integrable M (\<lambda>x. 2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p))"
    using f_intp g_intp by simp
  have bound_pt: "\<And>x. norm (\<bar>f x + g x\<bar> powr p)
      \<le> norm (2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p))"
  proof -
    fix x
    have s2: "\<bar>f x + g x\<bar> powr p \<le> (\<bar>f x\<bar> + \<bar>g x\<bar>) powr p"
    proof (rule powr_mono2)
      show "0 \<le> p" using p_ge1 by simp
      show "0 \<le> \<bar>f x + g x\<bar>" by simp
      show "\<bar>f x + g x\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" by simp
    qed
    have s3: "(\<bar>f x\<bar> + \<bar>g x\<bar>) powr p \<le> 2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p)"
      using sum_powr_le_two_powr[OF p_ge1 abs_ge_zero abs_ge_zero] .
    have nn: "2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p) \<ge> 0" by simp
    have step: "\<bar>f x + g x\<bar> powr p \<le> 2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p)"
      using s2 s3 by linarith
    show "norm (\<bar>f x + g x\<bar> powr p) \<le> norm (2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p))"
      using step nn by simp
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF dom_int dom_meas])
    show "AE x in M. norm (\<bar>f x + g x\<bar> powr p)
        \<le> norm (2 powr (p - 1) * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p))"
      using bound_pt by (intro AE_I2) simp
  qed
qed

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
theorem Lp_Minkowski_inequality:
  fixes M :: "'a measure" and f g :: "'a \<Rightarrow> real" and p :: real
  assumes p_ge1: "p \<ge> 1"
  assumes f_meas: "f \<in> borel_measurable M" and g_meas: "g \<in> borel_measurable M"
  assumes f_intp: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes g_intp: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "Lp_seminorm p M (\<lambda>x. f x + g x) \<le> Lp_seminorm p M f + Lp_seminorm p M g"
proof (cases "p = 1")
  case True
  have seminorm_eq: "\<And>h::'a\<Rightarrow>real. Lp_seminorm 1 M h = (\<integral>x. \<bar>h x\<bar> \<partial>M)"
    unfolding Lp_seminorm_def by simp
  have f_int1: "integrable M (\<lambda>x. \<bar>f x\<bar>)" using f_intp True by simp
  have g_int1: "integrable M (\<lambda>x. \<bar>g x\<bar>)" using g_intp True by simp
  have fg_int1: "integrable M (\<lambda>x. \<bar>f x + g x\<bar>)"
    using Lp_Minkowski_integrable[OF p_ge1 f_meas g_meas f_intp g_intp] True by simp
  have tri_pt: "\<And>x. \<bar>f x + g x\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" by simp
  have main: "(\<integral>x. \<bar>f x + g x\<bar> \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> + \<bar>g x\<bar> \<partial>M)"
    using fg_int1 f_int1 g_int1 tri_pt by (intro integral_mono_AE, auto intro:)
  have split: "(\<integral>x. \<bar>f x\<bar> + \<bar>g x\<bar> \<partial>M) = (\<integral>x. \<bar>f x\<bar> \<partial>M) + (\<integral>x. \<bar>g x\<bar> \<partial>M)"
    using f_int1 g_int1 by simp
  show ?thesis
    using main split seminorm_eq True by simp
next
  case False
  then have p_gt1: "p > 1" using p_ge1 by simp
  define q where "q = p / (p - 1)"
  have p_minus_1_pos: "p - 1 > 0" using p_gt1 by simp
  have q_gt1: "q > 1"
    unfolding q_def using p_gt1 p_minus_1_pos by (simp add: less_divide_eq)
  have pq_conj: "1 / p + 1 / q = 1"
  proof -
    have "1 / q = (p - 1) / p"
      unfolding q_def using p_minus_1_pos by (simp add: field_simps)
    then show ?thesis using p_gt1 by (simp add: field_simps)
  qed
  have p1_q_eq: "(p - 1) * q = p"
    unfolding q_def using p_minus_1_pos by (simp add: field_simps)
  have fg_intp: "integrable M (\<lambda>x. \<bar>f x + g x\<bar> powr p)"
    using Lp_Minkowski_integrable[OF p_ge1 f_meas g_meas f_intp g_intp] .
  show ?thesis
  proof (cases "Lp_seminorm p M (\<lambda>x. f x + g x) = 0")
    case True
    then show ?thesis
      using Lp_seminorm_nonneg[of p M f] Lp_seminorm_nonneg[of p M g] by simp
  next
    case False
    then have norm_fg_pos: "Lp_seminorm p M (\<lambda>x. f x + g x) > 0"
      using Lp_seminorm_nonneg[of p M "\<lambda>x. f x + g x"] by simp
    define h where "h = (\<lambda>x. \<bar>f x + g x\<bar> powr (p - 1))"
    have h_nonneg: "\<And>x. h x \<ge> 0" unfolding h_def by simp
    have h_meas: "h \<in> borel_measurable M"
      unfolding h_def using f_meas g_meas by measurable
    have h_intq: "integrable M (\<lambda>x. \<bar>h x\<bar> powr q)"
    proof -
      have s1: "\<And>x. \<bar>h x\<bar> powr q = \<bar>f x + g x\<bar> powr ((p - 1) * q)"
        unfolding h_def using h_nonneg by (simp add: powr_powr)
      have s2: "\<And>x. \<bar>f x + g x\<bar> powr ((p - 1) * q) = \<bar>f x + g x\<bar> powr p"
      proof -
        fix x
        show "\<bar>f x + g x\<bar> powr ((p - 1) * q) = \<bar>f x + g x\<bar> powr p"
          using arg_cong[OF p1_q_eq, of "\<lambda>e. \<bar>f x + g x\<bar> powr e"] .
      qed
      show ?thesis using s1 s2 fg_intp by simp
    qed
    have intfgp_nonneg: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) \<ge> 0"
      by (rule Bochner_Integration.integral_nonneg) simp
    have h_seminorm: "Lp_seminorm q M h powr q = (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M)"
    proof -
      have s1: "Lp_seminorm q M h powr q = (\<integral>x. \<bar>h x\<bar> powr q \<partial>M)"
        unfolding Lp_seminorm_def using h_intq q_gt1 by (simp add: powr_powr)
      have s2: "\<And>x. \<bar>h x\<bar> powr q = \<bar>f x + g x\<bar> powr p"
      proof -
        fix x
        have t1: "\<bar>h x\<bar> powr q = \<bar>f x + g x\<bar> powr ((p - 1) * q)"
          unfolding h_def using h_nonneg by (simp add: powr_powr)
        have t2: "\<bar>f x + g x\<bar> powr ((p - 1) * q) = \<bar>f x + g x\<bar> powr p"
          using arg_cong[OF p1_q_eq, of "\<lambda>e. \<bar>f x + g x\<bar> powr e"] .
        show "\<bar>h x\<bar> powr q = \<bar>f x + g x\<bar> powr p" using t1 t2 by simp
      qed
      show ?thesis using s1 s2 by simp
    qed
    have h_seminorm_eq: "Lp_seminorm q M h = Lp_seminorm p M (\<lambda>x. f x + g x) powr (p / q)"
    proof -
      have s1: "Lp_seminorm q M h = (Lp_seminorm q M h powr q) powr (1 / q)"
        using Lp_seminorm_nonneg[of q M h] q_gt1 by (simp add: powr_powr)
      have s2: "(Lp_seminorm q M h powr q) powr (1 / q)
          = (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / q)"
        using h_seminorm by simp
      have s3: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / q)
          = ((\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / p)) powr (p / q)"
      proof -
        have exp_eq: "1 / p * (p / q) = 1 / q" using p_gt1 by (simp add: field_simps)
        have u1: "((\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / p)) powr (p / q)
            = (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / p * (p / q))"
          by (rule powr_powr)
        have u2: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / p * (p / q))
            = (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1 / q)"
          using arg_cong[OF exp_eq, of "\<lambda>e. (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr e"] .
        show ?thesis using u1 u2 by simp
      qed
      show ?thesis
        using s1 s2 s3 unfolding Lp_seminorm_def by simp
    qed
    have split_eq: "\<And>x. \<bar>f x + g x\<bar> powr p = \<bar>f x + g x\<bar> * h x"
    proof -
      fix x
      have s1: "\<bar>f x + g x\<bar> powr p = \<bar>f x + g x\<bar> powr (1 + (p - 1))" by simp
      have s2: "\<bar>f x + g x\<bar> powr (1 + (p - 1))
          = \<bar>f x + g x\<bar> powr 1 * \<bar>f x + g x\<bar> powr (p - 1)"
        by (rule powr_add)
      show "\<bar>f x + g x\<bar> powr p = \<bar>f x + g x\<bar> * h x"
        unfolding h_def using s1 s2 by simp
    qed
    have pt_bound: "\<And>x. \<bar>f x + g x\<bar> * h x \<le> \<bar>f x\<bar> * h x + \<bar>g x\<bar> * h x"
    proof -
      fix x
      have tri: "\<bar>f x + g x\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" by simp
      have step: "\<bar>f x + g x\<bar> * h x \<le> (\<bar>f x\<bar> + \<bar>g x\<bar>) * h x"
      proof (rule mult_right_mono)
        show "\<bar>f x + g x\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" using tri .
        show "0 \<le> h x" using h_nonneg by simp
      qed
      show "\<bar>f x + g x\<bar> * h x \<le> \<bar>f x\<bar> * h x + \<bar>g x\<bar> * h x"
        using step by (simp add: ring_distribs)
    qed
    have fh_int: "integrable M (\<lambda>x. f x * h x)"
      using Lp_Holder_integrable[OF p_gt1 q_gt1 pq_conj f_meas h_meas f_intp h_intq] .
    have gh_int: "integrable M (\<lambda>x. g x * h x)"
      using Lp_Holder_integrable[OF p_gt1 q_gt1 pq_conj g_meas h_meas g_intp h_intq] .
    have fabsh_int: "integrable M (\<lambda>x. \<bar>f x\<bar> * h x)"
    proof -
      have "\<And>x. \<bar>f x\<bar> * h x = \<bar>f x * h x\<bar>"
        using h_nonneg by (simp add: abs_mult)
      then show ?thesis using fh_int by simp
    qed
    have gabsh_int: "integrable M (\<lambda>x. \<bar>g x\<bar> * h x)"
    proof -
      have "\<And>x. \<bar>g x\<bar> * h x = \<bar>g x * h x\<bar>"
        using h_nonneg by (simp add: abs_mult)
      then show ?thesis using gh_int by simp
    qed
    have fgh_int: "integrable M (\<lambda>x. \<bar>f x\<bar> * h x + \<bar>g x\<bar> * h x)"
      using fabsh_int gabsh_int by simp
    have fgabsh_int: "integrable M (\<lambda>x. \<bar>f x + g x\<bar> * h x)"
      using fg_intp split_eq by simp
    have main_step: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M)
        \<le> (\<integral>x. \<bar>f x\<bar> * h x \<partial>M) + (\<integral>x. \<bar>g x\<bar> * h x \<partial>M)"
    proof -
      have e1: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) = (\<integral>x. \<bar>f x + g x\<bar> * h x \<partial>M)"
        using split_eq by simp
      have e2: "(\<integral>x. \<bar>f x + g x\<bar> * h x \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> * h x + \<bar>g x\<bar> * h x \<partial>M)"
        using fgabsh_int fgh_int pt_bound by (intro integral_mono_AE, auto) 
      have e3: "(\<integral>x. \<bar>f x\<bar> * h x + \<bar>g x\<bar> * h x \<partial>M)
          = (\<integral>x. \<bar>f x\<bar> * h x \<partial>M) + (\<integral>x. \<bar>g x\<bar> * h x \<partial>M)"
        using fabsh_int gabsh_int by simp
      show ?thesis using e1 e2 e3 by linarith
    qed
    have fh_holder: "(\<integral>x. \<bar>f x\<bar> * h x \<partial>M) \<le> Lp_seminorm p M f * Lp_seminorm q M h"
    proof -
      have e1: "(\<integral>x. \<bar>f x\<bar> * h x \<partial>M) = (\<integral>x. \<bar>f x * h x\<bar> \<partial>M)"
        using h_nonneg by (simp add: abs_mult)
      have e2: "(\<integral>x. \<bar>f x * h x\<bar> \<partial>M) \<le> Lp_seminorm p M f * Lp_seminorm q M h"
        using Lp_Holder_inequality[OF p_gt1 q_gt1 pq_conj f_meas h_meas f_intp h_intq] .
      show ?thesis using e1 e2 by simp
    qed
    have gh_holder: "(\<integral>x. \<bar>g x\<bar> * h x \<partial>M) \<le> Lp_seminorm p M g * Lp_seminorm q M h"
    proof -
      have e1: "(\<integral>x. \<bar>g x\<bar> * h x \<partial>M) = (\<integral>x. \<bar>g x * h x\<bar> \<partial>M)"
        using h_nonneg by (simp add: abs_mult)
      have e2: "(\<integral>x. \<bar>g x * h x\<bar> \<partial>M) \<le> Lp_seminorm p M g * Lp_seminorm q M h"
        using Lp_Holder_inequality[OF p_gt1 q_gt1 pq_conj g_meas h_meas g_intp h_intq] .
      show ?thesis using e1 e2 by simp
    qed
    have combined: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M)
        \<le> (Lp_seminorm p M f + Lp_seminorm p M g) * Lp_seminorm q M h"
    proof -
      have "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M)
          \<le> Lp_seminorm p M f * Lp_seminorm q M h + Lp_seminorm p M g * Lp_seminorm q M h"
        using main_step fh_holder gh_holder by linarith
      then show ?thesis by (simp add: ring_distribs)
    qed
    have norm_p_eq: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) = Lp_seminorm p M (\<lambda>x. f x + g x) powr p"
      unfolding Lp_seminorm_def using fg_intp p_gt1 by (simp add: powr_powr)
    have key_ineq: "Lp_seminorm p M (\<lambda>x. f x + g x) powr p
        \<le> (Lp_seminorm p M f + Lp_seminorm p M g) * Lp_seminorm p M (\<lambda>x. f x + g x) powr (p / q)"
      using combined norm_p_eq h_seminorm_eq by simp
    have exponent_eq: "p - p / q = 1"
    proof -
      have s1: "1 / q = (p - 1) / p" using pq_conj p_gt1 by (simp add: field_simps)
      have s2: "p / q = p - 1"
        using s1 p_gt1 p_minus_1_pos by (simp add: field_simps)
      show ?thesis using s2 by simp
    qed
    have divide_step: "Lp_seminorm p M (\<lambda>x. f x + g x) powr (p - p / q)
        \<le> Lp_seminorm p M f + Lp_seminorm p M g"
    proof -
      have Y_pos: "Lp_seminorm p M (\<lambda>x. f x + g x) powr (p / q) > 0"
        using norm_fg_pos by simp
      have div_step: "Lp_seminorm p M (\<lambda>x. f x + g x) powr p
          / Lp_seminorm p M (\<lambda>x. f x + g x) powr (p / q)
          \<le> Lp_seminorm p M f + Lp_seminorm p M g"
      proof -
        have "Lp_seminorm p M (\<lambda>x. f x + g x) powr p
            \<le> (Lp_seminorm p M f + Lp_seminorm p M g) * Lp_seminorm p M (\<lambda>x. f x + g x) powr (p / q)"
          using key_ineq .
        then show ?thesis
          using Y_pos by (simp add: pos_divide_le_eq mult.commute)
      qed
      have powr_diff_eq: "Lp_seminorm p M (\<lambda>x. f x + g x) powr p
          / Lp_seminorm p M (\<lambda>x. f x + g x) powr (p / q)
          = Lp_seminorm p M (\<lambda>x. f x + g x) powr (p - p / q)"
        using norm_fg_pos by (simp add: powr_diff)
      show ?thesis using div_step powr_diff_eq by simp
    qed
    show ?thesis
    proof -
      have "Lp_seminorm p M (\<lambda>x. f x + g x) powr 1 \<le> Lp_seminorm p M f + Lp_seminorm p M g"
        using divide_step exponent_eq by simp
      then show ?thesis
        using norm_fg_pos by simp
    qed
  qed
qed

section \<open>The extended-real \<open>L\<^sup>p\<close> norm\<close>

text \<open>
  \<^const>\<open>Lp_seminorm\<close> above, and \<^term>\<open>Lp_norm\<close> in \<open>Lp_Approximation.thy\<close>, are
  \<^typ>\<open>real\<close>-valued, so a divergent integral has no value to take and must be excluded by
  an integrability guard.  The textbook object is instead \<open>[0,\<infinity>]\<close>-valued: for measurable
  \<open>g\<close> the quantity \<open>(\<integral>\<bar>g\<bar>\<^sup>p)\<^sup>1\<^sup>/\<^sup>p\<close> always has a value, namely \<open>\<infinity>\<close> when the integral
  diverges.  \<open>Lp_enorm\<close> below is that object.

  Note that moving to \<^typ>\<open>ennreal\<close> removes the need to exclude \<^emph>\<open>divergence\<close> but
  \<^bold>\<open>not\<close> the need to exclude \<^emph>\<open>non-measurability\<close>: \<^const>\<open>nn_integral\<close> is total, but on a
  non-measurable argument it returns the lower integral, which may be finite and small, so
  a bound \<open>\<dots> < \<epsilon>\<close> could again hold for the wrong reason.  The guard therefore remains --
  but it weakens from integrability to measurability, which is the honest hypothesis.
\<close>

subsection \<open>A real power on \<^typ>\<open>ennreal\<close>\<close>

text \<open>
  \<^typ>\<open>ennreal\<close> carries no \<open>powr\<close> instance -- there is no \<open>ln\<close> instance to build one on --
  so the outer \<open>p\<close>-th root has to be supplied here.  Only positive exponents occur below
  (\<open>r = 1/p\<close> with \<open>p \<ge> 1\<close>), and \<open>\<infinity>\<close> is sent to \<open>\<infinity>\<close> accordingly.
\<close>

definition ennreal_powr :: "ennreal \<Rightarrow> real \<Rightarrow> ennreal" where
  "ennreal_powr x r = (if x = top then top else ennreal (enn2real x powr r))"

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma ennreal_powr_top [simp]: "ennreal_powr top r = top"
  unfolding ennreal_powr_def by simp

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma ennreal_powr_of_ennreal [simp]:
  assumes x_nonneg: "0 \<le> x"
  shows "ennreal_powr (ennreal x) r = ennreal (x powr r)"
  using x_nonneg unfolding ennreal_powr_def by simp

subsection \<open>The norm itself\<close>

definition Lp_enorm :: "real \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ennreal" where
  "Lp_enorm p M g =
     (if (\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M
      then ennreal_powr (\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) (1 / p)
      else top)"

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma Lp_enorm_measurable_eq:
  assumes meas: "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M"
  shows "Lp_enorm p M g = ennreal_powr (\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) (1 / p)"
  using meas unfolding Lp_enorm_def by simp

(* Auxiliary for Theorems 3.1-3.2 and 5.3-5.4: finite error requires a defined integral. *)
lemma Lp_enorm_finite_integrable:
  assumes finite: "Lp_enorm p M g < top"
  shows "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
proof -
  have meas: "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M"
    using finite unfolding Lp_enorm_def by (auto split: if_splits)
  have nn: "(\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) < top"
    using finite unfolding Lp_enorm_measurable_eq[OF meas] ennreal_powr_def
    by (auto simp: top.not_eq_extremum split: if_splits)
  show ?thesis using meas nn by (simp add: integrable_iff_bounded)
qed

text \<open>The divergent case really is \<open>\<infinity>\<close>, not a junk finite value.\<close>

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma Lp_enorm_eq_top:
  assumes meas: "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M"
  assumes div: "\<not> integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "Lp_enorm p M g = top"
proof -
  have "\<not> (\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) < top"
    using div meas by (simp add: integrable_iff_bounded)
  then have "(\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) = top"
    using top.not_eq_extremum by blast
  then show ?thesis
    using Lp_enorm_measurable_eq[OF meas] by simp
qed

text \<open>Finiteness is exactly integrability -- the characterisation a \<open>real\<close>-valued norm
  cannot express.\<close>

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma Lp_enorm_less_top_iff:
  assumes meas: "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M"
  shows "Lp_enorm p M g < top \<longleftrightarrow> integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
proof
  assume lt: "Lp_enorm p M g < top"
  show "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  proof (rule ccontr)
    assume "\<not> integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
    from Lp_enorm_eq_top[OF meas this] lt show False by simp
  qed
next
  assume int: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  have "(\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) < top"
    using int by (simp add: integrable_iff_bounded)
  then have "(\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) \<noteq> top" by simp
  then show "Lp_enorm p M g < top"
    using Lp_enorm_measurable_eq[OF meas]
    by (simp add: ennreal_powr_def top.not_eq_extremum)
qed

subsection \<open>Agreement with the real-valued seminorm\<close>

text \<open>
  On integrable arguments -- the only regime in which \<^const>\<open>Lp_seminorm\<close> is used -- the two
  agree.  This is the bridge that lets H\"older and Minkowski, proved above in \<^typ>\<open>real\<close>,
  be reused for \<^const>\<open>Lp_enorm\<close> without being restated.
\<close>

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma Lp_enorm_eq_seminorm:
  assumes int: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "Lp_enorm p M g = ennreal (Lp_seminorm p M g)"
proof -
  have meas: "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M"
    using int by (simp add: integrable_iff_bounded)
  have nonneg: "AE x in M. 0 \<le> \<bar>g x\<bar> powr p" by simp
  have nn_eq: "(\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M) = ennreal (\<integral>x. \<bar>g x\<bar> powr p \<partial>M)"
    using nn_integral_eq_integral[OF int nonneg] .
  have int_nonneg: "0 \<le> (\<integral>x. \<bar>g x\<bar> powr p \<partial>M)"
    by (rule Bochner_Integration.integral_nonneg) simp
  show ?thesis
    unfolding Lp_enorm_measurable_eq[OF meas] nn_eq
              ennreal_powr_of_ennreal[OF int_nonneg] Lp_seminorm_def
    by (rule refl)
qed

subsection \<open>Measurability of \<open>\<bar>h\<bar> powr p\<close>\<close>

text \<open>
  Every \<open>L\<^sup>p\<close> statement in the project is phrased through the integrand \<open>\<bar>h x\<bar> powr p\<close>, so its
  measurability is needed in essentially every measure-theoretic step.  \<open>powr\<close> is continuous
  away from a zero base, which the hypothesis \<open>0 < p\<close> rules out as a discontinuity.
\<close>

(* Auxiliary integration inequality for Theorems 3.2 and 5.4; not separately numbered. *)
lemma abs_powr_measurable:
  fixes p :: real and h :: "'a::euclidean_space \<Rightarrow> real"
  assumes p_pos: "0 < p"
  assumes h: "h \<in> borel_measurable lborel"
  shows "(\<lambda>x. \<bar>h x\<bar> powr p) \<in> borel_measurable lborel"
proof -
  have powr_cont: "continuous_on UNIV (\<lambda>t::real. \<bar>t\<bar> powr p)"
  proof (rule continuous_on_powr')
    show "continuous_on UNIV (\<lambda>t::real. \<bar>t\<bar>)" by (intro continuous_intros)
    show "continuous_on UNIV (\<lambda>t::real. p)" by (intro continuous_intros)
    show "\<forall>t\<in>(UNIV::real set). \<bar>t\<bar> \<ge> 0 \<and> (\<bar>t\<bar> = 0 \<longrightarrow> p > 0)"
      using p_pos by simp
  qed
  have powr_meas: "(\<lambda>t::real. \<bar>t\<bar> powr p) \<in> borel_measurable borel"
    using borel_measurable_continuous_onI[OF powr_cont] .
  show ?thesis using measurable_compose[OF h powr_meas] by simp
qed

subsection \<open>Affine invariance of the Bochner integral over \<open>lborel\<close>\<close>

text \<open>
  HOL-Analysis states affine invariance of Lebesgue measure only as the measure-space identity
  \<open>lborel_affine\<close>.  The three Bochner-integral consequences below -- pure scaling, pure
  translation, and reflection-plus-translation -- are what the mollifier construction of
  \<^file>\<open>Mollifiers.thy\<close> actually uses, to move between \<open>\<integral>\<rho>\<^sub>k(x)\<close>, \<open>\<integral>\<rho>\<^sub>k(c+x)\<close> and
  \<open>\<integral>\<rho>\<^sub>k(t-x)\<close>.  They are dimension-generic and involve nothing but the measure, so they
  belong here rather than beside the construction that consumes them.
\<close>

(* Auxiliary for the mollifier construction of (3.3)-(3.4); not separately numbered. *)
lemma lborel_integral_scaleR_euclidean:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{banach, second_countable_topology}" and c :: real
  assumes c_neq: "c \<noteq> 0" and f: "integrable lborel f"
  shows "(\<integral>x. f x \<partial>lborel) = \<bar>c\<bar> ^ DIM('a) *\<^sub>R (\<integral>x. f (c *\<^sub>R x) \<partial>lborel)"
  using c_neq f f[THEN borel_measurable_integrable]
  by (subst lborel_affine[of c 0, OF c_neq]) (simp add: integral_density integral_distr)

(* Auxiliary for the mollifier construction of (3.3)-(3.4); not separately numbered. *)
lemma lborel_integral_translation:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{banach, second_countable_topology}" and c :: 'a
  assumes f_meas: "f \<in> borel_measurable borel"
  shows "(\<integral>x. f x \<partial>lborel) = (\<integral>x. f (c + x) \<partial>lborel)"
proof -
  have g_borel: "(+) c \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have g_meas: "(+) c \<in> measurable lborel borel"
    using g_borel unfolding measurable_def by (simp add: sets_lborel)
  have "(\<integral>x. f x \<partial>lborel) = (\<integral>x. f x \<partial>(distr lborel borel ((+) c)))"
    by (simp add: lborel_distr_plus)
  also have "\<dots> = (\<integral>x. f (c + x) \<partial>lborel)"
    by (rule integral_distr[OF g_meas f_meas])
  finally show ?thesis .
qed

(* Auxiliary for the mollifier construction of (3.3)-(3.4); not separately numbered. *)
lemma lborel_integral_reflect_translate:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{banach, second_countable_topology}" and t :: 'a
  assumes f_meas: "f \<in> borel_measurable borel"
  shows "(\<integral>x. f x \<partial>lborel) = (\<integral>x. f (t - x) \<partial>lborel)"
proof -
  have neg_one_neq: "(-1::real) \<noteq> 0" by simp
  have distr_eq: "distr lborel borel (\<lambda>x. t - x) = lborel"
    using lborel_affine[of "-1::real" t, OF neg_one_neq] by (simp add: density_1)
  have g_borel: "(\<lambda>x. t - x) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have g_meas: "(\<lambda>x. t - x) \<in> measurable lborel borel"
    using g_borel unfolding measurable_def by (simp add: sets_lborel)
  have "(\<integral>x. f x \<partial>lborel) = (\<integral>x. f x \<partial>(distr lborel borel (\<lambda>x. t - x)))"
    by (simp add: distr_eq)
  also have "\<dots> = (\<integral>x. f (t - x) \<partial>lborel)"
    by (rule integral_distr[OF g_meas f_meas])
  finally show ?thesis .
qed

end
