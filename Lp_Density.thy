section \<open>Density of continuous functions in \<open>L\<^sup>p\<close>\<close>

theory Lp_Density
  imports Lp_Inequalities
begin

text \<open>
  Continuous functions are dense in \<open>L\<^sup>p\<close> (\<open>continuous_dense_Lp\<close>, at the end of this theory).
  This is the one analytic input that the approximation theorems need beyond the sigmoidal
  construction itself, and it is used twice: by the Borel-target Theorem 3.2 and Theorem 5.4
  (\<^file>\<open>Lp_Approximation_General.thy\<close>, \<^file>\<open>Multivariate_Lp_Approximation_General.thy\<close>),
  and inside the paper's own mollifier construction (\<^file>\<open>Mollifiers.thy\<close>), where it supplies
  the compactly supported continuous comparison functions of the approximate-identity proof.

  The route is elementary and dimension-generic, over \<open>'a::euclidean_space\<close> throughout:
  inner regularity of \<open>lborel\<close> on sets of finite measure (which HOL-Analysis's
  \<open>Regularity.thy\<close> does not supply, as it assumes a finite measure space), then a continuous
  tent function separating a compact set from an open superset, then approximation of an
  indicator, of a simple function, and finally of an arbitrary \<open>L\<^sup>p\<close> element.

  No mollifier is used or needed here.  The project's mollifier is the paper's own, built in
  \<^file>\<open>Mollifiers.thy\<close> from equation (3.3); this theory is deliberately independent of it,
  and imports only \<^file>\<open>Lp_Inequalities.thy\<close>.
\<close>

subsection \<open>Inner regularity of Lebesgue measure on \<open>\<real>\<close>\<close>

text \<open>
  HOL-Analysis's \<open>Regularity.thy\<close> proves inner regularity only for FINITE measures
  (its hypothesis is \<open>emeasure M (space M) \<noteq> \<infinity>\<close>), which \<open>lborel\<close> on \<open>\<real>\<close> is not, so it does
  not apply here. We derive the finite-measure-SET case directly from \<open>outer_regular_lborel\<close>,
  applied to the complement of \<open>A\<close> inside a large interval \<open>{-N..N}\<close>: the resulting
  \<open>K = {-N..N} - V\<close> is the intersection of a compact interval with a closed set, hence compact.
\<close>

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma inner_regular_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A_meas: "A \<in> sets borel"
  assumes A_fin: "emeasure lborel A \<noteq> \<infinity>"
  assumes e_pos: "(e::real) > 0"
  obtains K where "compact K" "K \<subseteq> A" "emeasure lborel (A - K) < ennreal e"
proof -
  have A_sets: "A \<in> sets lborel" using A_meas by simp
  have e3_pos: "e / 3 > 0" using e_pos by simp

  \<comment> \<open>Step 1: the part of \<open>A\<close> lying outside \<open>{-N..N}\<close> is small for large \<open>N\<close>.\<close>
  define B where "B = (\<lambda>n::nat. A - cball 0 (real n))"
  have B_sets: "range B \<subseteq> sets lborel"
    unfolding B_def using A_sets by auto
  have B_dec: "decseq B"
    unfolding B_def decseq_def by (auto simp: mem_cball)
  have B_fin: "\<And>i. emeasure lborel (B i) \<noteq> \<infinity>"
  proof -
    fix i :: nat
    have "emeasure lborel (B i) \<le> emeasure lborel A"
      unfolding B_def using A_sets by (intro emeasure_mono) auto
    also have "\<dots> < \<infinity>" using A_fin by (simp add: less_top)
    finally show "emeasure lborel (B i) \<noteq> \<infinity>" by simp
  qed
  have B_int_empty: "(\<Inter>i. B i) = {}"
  proof -
    have "x \<notin> (\<Inter>i. B i)" for x :: 'a
    proof -
      obtain n :: nat where "norm x \<le> real n" using real_arch_simple by blast
      then have "x \<notin> B n" unfolding B_def by (simp add: mem_cball dist_norm)
      then show ?thesis by blast
    qed
    then show ?thesis by blast
  qed
  have B_lim: "(\<lambda>i. emeasure lborel (B i)) \<longlonglongrightarrow> 0"
    using Lim_emeasure_decseq[OF B_sets B_dec B_fin] B_int_empty by simp
  obtain N :: nat where B_small: "emeasure lborel (B N) < ennreal (e / 3)"
  proof -
    have pos: "(0::ennreal) < ennreal (e / 3)" using e3_pos by simp
    have "\<forall>\<^sub>F i in sequentially. emeasure lborel (B i) < ennreal (e / 3)"
      using order_tendstoD(2)[OF B_lim pos] .
    then obtain N where "emeasure lborel (B N) < ennreal (e / 3)"
      by (auto simp: eventually_sequentially)
    then show ?thesis using that by blast
  qed

  \<comment> \<open>Step 2: outer regularity applied to the complement of \<open>A\<close> inside \<open>{-N..N}\<close>.\<close>
  define I where "I = cball (0::'a) (real N)"
  define D where "D = I - A"
  have I_sets: "I \<in> sets borel" unfolding I_def by simp
  have D_sets: "D \<in> sets borel" unfolding D_def using A_meas I_sets by blast
  obtain V where V_open: "open V" and D_sub_V: "D \<subseteq> V"
    and V_small: "emeasure lborel (V - D) < ennreal (e / 3)"
    using outer_regular_lborel[OF D_sets e3_pos] by blast
  define K where "K = I - V"

  have K_compact: "compact K"
  proof -
    have K_eq: "K = I \<inter> (- V)" unfolding K_def by (simp add: Diff_eq)
    have "compact I" unfolding I_def by (rule compact_cball)
    moreover have "closed (- V)" using V_open by (rule closed_Compl)
    ultimately show ?thesis unfolding K_eq by (rule compact_Int_closed)
  qed
  have K_sub_A: "K \<subseteq> A"
  proof
    fix x assume "x \<in> K"
    then have xI: "x \<in> I" and xV: "x \<notin> V" unfolding K_def by auto
    from xV D_sub_V have "x \<notin> D" by blast
    with xI show "x \<in> A" unfolding D_def by blast
  qed
  have A_minus_K: "A - K \<subseteq> B N \<union> (V - D)"
  proof
    fix x assume "x \<in> A - K"
    then have xA: "x \<in> A" and xK: "x \<notin> K" by auto
    show "x \<in> B N \<union> (V - D)"
    proof (cases "x \<in> I")
      case True
      with xK have "x \<in> V" unfolding K_def by auto
      moreover from True xA have "x \<notin> D" unfolding D_def by blast
      ultimately show ?thesis by blast
    next
      case False
      then have "x \<in> B N" unfolding B_def I_def using xA by auto
      then show ?thesis by blast
    qed
  qed

  \<comment> \<open>Step 3: add up the two small pieces.\<close>
  have V_sets: "V - D \<in> sets lborel" using V_open D_sets by simp
  have BN_sets: "B N \<in> sets lborel" using B_sets by blast
  have K_sets: "A - K \<in> sets lborel"
    using A_sets K_compact by (simp add: compact_imp_closed)
  have bound: "emeasure lborel (A - K) < ennreal e"
  proof -
    have "emeasure lborel (A - K) \<le> emeasure lborel (B N \<union> (V - D))"
      using A_minus_K BN_sets V_sets by (intro emeasure_mono) auto
    also have "\<dots> \<le> emeasure lborel (B N) + emeasure lborel (V - D)"
      using BN_sets V_sets by (rule emeasure_subadditive)
    also have "\<dots> \<le> ennreal (e / 3) + ennreal (e / 3)"
      using B_small V_small by (intro add_mono) auto
    also have "\<dots> = ennreal (e / 3 + e / 3)"
      using e3_pos by (simp add: ennreal_plus[symmetric])
    also have "\<dots> < ennreal e"
      using e_pos by (simp add: ennreal_lessI)
    finally show ?thesis .
  qed
  show ?thesis using that[OF K_compact K_sub_A bound] .
qed

subsection \<open>A continuous tent function separating a compact set from an open superset\<close>

text \<open>
  The explicit Urysohn-style interpolant used below to approximate an indicator: for compact
  \<open>K \<subseteq> U\<close> with \<open>U\<close> open, \<open>g x = max 0 (1 - setdist {x} K / d)\<close> is continuous, equals \<open>1\<close> on
  \<open>K\<close>, vanishes off \<open>U\<close>, and -- because \<open>K\<close> is bounded -- vanishes outside a bounded set, which
  is what makes it uniformly continuous later. No abstract Urysohn machinery needed:
  \<open>continuous_on_setdist\<close> plus \<open>compact_subset_open_imp_ball_epsilon_subset\<close> suffice.
\<close>

definition tent :: "'a::euclidean_space set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real" where
  "tent K d x = max 0 (1 - setdist {x} K / d)"

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_nonneg: "0 \<le> tent K d x"
  unfolding tent_def by simp

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_le_one:
  assumes d_pos: "0 < d"
  shows "tent K d x \<le> 1"
proof -
  have "0 \<le> setdist {x} K / d" using d_pos by simp
  then show ?thesis unfolding tent_def by simp
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_continuous:
  assumes d_pos: "0 < d"
  shows "continuous_on UNIV (tent K d)"
  unfolding tent_def
  by (intro continuous_intros continuous_on_setdist) (use d_pos in auto)

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_eq_one:
  assumes xK: "x \<in> K"
  shows "tent K d x = 1"
proof -
  have "setdist {x} K = 0" by (rule setdist_eq_0I[OF singletonI xK])
  then show ?thesis unfolding tent_def by simp
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_near:
  fixes K :: "'a::euclidean_space set"
  assumes K_compact: "compact K" and K_ne: "K \<noteq> {}" and d_pos: "0 < d"
    and ne: "tent K d x \<noteq> 0"
  shows "\<exists>y\<in>K. dist x y < d"
proof -
  have pos: "0 < 1 - setdist {x} K / d"
  proof (rule ccontr)
    assume "\<not> 0 < 1 - setdist {x} K / d"
    then have "tent K d x = 0" unfolding tent_def by simp
    with ne show False by simp
  qed
  then have "setdist {x} K / d < 1" by simp
  then have lt: "setdist {x} K < d"
    using d_pos by (simp add: divide_less_eq)
  obtain y where yK: "y \<in> K" and y_eq: "setdist {x} K = infdist y {x}"
    using setdist_attains_inf[OF K_compact K_ne] by blast
  have dxy_eq: "dist x y = setdist {x} K"
    using y_eq by (simp add: dist_commute)
  show ?thesis
  proof (rule bexI[of _ y])
    show "dist x y < d" using dxy_eq lt by simp
    show "y \<in> K" using yK .
  qed
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_eq_zero_off:
  fixes K U :: "'a::euclidean_space set"
  assumes K_compact: "compact K" and K_ne: "K \<noteq> {}" and d_pos: "0 < d"
    and d_sub: "(\<Union>y\<in>K. ball y d) \<subseteq> U" and xU: "x \<notin> U"
  shows "tent K d x = 0"
proof (rule ccontr)
  assume ne: "tent K d x \<noteq> 0"
  obtain y where yK: "y \<in> K" and dxy: "dist x y < d"
    using tent_near[OF K_compact K_ne d_pos ne] by blast
  have "x \<in> ball y d" using dxy by (simp add: dist_commute)
  then have "x \<in> (\<Union>y\<in>K. ball y d)" using yK by blast
  with d_sub xU show False by blast
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma tent_eq_zero_far:
  fixes K :: "'a::euclidean_space set"
  assumes K_compact: "compact K" and K_ne: "K \<noteq> {}" and d_pos: "0 < d"
    and R0: "\<And>y. y \<in> K \<Longrightarrow> norm y \<le> R0" and far: "R0 + d < norm x"
  shows "tent K d x = 0"
proof (rule ccontr)
  assume ne: "tent K d x \<noteq> 0"
  obtain y where yK: "y \<in> K" and dxy: "dist x y < d"
    using tent_near[OF K_compact K_ne d_pos ne] by blast
  have "norm x = norm (y + (x - y))" by simp
  also have "\<dots> \<le> norm y + norm (x - y)" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> R0 + norm (x - y)" using R0[OF yK] by simp
  also have "\<dots> < R0 + d" using dxy by (simp add: dist_norm)
  finally show False using far by simp
qed


subsection \<open>Approximating an indicator by a continuous function in \<open>L\<^sup>p\<close>\<close>

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma measure_lt_of_emeasure_lt:
  fixes c :: real
  assumes lt: "emeasure M S < ennreal c" and c_pos: "0 < c"
  shows "measure M S < c"
proof -
  have "emeasure M S < top" using lt less_trans ennreal_less_top by blast
  then have fin: "emeasure M S \<noteq> top" by simp
  have "ennreal (measure M S) < ennreal c"
    using lt emeasure_eq_ennreal_measure[OF fin] by simp
  then show ?thesis
    using ennreal_less_iff[OF measure_nonneg] by blast
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma indicator_continuous_approx:
  fixes A :: "'a::euclidean_space set" and p e :: real
  assumes p_pos: "0 < p"
  assumes A_meas: "A \<in> sets borel"
  assumes A_fin: "emeasure lborel A \<noteq> \<infinity>"
  assumes e_pos: "0 < e"
  shows "\<exists>g. continuous_on UNIV g \<and> (\<forall>x. 0 \<le> g x) \<and> (\<forall>x. g x \<le> 1)
       \<and> (\<exists>R. \<forall>x. R < norm x \<longrightarrow> g x = 0)
       \<and> integrable lborel (\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p)
       \<and> (\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) < e"
proof -
  have e3: "0 < e / 3" using e_pos by simp
  obtain U where U_open: "open U" and A_sub_U: "A \<subseteq> U"
    and U_small: "emeasure lborel (U - A) < ennreal (e / 3)"
    using outer_regular_lborel[OF A_meas e3] by blast
  obtain K where K_compact: "compact K" and K_sub_A: "K \<subseteq> A"
    and K_small: "emeasure lborel (A - K) < ennreal (e / 3)"
    using inner_regular_lborel[OF A_meas A_fin e3] by blast
  have U_meas: "U \<in> sets borel" using U_open by simp
  have K_meas: "K \<in> sets borel" using K_compact by (simp add: compact_imp_closed)

  have UK_small: "emeasure lborel (U - K) < ennreal e"
  proof -
    have sub: "U - K \<subseteq> (U - A) \<union> (A - K)" using A_sub_U K_sub_A by blast
    have "emeasure lborel (U - K) \<le> emeasure lborel ((U - A) \<union> (A - K))"
      using sub U_meas A_meas K_meas by (intro emeasure_mono) auto
    also have "\<dots> \<le> emeasure lborel (U - A) + emeasure lborel (A - K)"
      using U_meas A_meas K_meas by (intro emeasure_subadditive) auto
    also have "\<dots> \<le> ennreal (e / 3) + ennreal (e / 3)"
      using U_small K_small by (intro add_mono) auto
    also have "\<dots> = ennreal (e / 3 + e / 3)"
      using e3 by (simp add: ennreal_plus[symmetric])
    also have "\<dots> < ennreal e" using e_pos by (simp add: ennreal_lessI)
    finally show ?thesis .
  qed
  have UK_meas: "U - K \<in> sets lborel" using U_meas K_meas by simp
  have UK_fin: "emeasure lborel (U - K) < \<infinity>"
    using less_trans[OF UK_small ennreal_less_top] by simp
  have ind_int: "integrable lborel (indicat_real (U - K))"
    using UK_meas UK_fin by (rule integrable_real_indicator)
  have ind_integral: "(\<integral>x. indicat_real (U - K) x \<partial>lborel) = measure lborel (U - K)"
    using UK_meas UK_fin by simp

  \<comment> \<open>the pointwise bound, shared by both cases below\<close>
  have key: "\<And>g x. (\<forall>x. 0 \<le> g x) \<Longrightarrow> (\<forall>x. g x \<le> 1) \<Longrightarrow> (\<forall>y\<in>K. g y = 1)
      \<Longrightarrow> (\<forall>y. y \<notin> U \<longrightarrow> g y = 0)
      \<Longrightarrow> \<bar>g x - indicat_real A x\<bar> powr p \<le> indicat_real (U - K) x"
  proof -
    fix g :: "'a \<Rightarrow> real" and x :: 'a
    assume g0: "\<forall>x. 0 \<le> g x" and g1: "\<forall>x. g x \<le> 1"
      and gK: "\<forall>y\<in>K. g y = 1" and gU: "\<forall>y. y \<notin> U \<longrightarrow> g y = 0"
    show "\<bar>g x - indicat_real A x\<bar> powr p \<le> indicat_real (U - K) x"
    proof (cases "x \<in> U - K")
      case True
      have le1: "\<bar>g x - indicat_real A x\<bar> \<le> 1"
      proof -
        have a0: "0 \<le> g x" by (rule g0[rule_format])
        have a1: "g x \<le> 1" by (rule g1[rule_format])
        have b0: "0 \<le> indicat_real A x" by simp
        have b1: "indicat_real A x \<le> 1" by simp
        have h1: "g x - indicat_real A x \<le> 1" using a1 b0 by linarith
        have h2: "indicat_real A x - g x \<le> 1" using a0 b1 by linarith
        show ?thesis using h1 h2 by (simp add: abs_le_iff)
      qed
      have "\<bar>g x - indicat_real A x\<bar> powr p \<le> 1 powr p"
        using le1 p_pos by (intro powr_mono2) auto
      also have "\<dots> = 1" by simp
      also have "\<dots> = indicat_real (U - K) x" using True by simp
      finally show ?thesis .
    next
      case False
      have "g x - indicat_real A x = 0"
      proof (cases "x \<in> K")
        case True
        then have "g x = 1" using gK by blast
        moreover have "indicat_real A x = 1" using True K_sub_A by auto
        ultimately show ?thesis by simp
      next
        case False
        then have "x \<notin> U" using \<open>x \<notin> U - K\<close> by blast
        then have "g x = 0" using gU by blast
        moreover have "indicat_real A x = 0"
        proof -
          have "x \<notin> A" using \<open>x \<notin> U\<close> A_sub_U by blast
          then show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      then show ?thesis using p_pos by simp
    qed
  qed

  \<comment> \<open>from the pointwise bound: integrability and the integral estimate\<close>
  have wrap: "\<And>g. continuous_on UNIV g \<Longrightarrow> (\<forall>x. 0 \<le> g x) \<Longrightarrow> (\<forall>x. g x \<le> 1)
      \<Longrightarrow> (\<forall>y\<in>K. g y = 1) \<Longrightarrow> (\<forall>y. y \<notin> U \<longrightarrow> g y = 0)
      \<Longrightarrow> integrable lborel (\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p)
        \<and> (\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) < e"
  proof -
    fix g :: "'a \<Rightarrow> real"
    assume gc: "continuous_on UNIV g" and g0: "\<forall>x. 0 \<le> g x" and g1: "\<forall>x. g x \<le> 1"
      and gK: "\<forall>y\<in>K. g y = 1" and gU: "\<forall>y. y \<notin> U \<longrightarrow> g y = 0"
    have bnd: "\<And>x. \<bar>g x - indicat_real A x\<bar> powr p \<le> indicat_real (U - K) x"
      using key[OF g0 g1 gK gU] by blast
    have g_meas: "g \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF gc])
    have powr_cont: "continuous_on UNIV (\<lambda>t::real. \<bar>t\<bar> powr p)"
    proof (rule continuous_on_powr')
      show "continuous_on UNIV (\<lambda>t::real. \<bar>t\<bar>)" by (intro continuous_intros)
      show "continuous_on UNIV (\<lambda>t::real. p)" by (intro continuous_intros)
      show "\<forall>t\<in>(UNIV::real set). \<bar>t\<bar> \<ge> 0 \<and> (\<bar>t\<bar> = 0 \<longrightarrow> p > 0)"
        using p_pos by simp
    qed
    have powr_meas: "(\<lambda>t::real. \<bar>t\<bar> powr p) \<in> borel_measurable borel"
      using borel_measurable_continuous_onI[OF powr_cont] .
    have h_meas: "(\<lambda>x. g x - indicat_real A x) \<in> borel_measurable lborel"
      using g_meas A_meas by measurable
    have diff_meas: "(\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p) \<in> borel_measurable lborel"
      using measurable_compose[OF h_meas powr_meas] by simp
    have int: "integrable lborel (\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p)"
    proof (rule Bochner_Integration.integrable_bound[OF ind_int diff_meas])
      show "AE x in lborel. norm (\<bar>g x - indicat_real A x\<bar> powr p)
          \<le> norm (indicat_real (U - K) x)"
        using bnd by (intro AE_I2) simp
    qed
    have "(\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel)
        \<le> (\<integral>x. indicat_real (U - K) x \<partial>lborel)"
      using int ind_int bnd by (intro integral_mono_AE) (auto intro: AE_I2)
    also have "\<dots> = measure lborel (U - K)" by (rule ind_integral)
    also have "\<dots> < e" using measure_lt_of_emeasure_lt[OF UK_small e_pos] .
    finally show "integrable lborel (\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p)
        \<and> (\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) < e"
      using int by blast
  qed

  show ?thesis
  proof (cases "K = {}")
    case True
    have c: "continuous_on UNIV (\<lambda>_::'a. 0::real)" by (intro continuous_intros)
    have w: "integrable lborel (\<lambda>x. \<bar>(\<lambda>_::'a. 0::real) x - indicat_real A x\<bar> powr p)
        \<and> (\<integral>x. \<bar>(\<lambda>_::'a. 0::real) x - indicat_real A x\<bar> powr p \<partial>lborel) < e"
      using True by (intro wrap c) auto
    show ?thesis
      using c w by (intro exI[of _ "\<lambda>_::'a. 0::real"]) auto
  next
    case False
    have K_sub_U: "K \<subseteq> U" using K_sub_A A_sub_U by blast
    obtain d where d_pos: "0 < d" and d_sub: "(\<Union>y\<in>K. ball y d) \<subseteq> U"
      using compact_subset_open_imp_ball_epsilon_subset[OF K_compact U_open K_sub_U] by blast
    obtain R0 where R0: "\<And>y. y \<in> K \<Longrightarrow> norm y \<le> R0"
      using compact_imp_bounded[OF K_compact] by (auto simp: bounded_iff)
    have c: "continuous_on UNIV (tent K d)" by (rule tent_continuous[OF d_pos])
    have t0: "\<forall>x. 0 \<le> tent K d x" using tent_nonneg by blast
    have t1: "\<forall>x. tent K d x \<le> 1" using tent_le_one[OF d_pos] by blast
    have tK: "\<forall>y\<in>K. tent K d y = 1" using tent_eq_one by blast
    have tU: "\<forall>y. y \<notin> U \<longrightarrow> tent K d y = 0"
      using tent_eq_zero_off[OF K_compact False d_pos d_sub] by blast
    have tR: "\<forall>x. R0 + d < norm x \<longrightarrow> tent K d x = 0"
      using tent_eq_zero_far[OF K_compact False d_pos R0] by blast
    have w: "integrable lborel (\<lambda>x. \<bar>tent K d x - indicat_real A x\<bar> powr p)
        \<and> (\<integral>x. \<bar>tent K d x - indicat_real A x\<bar> powr p \<partial>lborel) < e"
      by (rule wrap[OF c t0 t1 tK tU])
    show ?thesis
      using c t0 t1 tR w by (intro exI[of _ "tent K d"]) blast
  qed
qed

subsection \<open>Piece 5c: simple functions are dense in \<open>L\<^sup>p\<close>\<close>

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma simple_dense_Lp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and p e :: real
  assumes p_pos: "0 < p"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_intp: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes e_pos: "0 < e"
  shows "\<exists>s. simple_function lborel s
       \<and> integrable lborel (\<lambda>x. \<bar>s x - f x\<bar> powr p)
       \<and> (\<integral>x. \<bar>s x - f x\<bar> powr p \<partial>lborel) < e"
proof -
  have f_meas': "f \<in> borel_measurable lborel"
    using f_meas measurable_cong_sets[OF sets_lborel refl] by simp

  \<comment> \<open>simple functions converging pointwise, dominated by \<open>2\<bar>f\<bar>\<close> (library, for free)\<close>
  obtain s where s_simple: "\<And>i. simple_function lborel (s i)"
    and s_lim0: "\<And>x. x \<in> space lborel \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
    and s_bnd0: "\<And>i x. x \<in> space lborel \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
    using borel_measurable_implies_sequence_metric[OF f_meas', of 0] by simp metis
  have s_lim: "\<And>x. (\<lambda>i. s i x) \<longlonglongrightarrow> f x" using s_lim0 by simp
  have s_bnd: "\<And>i x. \<bar>s i x\<bar> \<le> 2 * \<bar>f x\<bar>" using s_bnd0 by simp
  have s_meas: "\<And>i. s i \<in> borel_measurable lborel"
    using s_simple by (rule borel_measurable_simple_function)

  \<comment> \<open>the dominating function \<open>3\<^sup>p\<bar>f\<bar>\<^sup>p\<close>\<close>
  define w where "w = (\<lambda>x. 3 powr p * \<bar>f x\<bar> powr p)"
  have w_int: "integrable lborel w"
    unfolding w_def using f_intp by (rule integrable_mult_right)
  have dom: "\<And>i x. \<bar>\<bar>s i x - f x\<bar> powr p\<bar> \<le> w x"
  proof -
    fix i x
    have "\<bar>s i x - f x\<bar> \<le> \<bar>s i x\<bar> + \<bar>f x\<bar>" by simp
    also have "\<dots> \<le> 2 * \<bar>f x\<bar> + \<bar>f x\<bar>" using s_bnd by simp
    also have "\<dots> = 3 * \<bar>f x\<bar>" by simp
    finally have le3: "\<bar>s i x - f x\<bar> \<le> 3 * \<bar>f x\<bar>" .
    have "\<bar>s i x - f x\<bar> powr p \<le> (3 * \<bar>f x\<bar>) powr p"
      using le3 p_pos by (intro powr_mono2) auto
    also have "\<dots> = 3 powr p * \<bar>f x\<bar> powr p" by (simp add: powr_mult)
    finally show "\<bar>\<bar>s i x - f x\<bar> powr p\<bar> \<le> w x" unfolding w_def by simp
  qed

  \<comment> \<open>pointwise convergence of the integrands to 0\<close>
  have lim0: "\<And>x. (\<lambda>i. \<bar>s i x - f x\<bar> powr p) \<longlonglongrightarrow> 0"
  proof -
    fix x
    have "(\<lambda>i. s i x - f x) \<longlonglongrightarrow> f x - f x"
      using s_lim by (intro tendsto_diff tendsto_const)
    then have z: "(\<lambda>i. \<bar>s i x - f x\<bar>) \<longlonglongrightarrow> 0"
      by (simp add: tendsto_rabs_zero_iff)
    have "(\<lambda>i. \<bar>s i x - f x\<bar> powr p) \<longlonglongrightarrow> 0 powr p"
      using z p_pos by (intro tendsto_powr2 tendsto_const) auto
    then show "(\<lambda>i. \<bar>s i x - f x\<bar> powr p) \<longlonglongrightarrow> 0" using p_pos by simp
  qed

  \<comment> \<open>naming the sequence keeps the dominated-convergence unification FIRST-ORDER;
      with the lambda written out inline, \<open>rule\<close> cannot solve for the sequence variable\<close>
  define g where "g = (\<lambda>i x. \<bar>s i x - f x\<bar> powr p)"

  have g_meas: "\<And>i. g i \<in> borel_measurable lborel"
  proof -
    fix i
    have "(\<lambda>x. s i x - f x) \<in> borel_measurable lborel"
      using s_meas f_meas' by measurable
    then have "(\<lambda>x. \<bar>s i x - f x\<bar> powr p) \<in> borel_measurable lborel"
      by (rule abs_powr_measurable[OF p_pos, where h = "\<lambda>x. s i x - f x"])
    then show "g i \<in> borel_measurable lborel" unfolding g_def by simp
  qed

  have g_dom: "\<And>i x. norm (g i x) \<le> w x"
    unfolding g_def using dom by simp

  have int_i: "\<And>i. integrable lborel (g i)"
  proof -
    fix i
    show "integrable lborel (g i)"
    proof (rule Bochner_Integration.integrable_bound[OF w_int g_meas])
      show "AE x in lborel. norm (g i x) \<le> norm (w x)"
        using g_dom by (intro AE_I2) (simp add: w_def)
    qed
  qed

  \<comment> \<open>BOTH the sequence and the limit must be NAMED constants here. With the limit written
      inline as \<open>integral\<^sup>L lborel (\<lambda>x. 0)\<close>, \<open>rule\<close>/\<open>intro\<close> fail to apply at all; with \<open>f0\<close> a
      named constant the identical proof goes through. Likewise the \<open>\<And>i\<close> premises must be
      discharged as \<open>show "\<And>i. \<dots>"\<close> inside \<open>proof (rule \<dots>)\<close> -- supplying them through \<open>OF\<close>
      fails with "OF: no unifiers", because a discharged \<open>\<And>i\<close> fact is exported with a
      SCHEMATIC \<open>?i\<close> which \<open>OF\<close> will not bridge to a meta-quantified premise.\<close>
  define f0 :: "'a \<Rightarrow> real" where "f0 = (\<lambda>x. 0)"

  have conv: "(\<lambda>i. integral\<^sup>L lborel (g i)) \<longlonglongrightarrow> integral\<^sup>L lborel f0"
  proof (rule integral_dominated_convergence)
    show "f0 \<in> borel_measurable lborel" unfolding f0_def by simp
    show "\<And>i. g i \<in> borel_measurable lborel" by (rule g_meas)
    show "integrable lborel w" by (rule w_int)
    show "AE x in lborel. (\<lambda>i. g i x) \<longlonglongrightarrow> f0 x"
      using lim0 by (intro AE_I2) (simp add: g_def f0_def)
    show "\<And>i. AE x in lborel. norm (g i x) \<le> w x"
      using g_dom by (intro AE_I2) simp
  qed
  have f0_int: "integral\<^sup>L lborel f0 = 0" unfolding f0_def by simp
  have conv0: "(\<lambda>i. integral\<^sup>L lborel (g i)) \<longlonglongrightarrow> 0"
    using conv[unfolded f0_int] .

  \<comment> \<open>state this with \<open>norm\<close>, exactly as @{thm LIMSEQ_D} produces it: \<open>blast\<close> does no
      rewriting, so an \<open>\<bar>\<dots>\<bar>\<close> version sends it into an unbounded search\<close>
  obtain n0 where n0: "\<And>n. n0 \<le> n \<Longrightarrow> norm (integral\<^sup>L lborel (g n) - 0) < e"
    using LIMSEQ_D[OF conv0 e_pos] by blast
  have lt: "integral\<^sup>L lborel (g n0) < e"
  proof -
    have "norm (integral\<^sup>L lborel (g n0) - 0) < e" using n0[of n0] by simp
    then have "\<bar>integral\<^sup>L lborel (g n0)\<bar> < e" by simp
    then show ?thesis by linarith
  qed

  show ?thesis
  proof (intro exI[of _ "s n0"] conjI)
    show "simple_function lborel (s n0)" by (rule s_simple)
    show "integrable lborel (\<lambda>x. \<bar>s n0 x - f x\<bar> powr p)"
      using int_i[of n0] unfolding g_def by simp
    show "(\<integral>x. \<bar>s n0 x - f x\<bar> powr p \<partial>lborel) < e"
      using lt unfolding g_def by simp
  qed
qed

subsection \<open>Piece 5d: continuous functions are dense in \<open>L\<^sup>p\<close>\<close>

text \<open>Finite-sum Minkowski: iterate @{thm Lp_Minkowski_inequality} over a finite index set.
  Integrability has to be carried along in the same induction, since each Minkowski step needs
  the integrability of the partial sum it is applied to. Stated with explicit \<open>\<forall>\<close>/\<open>\<longrightarrow>\<close> rather
  than \<open>arbitrary:\<close>, per the induction gotcha recorded in the project notes.\<close>

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma Lp_seminorm_sum:
  fixes h :: "'i \<Rightarrow> 'a \<Rightarrow> real" and p :: real and M :: "'a measure"
  assumes p_ge1: "1 \<le> p"
  assumes finI: "finite I"
  assumes meas: "\<And>i. i \<in> I \<Longrightarrow> h i \<in> borel_measurable M"
  assumes intp: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. \<bar>h i x\<bar> powr p)"
  shows "integrable M (\<lambda>x. \<bar>\<Sum>i\<in>I. h i x\<bar> powr p)
       \<and> Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>I. h i x) \<le> (\<Sum>i\<in>I. Lp_seminorm p M (h i))"
proof -
  have p_ne: "p \<noteq> 0" using p_ge1 by simp
  have main: "finite J \<Longrightarrow> (\<forall>i\<in>J. h i \<in> borel_measurable M)
      \<Longrightarrow> (\<forall>i\<in>J. integrable M (\<lambda>x. \<bar>h i x\<bar> powr p))
      \<Longrightarrow> integrable M (\<lambda>x. \<bar>\<Sum>i\<in>J. h i x\<bar> powr p)
        \<and> Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>J. h i x) \<le> (\<Sum>i\<in>J. Lp_seminorm p M (h i))"
    for J :: "'i set"
  proof (induction J rule: finite_induct)
    case empty
    have e1: "integrable M (\<lambda>x. \<bar>\<Sum>i\<in>{}. h i x\<bar> powr p)"
      using p_ne by simp
    have e2: "Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>{}. h i x) = 0"
      unfolding Lp_seminorm_def using p_ne by simp
    show ?case using e1 e2 by simp
  next
    case (insert a F)
    have aF: "a \<notin> F" and finF: "finite F" using insert.hyps by auto
    have ha_meas: "h a \<in> borel_measurable M" using insert.prems(1) by simp
    have ha_intp: "integrable M (\<lambda>x. \<bar>h a x\<bar> powr p)" using insert.prems(2) by simp
    have IH: "integrable M (\<lambda>x. \<bar>\<Sum>i\<in>F. h i x\<bar> powr p)
        \<and> Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>F. h i x) \<le> (\<Sum>i\<in>F. Lp_seminorm p M (h i))"
      using insert.IH insert.prems by simp
    have H_intp: "integrable M (\<lambda>x. \<bar>\<Sum>i\<in>F. h i x\<bar> powr p)" using IH by blast
    have H_bound: "Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>F. h i x) \<le> (\<Sum>i\<in>F. Lp_seminorm p M (h i))"
      using IH by blast
    have H_meas: "(\<lambda>x. \<Sum>i\<in>F. h i x) \<in> borel_measurable M"
      using insert.prems(1) by (intro borel_measurable_sum) simp
    have split: "(\<lambda>x. \<Sum>i\<in>insert a F. h i x) = (\<lambda>x. h a x + (\<Sum>i\<in>F. h i x))"
      using finF aF by simp
    \<comment> \<open>NB \<open>unfolding split\<close> does NOT fire here: the goal contains the SUM under a binder
        (\<open>\<Sum>i\<in>insert a F. h i x\<close> with \<open>x\<close> bound), not the lambda \<open>(\<lambda>x. \<Sum>\<dots>)\<close> that \<open>split\<close>
        rewrites. Rewrite the whole integrand as a function equation instead.\<close>
    have int_ins: "integrable M (\<lambda>x. \<bar>\<Sum>i\<in>insert a F. h i x\<bar> powr p)"
    proof -
      have base: "integrable M (\<lambda>x. \<bar>h a x + (\<Sum>i\<in>F. h i x)\<bar> powr p)"
        by (rule Lp_Minkowski_integrable[OF p_ge1 ha_meas H_meas ha_intp H_intp])
      have eq: "(\<lambda>x. \<bar>\<Sum>i\<in>insert a F. h i x\<bar> powr p)
              = (\<lambda>x. \<bar>h a x + (\<Sum>i\<in>F. h i x)\<bar> powr p)"
        using finF aF by simp
      show ?thesis using base eq by simp
    qed
    have "Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>insert a F. h i x)
        = Lp_seminorm p M (\<lambda>x. h a x + (\<Sum>i\<in>F. h i x))"
      unfolding split by (rule refl)
    also have "\<dots> \<le> Lp_seminorm p M (h a) + Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>F. h i x)"
      by (rule Lp_Minkowski_inequality[OF p_ge1 ha_meas H_meas ha_intp H_intp])
    also have "\<dots> \<le> Lp_seminorm p M (h a) + (\<Sum>i\<in>F. Lp_seminorm p M (h i))"
      using H_bound by linarith
    also have "\<dots> = (\<Sum>i\<in>insert a F. Lp_seminorm p M (h i))"
      using finF aF by simp
    finally have bound_ins: "Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>insert a F. h i x)
        \<le> (\<Sum>i\<in>insert a F. Lp_seminorm p M (h i))" .
    show ?case using int_ins bound_ins by blast
  qed
  show ?thesis using main[OF finI] meas intp by blast
qed

text \<open>A nonzero level set of a simple \<open>L\<^sup>p\<close> function has finite measure -- this is exactly the
  hypothesis @{thm indicator_continuous_approx} needs in order to approximate its indicator.\<close>

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma simple_Lp_level_finite:
  fixes s :: "'a::euclidean_space \<Rightarrow> real" and p y :: real
  assumes p_pos: "0 < p"
  assumes s_simple: "simple_function lborel s"
  assumes s_intp: "integrable lborel (\<lambda>x. \<bar>s x\<bar> powr p)"
  assumes y_ne: "y \<noteq> 0"
  shows "emeasure lborel (s -` {y} \<inter> space lborel) \<noteq> \<infinity>"
proof -
  define A where "A = s -` {y} \<inter> space lborel"
  have A_meas: "A \<in> sets lborel"
    unfolding A_def by (rule simple_functionD(2)[OF s_simple])
  have fin: "(\<integral>\<^sup>+x. ennreal (\<bar>s x\<bar> powr p) \<partial>lborel) < \<infinity>"
    using s_intp by (simp add: integrable_iff_bounded)
  have mono: "\<And>x. ennreal (\<bar>y\<bar> powr p) * indicator A x \<le> ennreal (\<bar>s x\<bar> powr p)"
  proof -
    fix x
    show "ennreal (\<bar>y\<bar> powr p) * indicator A x \<le> ennreal (\<bar>s x\<bar> powr p)"
    proof (cases "x \<in> A")
      case True
      then have "s x = y" unfolding A_def by simp
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  have "ennreal (\<bar>y\<bar> powr p) * emeasure lborel A
      = (\<integral>\<^sup>+x. ennreal (\<bar>y\<bar> powr p) * indicator A x \<partial>lborel)"
    using A_meas by (simp add: nn_integral_cmult_indicator)
  also have "\<dots> \<le> (\<integral>\<^sup>+x. ennreal (\<bar>s x\<bar> powr p) \<partial>lborel)"
    by (intro nn_integral_mono) (rule mono)
  also have "\<dots> < \<infinity>" by (rule fin)
  finally have lt: "ennreal (\<bar>y\<bar> powr p) * emeasure lborel A < \<infinity>" .
  have cpos: "ennreal (\<bar>y\<bar> powr p) \<noteq> 0"
    using y_ne p_pos by simp
  \<comment> \<open>\<open>define\<close> does NOT fold \<open>A\<close> into the goal here, so prove the \<open>A\<close>-form separately and
      unfold \<open>A_def\<close> at the very end rather than aiming \<open>show ?thesis\<close> at it directly\<close>
  have main: "emeasure lborel A \<noteq> \<infinity>"
  proof (rule ccontr)
    assume "\<not> emeasure lborel A \<noteq> \<infinity>"
    then have inf: "emeasure lborel A = \<infinity>" by simp
    have "ennreal (\<bar>y\<bar> powr p) * emeasure lborel A = \<infinity>"
      unfolding inf using cpos by simp
    with lt show False by simp
  qed
  show ?thesis using main unfolding A_def .
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma Lp_seminorm_scale:
  fixes c p :: real and M :: "'a measure" and h :: "'a \<Rightarrow> real"
  assumes p_pos: "0 < p"
  shows "Lp_seminorm p M (\<lambda>x. c * h x) = \<bar>c\<bar> * Lp_seminorm p M h"
proof -
  have p_ne: "p \<noteq> 0" using p_pos by simp
  have pt: "\<And>x. \<bar>c * h x\<bar> powr p = \<bar>c\<bar> powr p * \<bar>h x\<bar> powr p"
    by (simp add: abs_mult powr_mult)
  have int_nonneg: "0 \<le> (\<integral>x. \<bar>h x\<bar> powr p \<partial>M)"
    by (rule integral_nonneg_AE) simp
  have eq_int: "(\<integral>x. \<bar>c * h x\<bar> powr p \<partial>M) = \<bar>c\<bar> powr p * (\<integral>x. \<bar>h x\<bar> powr p \<partial>M)"
    using pt by simp
  have "Lp_seminorm p M (\<lambda>x. c * h x)
      = (\<bar>c\<bar> powr p * (\<integral>x. \<bar>h x\<bar> powr p \<partial>M)) powr (1 / p)"
    unfolding Lp_seminorm_def using eq_int by simp
  also have "\<dots> = (\<bar>c\<bar> powr p) powr (1 / p) * ((\<integral>x. \<bar>h x\<bar> powr p \<partial>M) powr (1 / p))"
    using int_nonneg by (simp add: powr_mult)
  also have "\<dots> = \<bar>c\<bar> * ((\<integral>x. \<bar>h x\<bar> powr p \<partial>M) powr (1 / p))"
    using p_ne by (simp add: powr_powr)
  also have "\<dots> = \<bar>c\<bar> * Lp_seminorm p M h"
    unfolding Lp_seminorm_def by (rule refl)
  finally show ?thesis .
qed

text \<open>One scaled level-set term. Note \<open>y = 0\<close> needs no special case: the bound
  \<open>\<bar>y\<bar> * (tau / (1+\<bar>y\<bar>)) < tau\<close> holds for every \<open>y\<close>.\<close>

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma indicator_scaled_Lp_approx:
  fixes A :: "'a::euclidean_space set" and p y tau :: real
  assumes p_pos: "0 < p"
  assumes A_meas: "A \<in> sets borel"
  assumes A_fin: "emeasure lborel A \<noteq> \<infinity>"
  assumes tau_pos: "0 < tau"
  shows "\<exists>gy. continuous_on UNIV gy
       \<and> integrable lborel (\<lambda>x. \<bar>y * (gy x - indicat_real A x)\<bar> powr p)
       \<and> Lp_seminorm p lborel (\<lambda>x. y * (gy x - indicat_real A x)) < tau"
proof -
  define c where "c = tau / (1 + \<bar>y\<bar>)"
  have c_pos: "0 < c" unfolding c_def using tau_pos by simp
  have cp_pos: "0 < c powr p" using c_pos by simp
  obtain g where g_cont: "continuous_on UNIV g"
    and g_int: "integrable lborel (\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p)"
    and g_lt: "(\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) < c powr p"
    using indicator_continuous_approx[OF p_pos A_meas A_fin cp_pos] by blast

  have sem_lt: "Lp_seminorm p lborel (\<lambda>x. g x - indicat_real A x) < c"
  proof -
    have "Lp_seminorm p lborel (\<lambda>x. g x - indicat_real A x)
        = (\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) powr (1 / p)"
      unfolding Lp_seminorm_def by (rule refl)
    also have "\<dots> < (c powr p) powr (1 / p)"
    proof (rule powr_less_mono2)
      show "0 < 1 / p" using p_pos by simp
      show "0 \<le> (\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel)"
        by (rule integral_nonneg_AE) simp
      show "(\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) < c powr p" by (rule g_lt)
    qed
    also have "\<dots> = c" using p_pos c_pos by (simp add: powr_powr)
    finally show ?thesis .
  qed

  have scaled_int: "integrable lborel (\<lambda>x. \<bar>y * (g x - indicat_real A x)\<bar> powr p)"
  proof -
    have "\<And>x. \<bar>y * (g x - indicat_real A x)\<bar> powr p
        = \<bar>y\<bar> powr p * \<bar>g x - indicat_real A x\<bar> powr p"
      by (simp add: abs_mult powr_mult)
    then show ?thesis using g_int by simp
  qed

  have scaled_lt: "Lp_seminorm p lborel (\<lambda>x. y * (g x - indicat_real A x)) < tau"
  proof -
    have "Lp_seminorm p lborel (\<lambda>x. y * (g x - indicat_real A x))
        = \<bar>y\<bar> * Lp_seminorm p lborel (\<lambda>x. g x - indicat_real A x)"
      by (rule Lp_seminorm_scale[OF p_pos])
    also have "\<dots> \<le> \<bar>y\<bar> * c"
    proof (rule mult_left_mono)
      show "Lp_seminorm p lborel (\<lambda>x. g x - indicat_real A x) \<le> c"
        using sem_lt by linarith
      show "0 \<le> \<bar>y\<bar>" by simp
    qed
    also have "\<dots> < tau"
    proof -
      have "\<bar>y\<bar> * c = tau * (\<bar>y\<bar> / (1 + \<bar>y\<bar>))"
        unfolding c_def by simp
      also have "\<dots> < tau * 1"
      proof (rule mult_strict_left_mono)
        show "\<bar>y\<bar> / (1 + \<bar>y\<bar>) < 1" by simp
        show "0 < tau" by (rule tau_pos)
      qed
      also have "\<dots> = tau" by simp
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed

  show ?thesis using g_cont scaled_int scaled_lt by blast
qed

(* Auxiliary for the density proof of Theorems 3.2 and 5.4; not separately numbered in the paper. *)
lemma simple_continuous_approx:
  fixes s :: "'a::euclidean_space \<Rightarrow> real" and p e :: real
  assumes p_ge1: "1 \<le> p"
  assumes s_simple: "simple_function lborel s"
  assumes s_intp: "integrable lborel (\<lambda>x. \<bar>s x\<bar> powr p)"
  assumes e_pos: "0 < e"
  shows "\<exists>g. continuous_on UNIV g
       \<and> integrable lborel (\<lambda>x. \<bar>g x - s x\<bar> powr p)
       \<and> Lp_seminorm p lborel (\<lambda>x. g x - s x) < e"
proof -
  have p_pos: "0 < p" using p_ge1 by simp
  define R where "R = s ` space lborel"
  have finR: "finite R" unfolding R_def by (rule simple_functionD(1)[OF s_simple])
  define Y where "Y = R - {0}"
  have finY: "finite Y" unfolding Y_def using finR by simp
  define A where "A = (\<lambda>y. s -` {y} \<inter> space lborel)"
  have A_meas: "\<And>y. A y \<in> sets borel"
    unfolding A_def using simple_functionD(2)[OF s_simple] by simp
  have A_fin: "\<And>y. y \<in> Y \<Longrightarrow> emeasure lborel (A y) \<noteq> \<infinity>"
    unfolding A_def Y_def
    using simple_Lp_level_finite[OF p_pos s_simple s_intp] by simp

  \<comment> \<open>indicator representation, with the \<open>y = 0\<close> term dropped\<close>
  have s_rep: "\<And>x. s x = (\<Sum>y\<in>Y. y * indicat_real (A y) x)"
  proof -
    fix x
    have "s x = (\<Sum>y \<in> s ` space lborel. indicat_real (s -` {y} \<inter> space lborel) x *\<^sub>R y)"
      by (rule simple_function_indicator_representation_banach[OF s_simple]) simp
    also have "\<dots> = (\<Sum>y\<in>R. y * indicat_real (A y) x)"
      unfolding R_def A_def by (simp add: mult.commute)
    also have "\<dots> = (\<Sum>y\<in>Y. y * indicat_real (A y) x)"
      unfolding Y_def using finR by (intro sum.mono_neutral_right) auto
    finally show "s x = (\<Sum>y\<in>Y. y * indicat_real (A y) x)" .
  qed

  show ?thesis
  proof (cases "Y = {}")
    case True
    have s_zero: "\<And>x. s x = 0" using s_rep True by simp
    have c0: "continuous_on UNIV (\<lambda>_::'a. 0::real)" by (intro continuous_intros)
    have i0: "integrable lborel (\<lambda>x. \<bar>(0::real) - s x\<bar> powr p)"
      using s_zero p_pos by simp
    have l0: "Lp_seminorm p lborel (\<lambda>x. (0::real) - s x) < e"
      unfolding Lp_seminorm_def using s_zero p_pos e_pos by simp
    show ?thesis using c0 i0 l0 by (intro exI[of _ "\<lambda>_::'a. 0::real"]) auto
  next
    case False
    define n where "n = card Y"
    have n_pos: "0 < n" unfolding n_def using finY False by (simp add: card_gt_0_iff)
    define tau where "tau = e / (2 * real n)"
    have tau_pos: "0 < tau" unfolding tau_def using e_pos n_pos by simp

    have ex: "\<forall>y\<in>Y. \<exists>gy. continuous_on UNIV gy
        \<and> integrable lborel (\<lambda>x. \<bar>y * (gy x - indicat_real (A y) x)\<bar> powr p)
        \<and> Lp_seminorm p lborel (\<lambda>x. y * (gy x - indicat_real (A y) x)) < tau"
    proof
      fix y assume yY: "y \<in> Y"
      show "\<exists>gy. continuous_on UNIV gy
          \<and> integrable lborel (\<lambda>x. \<bar>y * (gy x - indicat_real (A y) x)\<bar> powr p)
          \<and> Lp_seminorm p lborel (\<lambda>x. y * (gy x - indicat_real (A y) x)) < tau"
        by (rule indicator_scaled_Lp_approx[OF p_pos A_meas[of y] A_fin[OF yY] tau_pos])
    qed
    obtain G where G: "\<forall>y\<in>Y. continuous_on UNIV (G y)
        \<and> integrable lborel (\<lambda>x. \<bar>y * (G y x - indicat_real (A y) x)\<bar> powr p)
        \<and> Lp_seminorm p lborel (\<lambda>x. y * (G y x - indicat_real (A y) x)) < tau"
      using bchoice[OF ex] by blast

    define h where "h = (\<lambda>y x. y * (G y x - indicat_real (A y) x))"
    define g where "g = (\<lambda>x. \<Sum>y\<in>Y. y * G y x)"

    have Gcont: "\<And>y. y \<in> Y \<Longrightarrow> continuous_on UNIV (G y)" using G by blast
    have h_intp: "\<And>y. y \<in> Y \<Longrightarrow> integrable lborel (\<lambda>x. \<bar>h y x\<bar> powr p)"
      unfolding h_def using G by blast
    have h_lt: "\<And>y. y \<in> Y \<Longrightarrow> Lp_seminorm p lborel (h y) < tau"
      unfolding h_def using G by blast
    have h_meas: "\<And>y. y \<in> Y \<Longrightarrow> h y \<in> borel_measurable lborel"
    proof -
      fix y assume yY: "y \<in> Y"
      have "G y \<in> borel_measurable lborel"
        using borel_measurable_continuous_onI[OF Gcont[OF yY]] by simp
      moreover have "indicat_real (A y) \<in> borel_measurable lborel"
        using A_meas[of y] by simp
      ultimately show "h y \<in> borel_measurable lborel"
        unfolding h_def by measurable
    qed

    have g_cont: "continuous_on UNIV g"
      unfolding g_def
    proof (rule continuous_on_sum)
      fix y assume yY: "y \<in> Y"
      show "continuous_on UNIV (\<lambda>x. y * G y x)"
        using Gcont[OF yY] by (intro continuous_intros)
    qed

    have diff_eq: "(\<lambda>x. g x - s x) = (\<lambda>x. \<Sum>y\<in>Y. h y x)"
    proof
      fix x
      have "g x - s x = (\<Sum>y\<in>Y. y * G y x) - (\<Sum>y\<in>Y. y * indicat_real (A y) x)"
        unfolding g_def using s_rep by simp
      also have "\<dots> = (\<Sum>y\<in>Y. y * G y x - y * indicat_real (A y) x)"
        by (rule sum_subtractf[symmetric])
      also have "\<dots> = (\<Sum>y\<in>Y. h y x)"
        unfolding h_def by (simp add: algebra_simps)
      finally show "g x - s x = (\<Sum>y\<in>Y. h y x)" .
    qed

    have sum_res: "integrable lborel (\<lambda>x. \<bar>\<Sum>y\<in>Y. h y x\<bar> powr p)
        \<and> Lp_seminorm p lborel (\<lambda>x. \<Sum>y\<in>Y. h y x) \<le> (\<Sum>y\<in>Y. Lp_seminorm p lborel (h y))"
    proof (rule Lp_seminorm_sum)
      show "1 \<le> p" by (rule p_ge1)
      show "finite Y" by (rule finY)
      show "\<And>i. i \<in> Y \<Longrightarrow> h i \<in> borel_measurable lborel" by (rule h_meas)
      show "\<And>i. i \<in> Y \<Longrightarrow> integrable lborel (\<lambda>x. \<bar>h i x\<bar> powr p)" by (rule h_intp)
    qed

    have bound: "Lp_seminorm p lborel (\<lambda>x. g x - s x) < e"
    proof -
      have "Lp_seminorm p lborel (\<lambda>x. g x - s x)
          = Lp_seminorm p lborel (\<lambda>x. \<Sum>y\<in>Y. h y x)"
        unfolding diff_eq by (rule refl)
      also have "\<dots> \<le> (\<Sum>y\<in>Y. Lp_seminorm p lborel (h y))" using sum_res by blast
      also have "\<dots> < (\<Sum>y\<in>Y. tau)"
        using finY False h_lt by (intro sum_strict_mono) auto
      also have "\<dots> = real n * tau" unfolding n_def by simp
      also have "\<dots> = e / 2" unfolding tau_def using n_pos by simp
      also have "\<dots> < e" using e_pos by simp
      finally show ?thesis .
    qed

    \<comment> \<open>as in @{thm Lp_seminorm_sum}'s insert step, \<open>unfolding diff_eq\<close> does NOT fire on this
        goal: the integrand mentions \<open>g x - s x\<close> under a binder, not the lambda itself. (It DOES
        fire in \<open>bound\<close> above, where the lambda is an argument of \<open>Lp_seminorm\<close>.) Rewrite the
        whole integrand as a function equation instead -- otherwise \<open>blast\<close> searches forever.\<close>
    have diff_pt: "\<And>x. g x - s x = (\<Sum>y\<in>Y. h y x)"
      using fun_cong[OF diff_eq] by simp
    have g_int: "integrable lborel (\<lambda>x. \<bar>g x - s x\<bar> powr p)"
    proof -
      have eq: "(\<lambda>x. \<bar>g x - s x\<bar> powr p) = (\<lambda>x. \<bar>\<Sum>y\<in>Y. h y x\<bar> powr p)"
        using diff_pt by simp
      show ?thesis using sum_res eq by simp
    qed

    show ?thesis
    proof (intro exI[of _ g] conjI)
      show "continuous_on UNIV g" by (rule g_cont)
      show "integrable lborel (\<lambda>x. \<bar>g x - s x\<bar> powr p)" by (rule g_int)
      show "Lp_seminorm p lborel (\<lambda>x. g x - s x) < e" by (rule bound)
    qed
  qed
qed

(* Auxiliary density result for Theorems 3.2 and 5.4; alternative to the paper mollifier proof. *)
theorem continuous_dense_Lp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and p e :: real
  assumes p_ge1: "1 \<le> p"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_intp: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes e_pos: "0 < e"
  shows "\<exists>g. continuous_on UNIV g
       \<and> integrable lborel (\<lambda>x. \<bar>g x - f x\<bar> powr p)
       \<and> Lp_seminorm p lborel (\<lambda>x. g x - f x) < e"
proof -
  have p_pos: "0 < p" using p_ge1 by simp
  have e2_pos: "0 < e / 2" using e_pos by simp
  have tol_pos: "0 < (e / 2) powr p" using e2_pos by simp

  obtain s where s_simple: "simple_function lborel s"
    and s_int: "integrable lborel (\<lambda>x. \<bar>s x - f x\<bar> powr p)"
    and s_lt: "(\<integral>x. \<bar>s x - f x\<bar> powr p \<partial>lborel) < (e / 2) powr p"
    using simple_dense_Lp[OF p_pos f_meas f_intp tol_pos] by blast
  have s_meas: "s \<in> borel_measurable lborel"
    using s_simple by (rule borel_measurable_simple_function)
  have f_meas': "f \<in> borel_measurable lborel"
    using f_meas measurable_cong_sets[OF sets_lborel refl] by simp
  have sf_meas: "(\<lambda>x. s x - f x) \<in> borel_measurable lborel"
    using s_meas f_meas' by measurable

  have sf_sem: "Lp_seminorm p lborel (\<lambda>x. s x - f x) < e / 2"
  proof -
    have "Lp_seminorm p lborel (\<lambda>x. s x - f x)
        = (\<integral>x. \<bar>s x - f x\<bar> powr p \<partial>lborel) powr (1 / p)"
      unfolding Lp_seminorm_def by (rule refl)
    also have "\<dots> < ((e / 2) powr p) powr (1 / p)"
    proof (rule powr_less_mono2)
      show "0 < 1 / p" using p_pos by simp
      show "0 \<le> (\<integral>x. \<bar>s x - f x\<bar> powr p \<partial>lborel)"
        by (rule integral_nonneg_AE) simp
      show "(\<integral>x. \<bar>s x - f x\<bar> powr p \<partial>lborel) < (e / 2) powr p" by (rule s_lt)
    qed
    also have "\<dots> = e / 2" using p_pos e2_pos by (simp add: powr_powr)
    finally show ?thesis .
  qed

  \<comment> \<open>\<open>s\<close> is itself in \<open>L\<^sup>p\<close>, via \<open>s = (s - f) + f\<close> -- needed to feed
      @{thm simple_continuous_approx}\<close>
  have s_intp: "integrable lborel (\<lambda>x. \<bar>s x\<bar> powr p)"
  proof -
    have base: "integrable lborel (\<lambda>x. \<bar>(s x - f x) + f x\<bar> powr p)"
      by (rule Lp_Minkowski_integrable[OF p_ge1 sf_meas f_meas' s_int f_intp])
    have eq: "(\<lambda>x. \<bar>(s x - f x) + f x\<bar> powr p) = (\<lambda>x. \<bar>s x\<bar> powr p)" by simp
    show ?thesis using base eq by simp
  qed

  obtain g where g_cont: "continuous_on UNIV g"
    and g_int: "integrable lborel (\<lambda>x. \<bar>g x - s x\<bar> powr p)"
    and g_lt: "Lp_seminorm p lborel (\<lambda>x. g x - s x) < e / 2"
    using simple_continuous_approx[OF p_ge1 s_simple s_intp e2_pos] by blast
  have g_meas: "g \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF g_cont] by simp
  have gs_meas: "(\<lambda>x. g x - s x) \<in> borel_measurable lborel"
    using g_meas s_meas by measurable

  have gf_eq: "(\<lambda>x. (g x - s x) + (s x - f x)) = (\<lambda>x. g x - f x)" by simp

  have gf_int: "integrable lborel (\<lambda>x. \<bar>g x - f x\<bar> powr p)"
  proof -
    have base: "integrable lborel (\<lambda>x. \<bar>(g x - s x) + (s x - f x)\<bar> powr p)"
      by (rule Lp_Minkowski_integrable[OF p_ge1 gs_meas sf_meas g_int s_int])
    have eq: "(\<lambda>x. \<bar>(g x - s x) + (s x - f x)\<bar> powr p) = (\<lambda>x. \<bar>g x - f x\<bar> powr p)"
      by simp
    show ?thesis using base eq by simp
  qed

  have gf_sem: "Lp_seminorm p lborel (\<lambda>x. g x - f x) < e"
  proof -
    have "Lp_seminorm p lborel (\<lambda>x. g x - f x)
        = Lp_seminorm p lborel (\<lambda>x. (g x - s x) + (s x - f x))"
      unfolding gf_eq by (rule refl)
    also have "\<dots> \<le> Lp_seminorm p lborel (\<lambda>x. g x - s x)
                  + Lp_seminorm p lborel (\<lambda>x. s x - f x)"
      by (rule Lp_Minkowski_inequality[OF p_ge1 gs_meas sf_meas g_int s_int])
    also have "\<dots> < e" using g_lt sf_sem by linarith
    finally show ?thesis .
  qed

  show ?thesis
  proof (intro exI[of _ g] conjI)
    show "continuous_on UNIV g" by (rule g_cont)
    show "integrable lborel (\<lambda>x. \<bar>g x - f x\<bar> powr p)" by (rule gf_int)
    show "Lp_seminorm p lborel (\<lambda>x. g x - f x) < e" by (rule gf_sem)
  qed
qed

end
