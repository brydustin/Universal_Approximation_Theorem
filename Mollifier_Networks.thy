section \<open>Networks with the mollifier-integral coefficients of (3.4)\<close>

theory Mollifier_Networks
  imports Mollifiers Multivariate_Approximation
begin

text \<open>
  The networks the paper actually writes down.  Theorem 3.1 (\<^file>\<open>Lp_Approximation.thy\<close>)
  and Theorem 5.3 (\<^file>\<open>Multivariate_Approximation.thy\<close>) approximate a \<^emph>\<open>continuous\<close>
  target, and their coefficients are increments \<open>g(x\<^sub>j) - g(x\<^sub>j\<^sub>-\<^sub>1)\<close> of that target.  Composing
  them with the mollified target of \<^file>\<open>Mollifiers.thy\<close> turns those increments into the
  explicit convolution integrals of equation (3.4): \<open>mollifier_coefficient\<close>.

  The point of this theory is that the resulting statements are constructive in the
  coefficients.  \<open>mollifier_approximation\<close> and \<open>multivariate_mollifier_approximation\<close>
  approximate an arbitrary Lebesgue \<open>L\<^sup>p\<close> target by a network whose weights are written out as
  integrals of that target, with no appeal to an unspecified continuous function; the
  existential forms of Theorems 3.2 and 5.4 in \<^file>\<open>Lp_Representatives.thy\<close> follow from them
  by instantiation.
\<close>

(* Coefficient formula following (3.4): difference of two convolution integrals; also the coefficient construction in Theorem 5.4. *)
definition mollifier_coefficient where
  "mollifier_coefficient S f k u v =
    (\<integral>y. mollifier k (u-y)*f y \<partial>(lebesgue_on S)) -
    (\<integral>y. mollifier k (v-y)*f y \<partial>(lebesgue_on S))"

(* Coefficient formulas following (3.4): the literal whole-space integrals of the zero extension. *)
lemma mollifier_coefficient_zero_extension:
  fixes S :: "'a::euclidean_space set"
  assumes Sm: "S \<in> sets borel"
  shows "mollifier_coefficient S f k u v =
    (\<integral>y. mollifier k (u-y)*zero_extension S f y \<partial>lebesgue) -
    (\<integral>y. mollifier k (v-y)*zero_extension S f y \<partial>lebesgue)"
proof -
  have "mollifier_coefficient S f k u v = mollified_target S f k u-mollified_target S f k v"
    by (simp only: mollifier_coefficient_def mollified_target_def)
  then show ?thesis by (simp only: mollified_target_zero_extension[OF Sm])
qed

(* Coefficient formulas following (3.4): equivalent single-integral difference, valid also for unbounded Lp targets. *)
lemma mollifier_coefficient_single_integral:
  fixes S :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and Sb: "bounded S" and Sm: "S \<in> sets borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and fpi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "mollifier_coefficient S f k u v =
    (\<integral>y. (mollifier k (u-y)-mollifier k (v-y))*f y \<partial>(lebesgue_on S))"
  unfolding mollifier_coefficient_def
  by (simp only: left_diff_distrib Bochner_Integration.integral_diff[
    OF mollified_target_integrand_integrable[OF p Sb Sm fm fpi]
       mollified_target_integrand_integrable[OF p Sb Sm fm fpi]])

(* Unnumbered network formula following (3.4), p. 175. List indices 2..N+1 correspond to paper indices 1..N. *)
definition mollifier_network where
  "mollifier_network act f a b k N w x =
    (\<Sum>j\<in>{2..N+1}. mollifier_coefficient {a..b} f k
      (unif_part a b N ! j) (unif_part a b N ! (j-1)) *
      act (w*(x-unif_part a b N ! j))) +
    (\<integral>y. mollifier k (a-y)*f y \<partial>(lebesgue_on {a..b})) *
      act (w*(x-unif_part a b N ! 0))"

(* Coefficients following (3.4): the integral-coefficient network is exactly G_N(rho_k * f-tilde). *)
lemma mollifier_network_eq:
  "mollifier_network act f a b k N w =
    G_network act (mollified_target {a..b} f k) a b N w"
  by (rule ext) (simp only: mollifier_network_def G_network_def
      mollifier_coefficient_def mollified_target_def)

(* Proof of Theorem 5.4: equation (5.1) with convolution-integral coefficients; no separately numbered coefficient formula. *)
definition multivariate_mollifier_network where
  "multivariate_mollifier_network act f r0 a b k N w z =
    (\<Sum>c\<in>column_index r0 N. \<Sum>j\<in>{1..N}.
      mollifier_coefficient {y. \<forall>r. y$r \<in> {a..b}} f k
        (sample_point r0 (unif_part a b N) c j)
        (sample_point r0 (unif_part a b N) c (j-1)) *
      act (w * column_sign r0 (unif_part a b N) c j z *
        norm (z-grid_point r0 (unif_part a b N) c j))) +
    (\<Sum>c\<in>column_index r0 N.
      (\<integral>y. mollifier k (sample_point r0 (unif_part a b N) c 0-y)*f y
        \<partial>(lebesgue_on {y. \<forall>r. y$r \<in> {a..b}})) *
      act (w * column_sign r0 (unif_part a b N) c 0 z *
        norm (z-sigma_anchor r0 (unif_part a b N) c 0)))"

(* Theorem 5.4, proof: exact equality to the endpoint-sampling network applied to the mollified target. *)
lemma multivariate_mollifier_network_eq:
  "multivariate_mollifier_network act f r0 a b k N w =
    multivariate_network act (mollified_target {y. \<forall>r. y$r \<in> {a..b}} f k)
      r0 (unif_part a b N) N w"
  by (rule ext) (simp only: multivariate_mollifier_network_def multivariate_network_def
      mollifier_coefficient_def mollified_target_def)

(* Auxiliary for Theorems 3.2 and 5.4: the two epsilon/2 estimates imply the final finite Lp error. *)
lemma Lp_join_approximation:
  fixes A g f :: "'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and e: "0 < e"
    and Am: "A \<in> borel_measurable M" and gm: "g \<in> borel_measurable M"
    and fm: "f \<in> borel_measurable M"
    and ag: "Lp_enorm p M (\<lambda>x. A x-g x) < ennreal (e/2)"
    and gfi: "integrable M (\<lambda>x. \<bar>g x-f x\<bar> powr p)"
    and gf: "Lp_seminorm p M (\<lambda>x. g x-f x) < e/2"
  shows "Lp_enorm p M (\<lambda>x. A x-f x) < ennreal e"
proof -
  have agi: "integrable M (\<lambda>x. \<bar>A x-g x\<bar> powr p)"
    by (rule Lp_enorm_finite_integrable) (use ag in \<open>auto intro: less_trans\<close>)
  have ags: "Lp_seminorm p M (\<lambda>x. A x-g x) < e/2"
    using ag unfolding Lp_enorm_eq_seminorm[OF agi]
    by (simp add: ennreal_less_iff Lp_seminorm_nonneg)
  have agm: "(\<lambda>x. A x-g x) \<in> borel_measurable M" using Am gm by measurable
  have gfm: "(\<lambda>x. g x-f x) \<in> borel_measurable M" using gm fm by measurable
  have af: "(\<lambda>x. (A x-g x)+(g x-f x)) = (\<lambda>x. A x-f x)" by simp
  have afi: "integrable M (\<lambda>x. \<bar>A x-f x\<bar> powr p)"
    using Lp_Minkowski_integrable[OF p agm gfm agi gfi] by simp
  have "Lp_seminorm p M (\<lambda>x. A x-f x) \<le>
      Lp_seminorm p M (\<lambda>x. A x-g x) + Lp_seminorm p M (\<lambda>x. g x-f x)"
    using Lp_Minkowski_inequality[OF p agm gfm agi gfi] by (simp only: af)
  then have "Lp_seminorm p M (\<lambda>x. A x-f x) < e" using ags gf by linarith
  then show ?thesis unfolding Lp_enorm_eq_seminorm[OF afi]
    by (rule ennreal_lessI[OF e])
qed

(* Proofs of Theorems 3.2 and 5.4: first choose the mollifier index, then approximate that specific mollified target. *)
lemma mollified_network_approximation:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and S :: "'a set"
    and A :: "('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  assumes p: "1 \<le> p" and Sb: "bounded S" and Sm: "S \<in> sets borel"
    and fm: "f \<in> borel_measurable (lebesgue_on S)"
    and fpi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
    and e: "0 < e"
    and approx: "\<And>g d. continuous_on S g \<Longrightarrow> 0 < d \<Longrightarrow>
      \<exists>N w. 0 < N \<and> 0 < w \<and> Lp_enorm p (lebesgue_on S) (\<lambda>x. A g N w x-g x) < ennreal d"
    and Am: "\<And>g N w. A g N w \<in> borel_measurable (lebesgue_on S)"
  shows "\<exists>K>0. \<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on S) (\<lambda>x. A (mollified_target S f k) N w x-f x) < ennreal e"
proof -
  have e2: "0 < e/2" using e by simp
  have lim: "(\<lambda>k. Lp_seminorm p (lebesgue_on S)
      (\<lambda>x. mollified_target S f k x-f x)) \<longlonglongrightarrow> 0"
    by (rule mollified_target_Lp(3)[OF p Sb Sm fm fpi])
  obtain K where K: "\<And>k. K \<le> k \<Longrightarrow> Lp_seminorm p (lebesgue_on S)
      (\<lambda>x. mollified_target S f k x-f x) < e/2"
    using order_tendstoD(2)[OF lim e2] unfolding eventually_sequentially by blast
  have all: "\<forall>k\<ge>Suc K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on S) (\<lambda>x. A (mollified_target S f k) N w x-f x) < ennreal e"
  proof (intro allI impI)
    fix k assume k: "Suc K \<le> k"
    let ?g = "mollified_target S f k"
    have kc: "continuous_on UNIV ?g" by (rule mollified_target_Lp(1)[OF p Sb Sm fm fpi])
    have gc: "continuous_on S ?g" by (rule continuous_on_subset[OF kc]) simp
    have gm: "?g \<in> borel_measurable (lebesgue_on S)"
      by (rule borel_measurable_lebesgue_onI[OF borel_measurable_continuous_onI[OF kc]])
    obtain N w where N: "0 < N" and w: "0 < w"
      and ag: "Lp_enorm p (lebesgue_on S) (\<lambda>x. A ?g N w x-?g x) < ennreal (e/2)"
      using approx[OF gc e2] by blast
    have gfi: "integrable (lebesgue_on S) (\<lambda>x. \<bar>?g x-f x\<bar> powr p)"
      by (rule mollified_target_Lp(2)[OF p Sb Sm fm fpi]) (use k in simp)
    have ge: "Lp_seminorm p (lebesgue_on S) (\<lambda>x. ?g x-f x) < e/2"
      by (rule K) (use k in simp)
    have result: "Lp_enorm p (lebesgue_on S) (\<lambda>x. A ?g N w x-f x) < ennreal e"
      by (rule Lp_join_approximation[OF p e Am gm fm ag gfi ge])
    show "\<exists>N w. 0 < N \<and> 0 < w \<and>
      Lp_enorm p (lebesgue_on S) (\<lambda>x. A ?g N w x-f x) < ennreal e"
      by (intro exI[where x=N] exI[where x=w]) (use N w result in simp)
  qed
  show ?thesis by (intro exI[where x="Suc K"]) (use all in simp)
qed

(* Theorem 3.2 and coefficient formulas after (3.4): the explicit mollifier network approximates every Lebesgue Lp target. *)
theorem mollifier_approximation:
  fixes f :: "real \<Rightarrow> real"
  assumes sig: "sigmoidal act" and bnd: "bounded_function act"
    and sm: "act \<in> borel_measurable borel" and ab: "a < b" and p: "1 \<le> p"
    and fm: "f \<in> borel_measurable (lebesgue_on {a..b})"
    and fpi: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>f x\<bar> powr p)" and e: "0 < e"
  shows "\<exists>K>0. \<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {a..b})
      (\<lambda>x. mollifier_network act f a b k N w x-f x) < ennreal e"
proof -
  let ?A = "\<lambda>g N w. G_network act g a b N w"
  have approx: "\<And>g d. continuous_on {a..b} g \<Longrightarrow> 0 < d \<Longrightarrow>
      \<exists>N w. 0 < N \<and> 0 < w \<and>
      Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x. ?A g N w x-g x) < ennreal d"
    using sigmoidal_Lp_approximation_theorem[OF sig bnd sm ab _ p]
    unfolding G_network_def by blast
  have Am: "\<And>g N w. ?A g N w \<in> borel_measurable (lebesgue_on {a..b})"
    by (rule borel_measurable_lebesgue_onI[OF G_network_measurable[OF sm]])
  show ?thesis unfolding mollifier_network_eq
    by (rule mollified_network_approximation[OF p bounded_closed_interval _ fm fpi e approx Am]) simp
qed

(* Theorem 5.4, constructive proof: equation (5.1) with integral coefficients from the exact radial mollifier. *)
theorem multivariate_mollifier_approximation:
  fixes f :: "(real,'n::finite) vec \<Rightarrow> real" and r0 :: 'n
  assumes sig: "sigmoidal act" and bnd: "bounded_function act"
    and sm: "act \<in> borel_measurable borel" and ab: "a < b" and p: "1 \<le> p"
    and fm: "f \<in> borel_measurable (lebesgue_on {z. \<forall>r. z$r \<in> {a..b}})"
    and fpi: "integrable (lebesgue_on {z. \<forall>r. z$r \<in> {a..b}}) (\<lambda>x. \<bar>f x\<bar> powr p)"
    and e: "0 < e"
  shows "\<exists>K>0. \<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {z. \<forall>r. z$r \<in> {a..b}})
      (\<lambda>x. multivariate_mollifier_network act f r0 a b k N w x-f x) < ennreal e"
proof -
  let ?Q = "{z::(real,'n) vec. \<forall>r. z$r \<in> {a..b}}"
  let ?A = "\<lambda>g N w. multivariate_network act g r0 (unif_part a b N) N w"
  have Q: "?Q = cbox (\<chi> r. a) (\<chi> r. b)" by (auto simp: mem_box_cart)
  have Qb: "bounded ?Q" unfolding Q by (rule bounded_cbox)
  have Qm: "?Q \<in> sets borel" unfolding Q by simp
  have approx: "\<And>g d. continuous_on ?Q g \<Longrightarrow> 0 < d \<Longrightarrow>
      \<exists>N w. 0 < N \<and> 0 < w \<and> Lp_enorm p (lebesgue_on ?Q) (\<lambda>x. ?A g N w x-g x) < ennreal d"
    using multivariate_sigmoidal_Lp_approximation_theorem[OF sig bnd sm ab _ p] by blast
  have Am: "\<And>g N w. ?A g N w \<in> borel_measurable (lebesgue_on ?Q)"
    by (rule borel_measurable_lebesgue_onI[OF multivariate_network_measurable[OF sm]])
  show ?thesis unfolding multivariate_mollifier_network_eq
    by (rule mollified_network_approximation[OF p Qb Qm fm fpi e approx Am])
qed

end
