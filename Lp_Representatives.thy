section \<open>Theorems 3.2 and 5.4 for arbitrary Lebesgue \<open>L\<^sup>p\<close> targets\<close>

theory Lp_Representatives
  imports Mollifier_Networks
begin

text \<open>
  The final form of the two general \<open>L\<^sup>p\<close> theorems: the target is assumed only measurable for
  the completed Lebesgue measure on its own domain, and only \<open>L\<^sup>p\<close> there.  No global Borel
  representative and no continuity is assumed of it, and the activation is assumed only Borel
  measurable.

  Both are read off the constructive theorems of \<^file>\<open>Mollifier_Networks.thy\<close> by instantiating
  the mollifier index.  Those theorems produce, for every large enough \<open>k\<close>, a network whose
  coefficients are the mollifier integrals of (3.4); taking any one such \<open>k\<close> and reading the
  network back through \<open>mollifier_network_eq\<close> exhibits it as the Theorem 3.1 network of the
  continuous function \<^const>\<open>mollified_target\<close>, which is what the existential statements below
  assert.  The paper's own construction therefore \<^emph>\<open>is\<close> the proof of the existential forms,
  rather than an alternative to them.
\<close>

(* Theorem 3.2: arbitrary Lebesgue Lp targets on the interval; measurable activation. *)
theorem sigmoidal_Lp_approximation_lebesgue:
  fixes f :: "real \<Rightarrow> real" and p \<epsilon> :: real
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and sm: "\<sigma> \<in> borel_measurable borel"
    and ab: "a < b"
    and fm: "f \<in> borel_measurable (lebesgue_on {a..b})"
    and fi: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>f x\<bar> powr p)"
    and p: "1 \<le> p" and eps: "0 < \<epsilon>"
  shows "\<exists>g N w. continuous_on {a..b} g \<and> 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x. G_network \<sigma> g a b N w x - f x) < ennreal \<epsilon>"
proof -
  obtain K where K: "0 < K"
    and all: "\<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
      Lp_enorm p (lebesgue_on {a..b})
        (\<lambda>x. mollifier_network \<sigma> f a b k N w x - f x) < ennreal \<epsilon>"
    using mollifier_approximation[OF sig bnd sm ab p fm fi eps] by blast
  obtain N w where N: "0 < N" and w: "0 < w"
    and bound: "Lp_enorm p (lebesgue_on {a..b})
      (\<lambda>x. mollifier_network \<sigma> f a b K N w x - f x) < ennreal \<epsilon>"
    using all by blast
  let ?g = "mollified_target {a..b} f K"
  have ab_borel: "{a..b} \<in> sets borel" by simp
  have cont_UNIV: "continuous_on UNIV ?g"
    by (rule mollified_target_Lp(1)[OF p bounded_closed_interval ab_borel fm fi])
  have gc: "continuous_on {a..b} ?g"
    by (rule continuous_on_subset[OF cont_UNIV]) simp
  have bound': "Lp_enorm p (lebesgue_on {a..b})
      (\<lambda>x. G_network \<sigma> ?g a b N w x - f x) < ennreal \<epsilon>"
    using bound by (simp only: mollifier_network_eq)
  show ?thesis
    by (intro exI[where x="?g"] exI[where x=N] exI[where x=w])
       (use gc N w bound' in blast)
qed

(* Theorem 5.4: Lebesgue Lp targets; operator correspondence is inherited from multivariate_network. *)
theorem multivariate_sigmoidal_Lp_approximation_lebesgue:
  fixes f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: 'n
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and sm: "\<sigma> \<in> borel_measurable borel" and ab: "a < b"
    and fm: "f \<in> borel_measurable (lebesgue_on {z. \<forall>r. z $ r \<in> {a..b}})"
    and fi: "integrable (lebesgue_on {z. \<forall>r. z $ r \<in> {a..b}}) (\<lambda>z. \<bar>f z\<bar> powr p)"
    and p: "1 \<le> p" and eps: "0 < \<epsilon>"
  shows "\<exists>g N w. continuous_on {z. \<forall>r. z $ r \<in> {a..b}} g \<and> 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {z. \<forall>r. z $ r \<in> {a..b}})
      (\<lambda>z. multivariate_network \<sigma> g r0 (unif_part a b N) N w z - f z) < ennreal \<epsilon>"
proof -
  let ?Q = "{z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}"
  have Q: "?Q = cbox (\<chi> r. a) (\<chi> r. b)" by (auto simp: mem_box_cart)
  have Qb: "bounded ?Q" unfolding Q by (rule bounded_cbox)
  have Qm: "?Q \<in> sets borel" unfolding Q by simp
  obtain K where K: "0 < K"
    and all: "\<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
      Lp_enorm p (lebesgue_on ?Q)
        (\<lambda>z. multivariate_mollifier_network \<sigma> f r0 a b k N w z - f z) < ennreal \<epsilon>"
    using multivariate_mollifier_approximation[OF sig bnd sm ab p fm fi eps] by blast
  obtain N w where N: "0 < N" and w: "0 < w"
    and bound: "Lp_enorm p (lebesgue_on ?Q)
      (\<lambda>z. multivariate_mollifier_network \<sigma> f r0 a b K N w z - f z) < ennreal \<epsilon>"
    using all by blast
  let ?g = "mollified_target ?Q f K"
  have cont_UNIV: "continuous_on UNIV ?g"
    by (rule mollified_target_Lp(1)[OF p Qb Qm fm fi])
  have gc: "continuous_on ?Q ?g"
    by (rule continuous_on_subset[OF cont_UNIV]) simp
  have bound': "Lp_enorm p (lebesgue_on ?Q)
      (\<lambda>z. multivariate_network \<sigma> ?g r0 (unif_part a b N) N w z - f z) < ennreal \<epsilon>"
    using bound by (simp only: multivariate_mollifier_network_eq)
  show ?thesis
    by (intro exI[where x="?g"] exI[where x=N] exI[where x=w])
       (use gc N w bound' in blast)
qed

end
