section \<open>Theorem 5.4: multivariate \<open>L\<^sup>p\<close> approximation for \<open>f\<close> not assumed continuous\<close>

theory Multivariate_Lp_Approximation_General
  imports Multivariate_Approximation Lp_Approximation_General
begin

text \<open>
  The multivariate analogue of Theorem 3.2 (\<open>sigmoidal_Lp_approximation_theorem_general\<close>,
  \<^file>\<open>Lp_Approximation_General.thy\<close>): Theorem 5.3 assumes \<open>f\<close> continuous on the box, and this
  drops that, assuming only \<open>f \<in> L\<^sup>p\<close> of the box.

  As in the one-dimensional case, a Borel target is measurable for the completed Lebesgue
  measure on the box, so this is the special case of
  \<open>multivariate_sigmoidal_Lp_approximation_lebesgue\<close> (\<^file>\<open>Lp_Representatives.thy\<close>) in
  which a global Borel representative is already given, and the witness is the mollified
  target of \<^file>\<open>Mollifiers.thy\<close> rather than an unspecified continuous function.

  The earlier direct proof mirrored Theorem 5.3's own argument rather than using it as a black
  box, because \<^const>\<open>multivariate_network\<close> is deliberately not continuous in \<open>z\<close> and a small
  \<open>Lp_seminorm\<close> does not by itself give the integrability that Minkowski needs as a side
  condition.  That obstacle is now handled once and for all upstream, by
  \<open>mollified_target_Lp\<close>, which returns the integrability of \<open>\<bar>\<rho>\<^sub>k*f - f\<bar>\<^sup>p\<close> along with the
  convergence.
\<close>

(* Theorem 5.4: endpoint-sampling operator; Borel representative version. *)
theorem multivariate_sigmoidal_Lp_approximation_theorem_general:
  fixes a b :: real and f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: "'n::finite"
  fixes \<sigma> :: "real \<Rightarrow> real" and p \<epsilon> :: real
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  assumes a_lt_b: "a < b"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_int: "integrable (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})
                    (\<lambda>z. \<bar>f z\<bar> powr p)"
  assumes p_geq_1: "p \<ge> (1::real)"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>g. continuous_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}} g
       \<and> (\<exists>N::nat. \<exists>(w::real) > 0. N > 0 \<and>
           Lp_enorm p (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})
             (\<lambda>z. multivariate_network \<sigma> g r0 (unif_part a b N) N w z - f z) < ennreal \<epsilon>)"
proof -
  have f_leb: "f \<in> borel_measurable (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})"
    by (rule borel_measurable_lebesgue_onI[OF f_meas])
  show ?thesis
    using multivariate_sigmoidal_Lp_approximation_lebesgue[OF sigmoidal_function
        bounded_sigmoidal meas_sigmoidal a_lt_b f_leb f_int p_geq_1 eps_pos]
    by blast
qed

end
