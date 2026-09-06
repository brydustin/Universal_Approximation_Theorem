section \<open>Theorem 3.2: \<open>L\<^sup>p\<close> approximation for \<open>f\<close> not assumed continuous\<close>

theory Lp_Approximation_General
  imports Lp_Representatives
begin

text \<open>
  Theorem 3.2 of Costarelli--Spigler: the \<open>L\<^sup>p[a,b]\<close> universal approximation theorem with \<open>f\<close>
  only assumed to lie in \<open>L\<^sup>p[a,b]\<close>, not continuous.  This is the theorem in its literal
  printed form, for a Borel target.

  A Borel target is in particular measurable for \<open>lebesgue_on {a..b}\<close>, so this is the special
  case of \<open>sigmoidal_Lp_approximation_lebesgue\<close> (\<^file>\<open>Lp_Representatives.thy\<close>) in which the
  target happens to have a globally Borel representative already.  The proof is that
  observation and nothing else.

  Consequently the printed statement is obtained \<^emph>\<open>through\<close> the paper's own construction:
  the witness \<open>g\<close> produced below is the mollified target \<open>\<rho>\<^sub>k*f\<close> of
  \<^file>\<open>Mollifiers.thy\<close>, and the network is the integral-coefficient network of
  \<^file>\<open>Mollifier_Networks.thy\<close> read through \<open>mollifier_network_eq\<close>.  No result in the
  project now depends on an existence-only choice of continuous approximant: density of
  continuous functions (\<^file>\<open>Lp_Density.thy\<close>) survives only as an ingredient \<^emph>\<open>inside\<close> the
  mollifier convergence proof, where it supplies compactly supported comparison functions.

  The earlier direct proof of this statement -- Theorem 3.1 against a continuous approximant
  from \<open>continuous_dense_Lp\<close>, glued with Minkowski -- was independent of the mollifier
  development and is no longer carried.  What it needed from the measure-theoretic
  bookkeeping between \<open>lebesgue_on {a..b} = restrict_space (completion lborel) {a..b}\<close> and
  \<open>lborel\<close> now lives in \<^file>\<open>Lp_Restriction.thy\<close>, still used by the mollifier construction.
\<close>

text \<open>Continuity of the sigmoidal network of Theorem 3.1, as a function of \<open>x\<close>.\<close>

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma sigmoidal_network_continuous:
  fixes \<sigma> :: "real \<Rightarrow> real" and w :: real
  assumes cont_sigmoidal: "continuous_on UNIV \<sigma>"
  shows "continuous_on S (\<lambda>x. (\<Sum>k\<in>{2..N+1}. c k * \<sigma> (w * (x - d k))) + e0 * \<sigma> (w * (x - d0)))"
proof -
  have shift: "\<And>t. continuous_on S (\<lambda>x. \<sigma> (w * (x - t)))"
  proof -
    fix t
    have "continuous_on S (\<lambda>x. w * (x - t))" by (intro continuous_intros)
    then show "continuous_on S (\<lambda>x. \<sigma> (w * (x - t)))"
      by (rule continuous_on_compose2[OF cont_sigmoidal]) simp
  qed
  have "continuous_on S (\<lambda>x. \<Sum>k\<in>{2..N+1}. c k * \<sigma> (w * (x - d k)))"
  proof (rule continuous_on_sum)
    fix k assume "k \<in> {2..N+1}"
    show "continuous_on S (\<lambda>x. c k * \<sigma> (w * (x - d k)))"
      using shift by (intro continuous_intros)
  qed
  moreover have "continuous_on S (\<lambda>x. e0 * \<sigma> (w * (x - d0)))"
    using shift by (intro continuous_intros)
  ultimately show ?thesis by (rule continuous_on_add)
qed

subsection \<open>Theorem 3.2\<close>

(* Theorem 3.2: Lp approximation; Borel representative version. *)
theorem sigmoidal_Lp_approximation_theorem_general:
  fixes f :: "real \<Rightarrow> real" and p \<epsilon> :: real
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  assumes a_lt_b: "a < b"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_int: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>f x\<bar> powr p)"
  assumes p_geq_1: "p \<ge> (1::real)"
  assumes eps_pos: "0 < \<epsilon>"
  defines "xs N \<equiv> unif_part a b N"
  shows "\<exists>g. continuous_on {a..b} g \<and> (\<exists>N::nat. \<exists>(w::real) > 0. N > 0 \<and>
           Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x.
               (\<Sum>k\<in>{2..N+1}. (g(xs N ! k) - g(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + g(a) * \<sigma>(w * (x - xs N ! 0)) - f x) < ennreal \<epsilon>)"
proof -
  have f_leb: "f \<in> borel_measurable (lebesgue_on {a..b})"
    by (rule borel_measurable_lebesgue_onI[OF f_meas])
  have key: "\<exists>g N w. continuous_on {a..b} g \<and> 0 < N \<and> 0 < w \<and>
      Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x. G_network \<sigma> g a b N w x - f x) < ennreal \<epsilon>"
    by (rule sigmoidal_Lp_approximation_lebesgue[OF sigmoidal_function bounded_sigmoidal
          meas_sigmoidal a_lt_b f_leb f_int p_geq_1 eps_pos])
  show ?thesis
    unfolding xs_def using key[unfolded G_network_def] by blast
qed

end
