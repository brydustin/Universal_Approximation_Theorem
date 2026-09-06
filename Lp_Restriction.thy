section \<open>Restriction, zero extension and almost-everywhere representatives\<close>

theory Lp_Restriction
  imports Lp_Approximation
begin

text \<open>
  Measure-theoretic bookkeeping shared by every \<open>L\<^sup>p\<close> result in the project, collected in one
  place below the theorems that use it so that none of them has to import another.

  Two kinds of fact live here.  First, bridges between the three measures the development moves
  among: \<open>Lp_norm\<close> and \<open>multivariate_Lp_norm\<close> live on
  \<open>lebesgue_on S = restrict_space (completion lborel) S\<close>, while the density theorem
  (\<^file>\<open>Lp_Density.thy\<close>) and the mollifier construction (\<^file>\<open>Mollifiers.thy\<close>) live on
  \<open>lborel\<close>.  The bridges use \<open>integral_restrict_space\<close> (restriction \<open>\<leftrightarrow>\<close> multiplication by an
  indicator) and \<open>integral_completion\<close> (completing the measure does not change integrals of
  Borel-measurable functions).

  Second, almost-everywhere representatives: a function measurable for the completed measure
  \<open>lebesgue_on S\<close> agrees almost everywhere with a Borel function, and both \<open>L\<^sup>p\<close>
  integrability and the \<open>L\<^sup>p\<close> error are insensitive to that change.  This is what lets the
  final theorems assume only \<open>lebesgue_on S\<close>-measurability of the target while their proofs
  work with a Borel representative.
\<close>

subsection \<open>Bridges between \<open>Lp_norm\<close> on \<open>[a,b]\<close> and \<open>Lp_seminorm\<close> on \<open>lborel\<close>\<close>

text \<open>NB the explicit \<open>fixes\<close> clause is REQUIRED, not decoration. Stated as a bare
  \<open>lemma "Lp_norm p a b h = \<dots>"\<close>, the variable \<open>h\<close> is stored UN-generalized -- the theorem comes
  out as \<open>Lp_norm ?p ?a ?b h = Lp_seminorm ?p (lebesgue_on {?a..?b}) h\<close>, with \<open>?p\<close>, \<open>?a\<close>, \<open>?b\<close>
  schematic but \<open>h\<close> a fixed free variable -- so \<open>rule\<close>/\<open>simp\<close> can only ever apply it to a
  function literally named \<open>h\<close>, and it fails on every real call site while the goal still prints
  as exactly its own instance. Renaming the variable (e.g. to \<open>hh\<close>) or adding \<open>fixes\<close> both cure
  it. Same root cause as the earlier "No such variable in theorem: ?h" on
  \<open>abs_powr_measurable\<close>.\<close>

text \<open>
  \<^const>\<open>Lp_norm\<close> carries an integrability guard (see \<^file>\<open>Lp_Approximation.thy\<close>) while
  \<^const>\<open>Lp_seminorm\<close> -- used for H\"older and Minkowski, where the arguments always come
  with their own integrability hypotheses -- does not.  The bridge between them therefore
  holds on integrable arguments, which is the only regime in which either is used below.
\<close>
(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma Lp_norm_eq_seminorm:
  fixes p a b :: real and h :: "real \<Rightarrow> real"
  assumes h_int: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "Lp_norm p a b h = Lp_seminorm p (lebesgue_on {a..b}) h"
  unfolding Lp_norm_integrable_eq[OF h_int] Lp_seminorm_def by (rule refl)

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma powr_indicator_measurable:
  fixes h :: "'a::euclidean_space \<Rightarrow> real" and p :: real and S :: "'a set"
  assumes p_pos: "0 < p"
  assumes S_meas: "S \<in> sets borel"
  assumes h_meas: "h \<in> borel_measurable borel"
  shows "(\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p) \<in> borel_measurable lborel"
proof -
  have h_meas': "h \<in> borel_measurable lborel"
    using h_meas measurable_cong_sets[OF sets_lborel refl] by simp
  have hp: "(\<lambda>x. \<bar>h x\<bar> powr p) \<in> borel_measurable lborel"
    by (rule abs_powr_measurable[OF p_pos h_meas'])
  have S_l: "S \<in> sets lborel" using S_meas by simp
  show ?thesis using hp S_l by measurable
qed

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma powr_indicator_integrable:
  fixes h :: "'a::euclidean_space \<Rightarrow> real" and p :: real and S :: "'a set"
  assumes p_pos: "0 < p"
  assumes S_meas: "S \<in> sets borel"
  assumes h_meas: "h \<in> borel_measurable borel"
  assumes h_int: "integrable lborel (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "integrable lborel (\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p)"
proof -
  have meas: "(\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p) \<in> borel_measurable lborel"
    by (rule powr_indicator_measurable[OF p_pos S_meas h_meas])
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF h_int meas])
    show "AE x in lborel. norm (indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p) \<le> norm (\<bar>h x\<bar> powr p)"
      by (intro AE_I2) (simp add: indicator_def)
  qed
qed

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma integrable_powr_restrict_gen:
  fixes h :: "'a::euclidean_space \<Rightarrow> real" and p :: real and S :: "'a set"
  assumes p_pos: "0 < p"
  assumes S_meas: "S \<in> sets borel"
  assumes h_meas: "h \<in> borel_measurable borel"
  assumes h_int: "integrable lborel (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "integrable (lebesgue_on S) (\<lambda>x. \<bar>h x\<bar> powr p)"
proof -
  have meas: "(\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p) \<in> borel_measurable lborel"
    by (rule powr_indicator_measurable[OF p_pos S_meas h_meas])
  have i1: "integrable lborel (\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p)"
    by (rule powr_indicator_integrable[OF p_pos S_meas h_meas h_int])
  have i2: "integrable lebesgue (\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p)"
    using i1 meas by (simp only: integrable_completion)
  have S_leb: "S \<inter> space lebesgue \<in> sets lebesgue"
    using S_meas by simp
  show ?thesis using i2 S_leb by (simp only: integrable_restrict_space)
qed

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma Lp_seminorm_restrict_le:
  fixes h :: "'a::euclidean_space \<Rightarrow> real" and p :: real and S :: "'a set"
  assumes p_pos: "0 < p"
  assumes S_meas: "S \<in> sets borel"
  assumes h_meas: "h \<in> borel_measurable borel"
  assumes h_int: "integrable lborel (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "Lp_seminorm p (lebesgue_on S) h \<le> Lp_seminorm p lborel h"
proof -
  have meas: "(\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p) \<in> borel_measurable lborel"
    by (rule powr_indicator_measurable[OF p_pos S_meas h_meas])
  have i1: "integrable lborel (\<lambda>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p)"
    by (rule powr_indicator_integrable[OF p_pos S_meas h_meas h_int])
  have S_leb: "S \<inter> space lebesgue \<in> sets lebesgue"
    using S_meas by simp
  have restr: "(\<integral>x. \<bar>h x\<bar> powr p \<partial>(lebesgue_on S))
             = (\<integral>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p \<partial>lborel)"
  proof -
    have "(\<integral>x. \<bar>h x\<bar> powr p \<partial>(lebesgue_on S))
        = (\<integral>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p \<partial>lebesgue)"
      by (rule integral_restrict_space) (rule S_leb)
    also have "\<dots> = (\<integral>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p \<partial>lborel)"
      by (rule integral_completion[OF meas])
    finally show ?thesis .
  qed
  have le_int: "(\<integral>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p \<partial>lborel)
              \<le> (\<integral>x. \<bar>h x\<bar> powr p \<partial>lborel)"
  proof (rule integral_mono_AE[OF i1 h_int])
    show "AE x in lborel. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p \<le> \<bar>h x\<bar> powr p"
      by (intro AE_I2) (simp add: indicator_def)
  qed
  have nonneg: "0 \<le> (\<integral>x. indicat_real S x *\<^sub>R \<bar>h x\<bar> powr p \<partial>lborel)"
    by (rule integral_nonneg_AE) (simp add: indicator_def)
  show ?thesis
    unfolding Lp_seminorm_def restr
    using nonneg le_int p_pos by (intro powr_mono2) auto
qed

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma integrable_powr_zero_extension_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and p :: real and S :: "'a set"
  assumes p_pos: "0 < p"
  assumes S_meas: "S \<in> sets borel"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_int: "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "integrable lborel (\<lambda>x. \<bar>(if x \<in> S then f x else 0)\<bar> powr p)"
proof -
  have meas: "(\<lambda>x. indicat_real S x *\<^sub>R \<bar>f x\<bar> powr p) \<in> borel_measurable lborel"
    by (rule powr_indicator_measurable[OF p_pos S_meas f_meas])
  have S_leb: "S \<inter> space lebesgue \<in> sets lebesgue"
    using S_meas by simp
  have i1: "integrable lebesgue (\<lambda>x. indicat_real S x *\<^sub>R \<bar>f x\<bar> powr p)"
    using f_int S_leb by (simp only: integrable_restrict_space)
  have i2: "integrable lborel (\<lambda>x. indicat_real S x *\<^sub>R \<bar>f x\<bar> powr p)"
    using i1 meas by (simp only: integrable_completion)
  have eq: "(\<lambda>x. \<bar>(if x \<in> S then f x else 0)\<bar> powr p)
          = (\<lambda>x. indicat_real S x *\<^sub>R \<bar>f x\<bar> powr p)"
    using p_pos by (simp add: fun_eq_iff indicator_def)
  show ?thesis using i2 eq by simp
qed

text \<open>The \<open>{a..b}\<close> instances, as used by Theorem 3.2 below.\<close>

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma integrable_powr_restrict:
  fixes h :: "real \<Rightarrow> real" and p :: real
  assumes p_pos: "0 < p"
  assumes h_meas: "h \<in> borel_measurable borel"
  assumes h_int: "integrable lborel (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>h x\<bar> powr p)"
  by (rule integrable_powr_restrict_gen[OF p_pos _ h_meas h_int]) simp

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma Lp_norm_le_lborel:
  fixes h :: "real \<Rightarrow> real" and p :: real
  assumes p_pos: "0 < p"
  assumes h_meas: "h \<in> borel_measurable borel"
  assumes h_int: "integrable lborel (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "Lp_norm p a b h \<le> Lp_seminorm p lborel h"
proof -
  have "Lp_seminorm p (lebesgue_on {a..b}) h \<le> Lp_seminorm p lborel h"
    by (rule Lp_seminorm_restrict_le[OF p_pos _ h_meas h_int]) simp
  moreover have "Lp_norm p a b h = Lp_seminorm p (lebesgue_on {a..b}) h"
    by (rule Lp_norm_eq_seminorm[OF integrable_powr_restrict[OF p_pos h_meas h_int]])
  ultimately show ?thesis by simp
qed

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma integrable_powr_zero_extension:
  fixes f :: "real \<Rightarrow> real" and p :: real
  assumes p_pos: "0 < p"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_int: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "integrable lborel (\<lambda>x. \<bar>(if x \<in> {a..b} then f x else 0)\<bar> powr p)"
  by (rule integrable_powr_zero_extension_gen[OF p_pos _ f_meas f_int]) simp

text \<open>A \<open>real\<close>-typed restatement of \<open>borel_measurable_lebesgue_onI\<close>
  (\<^file>\<open>Lp_Inequalities.thy\<close>) with the domain type fixed; same two-step proof.\<close>

(* Auxiliary for Theorem 3.2; not separately numbered. *)
lemma borel_measurable_lebesgue_on_real:
  fixes h :: "real \<Rightarrow> real"
  assumes h_meas: "h \<in> borel_measurable borel"
  shows "h \<in> borel_measurable (lebesgue_on Q)"
proof -
  have h_lborel: "h \<in> borel_measurable lborel"
    using h_meas unfolding measurable_def by simp
  have h_lebesgue: "h \<in> borel_measurable lebesgue"
    using measurable_completion[OF h_lborel] .
  show ?thesis using measurable_restrict_space1[OF h_lebesgue] .
qed

(* Auxiliary for Theorems 3.2 and 5.4: Borel representatives on the approximation domain. *)
lemma Lp_borel_representative_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes S: "S \<in> sets borel"
  assumes meas: "f \<in> borel_measurable (lebesgue_on S)"
  obtains g where "g \<in> borel_measurable borel"
    "AE x in lebesgue_on S. f x = g x"
proof -
  have S_leb: "S \<inter> space lebesgue \<in> sets lebesgue"
    using S by simp
  have F_meas: "(\<lambda>x. indicator S x *\<^sub>R f x) \<in> borel_measurable lebesgue"
    using meas borel_measurable_restrict_space_iff[OF S_leb, of f] by simp
  obtain g where g_meas: "g \<in> borel_measurable lborel"
    and eq: "AE x in lborel. indicator S x *\<^sub>R f x = g x"
    using completion_ex_borel_measurable_real[OF F_meas] by blast
  have g_borel: "g \<in> borel_measurable borel"
    using g_meas by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have eq_leb: "AE x in lebesgue. indicator S x *\<^sub>R f x = g x"
    using eq by (rule AE_completion)
  have eq_S: "AE x in lebesgue_on S. f x = g x"
    unfolding AE_restrict_space_iff[OF S_leb]
    using eq_leb by eventually_elim (auto simp: indicator_def)
  show thesis using that[OF g_borel eq_S] .
qed

(* Auxiliary for Theorems 3.2 and 5.4: approximation errors respect almost-everywhere equality. *)
lemma Lp_enorm_cong_AE:
  fixes f g :: "'a \<Rightarrow> real"
  assumes p: "0 < p"
  assumes fm: "f \<in> borel_measurable M" and gm: "g \<in> borel_measurable M"
  assumes eq: "AE x in M. f x = g x"
  shows "Lp_enorm p M f = Lp_enorm p M g"
proof -
  have fp: "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> borel_measurable M"
    using fm by measurable
  have gp: "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> borel_measurable M"
    using gm by measurable
  have nn: "(\<integral>\<^sup>+x. ennreal (\<bar>f x\<bar> powr p) \<partial>M) =
            (\<integral>\<^sup>+x. ennreal (\<bar>g x\<bar> powr p) \<partial>M)"
    by (rule nn_integral_cong_AE) (use eq in eventually_elim, simp)
  show ?thesis unfolding Lp_enorm_measurable_eq[OF fp] Lp_enorm_measurable_eq[OF gp]
    using nn by simp
qed

(* Auxiliary for Theorems 3.1-3.2: measurability of equation (2.2). *)
lemma G_network_measurable:
  assumes meas: "\<sigma> \<in> borel_measurable borel"
  shows "G_network \<sigma> f a b N w \<in> borel_measurable borel"
  unfolding G_network_def using meas by measurable

(* Auxiliary for Theorems 3.2 and 5.4: transfer of Lp integrability to a representative. *)
lemma Lp_representative_integrable:
  fixes f g :: "'a \<Rightarrow> real"
  assumes int: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
    and gm: "g \<in> borel_measurable M"
    and eq: "AE x in M. f x = g x"
  shows "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  by (rule integrable_cong_AE_imp[OF int])
     (use gm in measurable, use eq in eventually_elim, simp)

end
