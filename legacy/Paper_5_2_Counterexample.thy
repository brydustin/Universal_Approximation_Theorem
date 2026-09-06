theory Paper_5_2_Counterexample
  imports Paper_Multivariate
begin

(* Audit of Theorem 5.2: a bounded Borel sigmoidal activation allowed by its hypotheses. *)
definition spike_activation :: "real \<Rightarrow> real" where
  "spike_activation t = (if t = 0 then 10 else if t < 0 then 0 else 1)"

(* Audit of Theorem 5.2: the exceptional value at zero does not change the sigmoidal limits. *)
lemma spike_activation_sigmoidal: "sigmoidal spike_activation"
proof -
  have bot: "(spike_activation \<longlongrightarrow> 0) at_bot"
    by (rule tendsto_eventually, subst eventually_at_bot_dense)
       (rule exI[where x=0], auto simp: spike_activation_def)
  have top: "(spike_activation \<longlongrightarrow> 1) at_top"
    by (rule tendsto_eventually, subst eventually_at_top_dense)
       (rule exI[where x=0], auto simp: spike_activation_def)
  show ?thesis unfolding sigmoidal_def using bot top by simp
qed

(* Audit of Theorem 5.2: boundedness and exact activation supremum. *)
lemma spike_activation_bounded: "bounded_function spike_activation"
  unfolding bounded_function_def
  by (rule bdd_aboveI[of _ 10]) (auto simp: spike_activation_def)

(* Audit of Theorem 5.2: the activation is measurable, so nonmeasurability is not the issue. *)
lemma spike_activation_measurable: "spike_activation \<in> borel_measurable borel"
  unfolding spike_activation_def by measurable

(* Audit of Theorem 5.2: its activation-norm parameter equals ten. *)
lemma spike_activation_sup:
  "Sup ((\<lambda>t. \<bar>spike_activation t\<bar>) ` UNIV) = 10"
proof (rule antisym)
  show "Sup ((\<lambda>t. \<bar>spike_activation t\<bar>) ` UNIV) \<le> 10"
    by (rule cSup_least) (auto simp: spike_activation_def)
  show "10 \<le> Sup ((\<lambda>t. \<bar>spike_activation t\<bar>) ` UNIV)"
    using cSUP_upper[OF UNIV_I, of "\<lambda>t. \<bar>spike_activation t\<bar>" 0]
      spike_activation_bounded unfolding bounded_function_def spike_activation_def by simp
qed

(* Auxiliary for the Theorem 5.2 counterexample: exact activation of a negative radial argument. *)
lemma spike_activation_negative_norm:
  fixes v :: "'a::real_normed_vector"
  assumes w: "0 < w"
  shows "spike_activation (-(w * norm v)) = (if v = 0 then 10 else 0)"
  using w unfolding spike_activation_def by auto

(* Auxiliary for the Theorem 5.2 counterexample: the three columns of its two-dimensional grid. *)
lemma bool_three_columns:
  "column_index True 3 =
    {(\<lambda>r. if r then undefined else 1), (\<lambda>r. if r then undefined else 2),
     (\<lambda>r. if r then undefined else 3)}"
proof -
  have mem: "\<And>k. k \<in> column_index True 3 \<longleftrightarrow> k True = undefined \<and> k False \<in> {1..3}"
    unfolding column_index_def PiE_def extensional_def by auto
  have rep: "\<And>k :: bool \<Rightarrow> nat. k True = undefined \<Longrightarrow> k = (\<lambda>r. if r then undefined else k False)"
    by (rule ext) auto
  show ?thesis
    unfolding set_eq_iff mem
    using rep by (auto simp: fun_eq_iff atLeastAtMostSuc_conv numeral_3_eq_3)
qed

(* Audit of Theorem 5.2: equation (5.1) has error 95/3 for every positive weight. *)
lemma paper_5_2_counterexample_error:
  assumes w: "0 < w"
  shows "\<bar>multivariate_network spike_activation (\<lambda>z :: (real,bool) vec. 10 * z$True)
      True (unif_part 0 1 3) 3 w (\<chi> r. 1/6) - 10 * (1/6)\<bar> = 95/3"
  using w
  unfolding multivariate_network_def bool_three_columns
  by (simp add: unif_part_def sample_point_def grid_point_def column_sign_def
      spike_activation_negative_norm vec_eq_iff atLeastAtMostSuc_conv numeral_3_eq_3
      fun_eq_iff all_bool_eq)

(* Audit of Theorem 5.2: the target is continuous on the paper's square. *)
lemma paper_5_2_target_continuous:
  "continuous_on {z :: (real,bool) vec. \<forall>r. z$r \<in> {0..1}} (\<lambda>z. 10*z$True)"
  by (intro continuous_intros)

(* Audit of Theorem 5.2: the target is Hoelder of order one with constant L = 10. *)
lemma paper_5_2_target_holder:
  fixes x y :: "(real,bool) vec"
  shows "\<bar>10*x$True - 10*y$True\<bar> \<le> 10 * norm (x-y) powr 1"
proof -
  have bd: "\<bar>(x-y)$True\<bar> \<le> norm (x-y)" by (rule component_le_norm_cart)
  have eq: "10*x$True - 10*y$True = 10*((x-y)$True)" by (simp add: algebra_simps)
  show ?thesis unfolding eq
    using mult_left_mono[OF bd, of 10] by (simp add: abs_mult)
qed

(* Audit of Theorem 5.2: the target's supremum norm equals ten. *)
lemma paper_5_2_target_sup:
  "Sup ((\<lambda>z :: (real,bool) vec. \<bar>10*z$True\<bar>) ` {z. \<forall>r. z$r \<in> {0..1}}) = 10"
proof (rule antisym)
  have ne: "{z :: (real,bool) vec. \<forall>r. z$r \<in> {0..1}} \<noteq> {}"
    by (auto intro!: exI[where x=0])
  have bd: "\<And>z :: (real,bool) vec. (\<forall>r. z$r \<in> {0..1}) \<Longrightarrow> \<bar>10*z$True\<bar> \<le> 10"
    by (auto simp: abs_mult)
  show "Sup ((\<lambda>z :: (real,bool) vec. \<bar>10*z$True\<bar>) ` {z. \<forall>r. z$r \<in> {0..1}}) \<le> 10"
    by (rule cSup_least) (use ne in simp, use bd in blast)
  have mem: "(10::real) \<in> (\<lambda>z :: (real,bool) vec. \<bar>10*z$True\<bar>) ` {z. \<forall>r. z$r \<in> {0..1}}"
    by (rule image_eqI[where x="\<chi> r. 1"]) auto
  have bdd: "bdd_above ((\<lambda>z :: (real,bool) vec. \<bar>10*z$True\<bar>) ` {z. \<forall>r. z$r \<in> {0..1}})"
    by (rule bdd_aboveI[of _ 10]) (use bd in blast)
  show "10 \<le> Sup ((\<lambda>z :: (real,bool) vec. \<bar>10*z$True\<bar>) ` {z. \<forall>r. z$r \<in> {0..1}})"
    by (rule cSup_upper[OF mem bdd])
qed

(* Audit of Theorem 5.2: the printed bound at alpha = 1, L = S = M = 10 is too small. *)
lemma paper_5_2_printed_bound_too_small:
  "(10 * (2::real) powr (1/2+1) + 2 powr (1/2) * 10 + 10) / 3 < 95/3"
proof -
  have rt: "sqrt (2::real) < 2"
    using real_sqrt_less_iff[of 2 4] by simp
  have eq: "(2::real) powr (1/2+1) = sqrt 2 * 2"
    by (simp only: powr_add, simp add: powr_half_sqrt)
  show ?thesis unfolding eq using rt by (simp add: powr_half_sqrt; linarith)
qed

(* Audit of Theorem 5.2: no positive weight can satisfy its printed uniform error bound. *)
theorem paper_5_2_counterexample:
  assumes w: "0 < w"
  shows "\<not> (\<forall>z :: (real,bool) vec. (\<forall>r. z$r \<in> {0..1}) \<longrightarrow>
    \<bar>multivariate_network spike_activation (\<lambda>z. 10*z$True) True (unif_part 0 1 3) 3 w z
       - 10*z$True\<bar> <
       (10 * (2::real) powr (1/2+1) + 2 powr (1/2) * 10 + 10) / 3)"
proof
  assume bd: "\<forall>z :: (real,bool) vec. (\<forall>r. z$r \<in> {0..1}) \<longrightarrow>
    \<bar>multivariate_network spike_activation (\<lambda>z. 10*z$True) True (unif_part 0 1 3) 3 w z
       - 10*z$True\<bar> <
       (10 * (2::real) powr (1/2+1) + 2 powr (1/2) * 10 + 10) / 3"
  have point: "\<forall>r. (\<chi> r. 1/6 :: (real,bool) vec)$r \<in> {0..1}" by simp
  note at_point = bd[rule_format, OF point[rule_format]]
  show False
    using at_point paper_5_2_counterexample_error[OF w] paper_5_2_printed_bound_too_small
    by (simp only: vec_lambda_beta; linarith)
qed

end
