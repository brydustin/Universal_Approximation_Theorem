section \<open>Constructive Approximation in \<open>L\<^sup>p\<close>\<close>

theory Lp_Approximation
  imports Universal_Approximation_1d Lp_Inequalities
begin

text \<open>
  This theory formalizes Section 3 of Costarelli and Spigler~\cite{CostarelliSpigler},
  which upgrades the uniform-norm Universal Approximation Theorem of theory
  Universal\_Approximation\_1d (Theorem 2.1 there) to an \<open>L\<^sup>p[a,b]\<close> approximation result
  (Theorem 3.1 in the paper).  The argument is exactly as trivial as the authors say: a
  function within \<open>\<eta>\<close> of \<open>f\<close> uniformly on \<open>[a,b]\<close> is within \<open>\<eta>(b-a)\<^sup>1\<^sup>/\<^sup>p\<close> of \<open>f\<close> in
  \<open>L\<^sup>p[a,b]\<close>.  (Theorem 3.2, the extension to \<open>f \<in> L\<^sup>p[a,b]\<close> not assumed continuous, is
  proved in \<^file>\<open>Lp_Approximation_General.thy\<close>, via density of the continuous functions
  in \<open>L\<^sup>p\<close> rather than via the paper's mollifiers.)

  We do \<open>not\<close> build on the AFP entry \<open>Lp\<close> (Gou\"ezel) here, even though it offers exactly
  the general quasinorm \<open>Norm (\<LL> p M)\<close> this section specializes: that entry's
  \<open>Functional_Spaces\<close> theory instantiates \<open>scaleR\<close> for function types in a way that
  Isabelle's class system cannot merge with \<open>Smooth_Manifolds\<close>'s own \<open>scaleR\<close> instantiation
  for function types (a hard "clash of specifications", not a design choice) -- and this
  project now needs \<open>Smooth_Manifolds\<close> transitively, via \<open>Real_and_Complex_Analytic\<close>'s
  higher-differentiability development used throughout \<^file>\<open>Sigmoid_Definition.thy\<close> onward.
  Since \<open>Lp_norm\<close> only ever needs the elementary Bochner-integral formula below (see
  \<open>Lp_norm_continuous_eq\<close>), not Minkowski/H\"older/completeness, this costs us nothing here.
\<close>

text \<open>
  The \<open>L\<^sup>p[a,b]\<close> norm, as in the paper: \<open>\<parallel>g\<parallel>\<^sub>L\<^sup>p\<^sub>[\<^sub>a\<^sub>,\<^sub>b\<^sub>] := (\<integral>\<^sub>a\<^sup>b |g(x)|\<^sup>p dx)\<^sup>1\<^sup>/\<^sup>p\<close>.  This is
  exactly the shape of \<open>lnorm\<close> in the AFP \<open>Fourier\<close> entry (theory Square\_Integrable,
  \<open>lnorm M p f \<equiv> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)\<close>), specialized to \<open>M = lebesgue_on {a..b}\<close>.
  We reuse \<open>Lp_norm\<close> for Theorems 5.3 and 5.4 later on, so it is worth naming.

  \<^bold>\<open>The integrability guard.\<close>  Isabelle's Bochner integral \<open>integral\<^sup>L\<close> is a total
  function which returns the junk value \<open>0\<close> on a non-integrable argument
  (\<open>not_integrable_integral_eq\<close>), and \<open>powr_0\<close> gives \<open>0 powr (1/p) = 0\<close>.  Defining
  \<open>Lp_norm\<close> by the integral alone would therefore make \<open>Lp_norm p a b g = 0 < \<epsilon>\<close> hold
  \<^emph>\<open>for every\<close> \<open>\<epsilon>>0\<close> whenever \<open>\<bar>g\<bar>\<^sup>p\<close> fails to be integrable -- so an \<open>L\<^sup>p\<close>-approximation
  statement could be satisfied for a reason having nothing to do with approximation.  This
  is not hypothetical: \<open>bounded_function\<close> and \<open>sigmoidal\<close> constrain only the sup norm and
  the two limits, so a bounded sigmoidal \<open>\<sigma>\<close> built from a non-measurable set is admissible
  and makes the network non-measurable; and even for measurable \<open>g\<close> the integral may
  diverge (\<open>\<integral>\<^sub>0\<^sup>1 1/x\<close>).

  We therefore guard the definition on integrability and return \<^const>\<open>undefined\<close>
  otherwise. This is only an internal real-valued working form: \<^const>\<open>undefined\<close>
  is an ordinary, unspecified real, not a domain check. An inequality about it does not
  establish integrability. Every use of this working form therefore carries an explicit
  integrability premise. Public approximation statements use \<open>Lp_enorm\<close>, which
  returns \<open>\<top>\<close> outside its measurable domain; a finite bound implies integrability
  by \<open>Lp_enorm_finite_integrable\<close>.

  \<open>Lp_norm\<close> is nonetheless \<^emph>\<open>not\<close> the object the paper's theorems are stated with:
  \<open>\<parallel>\<cdot>\<parallel>\<^sub>L\<^sup>p\<close> is \<open>[0,\<infinity>]\<close>-valued, assigning \<open>\<infinity>\<close> to a divergent integral rather than excluding
  it.  That object is \<open>Lp_enorm\<close> (\<^file>\<open>Lp_Inequalities.thy\<close>), and Theorems 3.1, 3.2, 5.3
  and 5.4 are stated with it.  \<open>Lp_norm\<close> remains as the \<^typ>\<open>real\<close>-valued working
  form in which the H\"older and Minkowski estimates are carried out, linked to
  \<open>Lp_enorm\<close> by \<open>Lp_enorm_eq_Lp_norm\<close> below.
\<close>
definition Lp_norm :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "Lp_norm p a b g =
     (if integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>g x\<bar> powr p)
      then (\<integral>x. \<bar>g x\<bar> powr p \<partial>(lebesgue_on {a..b})) powr (1 / p)
      else undefined)"

text \<open>
  The computation rule for \<^const>\<open>Lp_norm\<close>: on integrable arguments it is the integral
  formula, exactly as before the guard was added.  Every former \<open>unfolding Lp_norm_def\<close>
  becomes an appeal to this lemma, discharging integrability at that point.
\<close>
(* Auxiliary for Theorem 3.1; not separately numbered. *)
lemma Lp_norm_integrable_eq:
  fixes g :: "real \<Rightarrow> real"
  assumes g_int: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "Lp_norm p a b g = (\<integral>x. \<bar>g x\<bar> powr p \<partial>(lebesgue_on {a..b})) powr (1 / p)"
  using g_int unfolding Lp_norm_def by simp

text \<open>
  For a continuous \<open>g\<close>, \<open>Lp_norm\<close> agrees with the elementary Henstock--Kurzweil-integral
  formula already used in theory Universal\_Approximation\_1d.  This is the only place we
  touch the measure-theoretic machinery; every other proof in this theory works with the
  ordinary \<open>integral\<close>.
\<close>
(* Auxiliary for Theorem 3.1; not separately numbered. *)
lemma Lp_norm_continuous_eq:
  fixes g :: "real \<Rightarrow> real"
  assumes cont_g: "continuous_on {a..b} g"
  assumes p_pos: "p > (0::real)"
  shows "Lp_norm p a b g = (integral {a..b} (\<lambda>x. \<bar>g x\<bar> powr p)) powr (1 / p)"
proof -
  (* {a..b} is closed, hence Borel, hence Lebesgue measurable. *)
  have S_meas: "{a..b} \<in> sets lebesgue"
    by (intro sets_completionI_sets, simp)

  (* Likewise |g|^p is continuous, using p > 0 to handle the point(s) where g vanishes. *)
  have powr_continuous: "continuous_on {a..b} (\<lambda>x. \<bar>g x\<bar> powr p)"
  proof (rule continuous_on_powr')
    show "continuous_on {a..b} (\<lambda>x. \<bar>g x\<bar>)"
      using cont_g by (intro continuous_intros)
    show "continuous_on {a..b} (\<lambda>x. p)"
      by (rule continuous_on_const)
    show "\<forall>x\<in>{a..b}. \<bar>g x\<bar> \<ge> 0 \<and> (\<bar>g x\<bar> = 0 \<longrightarrow> p > 0)"
      using p_pos by simp
  qed
  have powr_integrable: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>g x\<bar> powr p)"
    using continuous_imp_integrable_real[OF powr_continuous] .

  (* Bridge: the Bochner integral over lebesgue_on {a..b} is the Henstock-Kurzweil integral. *)
  have bochner_eq_HK: "(\<integral>x. \<bar>g x\<bar> powr p \<partial>(lebesgue_on {a..b})) = integral {a..b} (\<lambda>x. \<bar>g x\<bar> powr p)"
    using lebesgue_integral_eq_integral[OF powr_integrable S_meas] .

  show ?thesis
    unfolding Lp_norm_integrable_eq[OF powr_integrable] bochner_eq_HK by (rule refl)
qed

text \<open>
  Each summand of the network is \<open>\<sigma>\<close> composed with the affine map \<open>x \<mapsto> w(x-t)\<close>, which is
  continuous; so a \<^emph>\<open>measurable\<close> \<open>\<sigma>\<close> already makes every summand measurable.  This is what
  replaces the appeal to continuity of \<open>\<sigma>\<close> in Theorems 3.1 and 3.2: what the \<open>L\<^sup>p\<close> norm
  needs of the network is measurability, and nothing more.
\<close>
(* Auxiliary for Theorem 3.1; not separately numbered. *)
lemma sigma_shift_measurable:
  fixes \<sigma> :: "real \<Rightarrow> real" and w t :: real
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  shows "(\<lambda>x::real. \<sigma> (w * (x - t))) \<in> borel_measurable borel"
proof -
  have affine: "(\<lambda>x::real. w * (x - t)) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show ?thesis using measurable_compose[OF affine meas_sigmoidal] .
qed

text \<open>
  The real-valued form of Theorem 3.1.  This is an \<^emph>\<open>internal\<close> stepping stone: the paper's
  \<open>\<parallel>G\<^sub>N - f\<parallel>\<^sub>L\<^sup>p\<close> is the \<open>[0,\<infinity>]\<close>-valued norm, so the theorem as the paper states it is
  \<open>sigmoidal_Lp_approximation_theorem\<close> below, in terms of \<^const>\<open>Lp_enorm\<close>.  The two
  differ only by the bridge \<open>Lp_enorm_eq_Lp_norm\<close>; this form is kept because Theorem 3.2's
  proof, and the Minkowski estimates it runs on, work in \<^typ>\<open>real\<close>.
\<close>
(* Auxiliary for Theorem 3.1; not separately numbered. *)
lemma sigmoidal_Lp_approximation_real:
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  assumes a_lt_b: "a < b"
  assumes contin_f: "continuous_on {a..b} f"
  assumes p_geq_1: "p \<ge> (1::real)"
  assumes eps_pos: "0 < \<epsilon>"
  defines "xs N \<equiv> unif_part a b N"
  shows "\<exists>N::nat. \<exists>(w::real) > 0. (N > 0) \<and>
           integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>
               (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x\<bar> powr p) \<and>
           Lp_norm p a b (\<lambda>x.
               (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x) < \<epsilon>"
(* High-level plan (mirroring the one-line proof of Theorem 3.1 in the paper):
   1) Let \<eta> := (\<epsilon>/2) / (b-a) powr (1/p).
   2) Invoke the uniform-norm theorem with tolerance \<eta> to get N, w with
      |G_Nf(x) - f(x)| < \<eta> for every x \<in> [a,b].
   3) G_Nf is continuous (\<sigma> is continuous by assumption), hence so is
      x \<mapsto> |G_Nf(x)-f(x)|^p, hence Lp_norm agrees with the Henstock-Kurzweil integral formula
      (Lp_norm_continuous_eq), which is integrable on the compact interval [a,b].
   4) Bound the integral by the constant \<eta>^p, take the p-th root, and simplify:
      (\<eta>^p (b-a)) powr (1/p) = \<eta> (b-a) powr (1/p) = \<epsilon>/2 < \<epsilon>. *)
proof -
  obtain \<epsilon>' where \<epsilon>'_def: "\<epsilon>' = \<epsilon> / 2"
    by blast
  have \<epsilon>'_pos: "\<epsilon>' > 0"
    using \<epsilon>'_def eps_pos by simp

  (* b - a > 0, so (b-a) powr (1/p) > 0, and hence \<eta> is well-defined and positive. *)
  have b_minus_a_pos: "b - a > 0"
    using a_lt_b by simp
  have b_minus_a_powr_pos: "(b - a) powr (1 / p) > 0"
    using b_minus_a_pos by simp

  obtain \<eta> where \<eta>_def: "\<eta> = \<epsilon>' / (b - a) powr (1 / p)"
    by blast
  have \<eta>_pos: "\<eta> > 0"
    unfolding \<eta>_def using \<epsilon>'_pos b_minus_a_powr_pos by simp

  (* Step 2: apply the uniform-norm Universal Approximation Theorem with tolerance \<eta>. *)
  from sigmoidal_approximation_theorem
       [OF sigmoidal_function bounded_sigmoidal a_lt_b contin_f \<eta>_pos]
  obtain N w where N_pos: "N > 0" and w_pos: "w > 0"
    and sup_bound: "\<forall>x\<in>{a..b}.
         \<bar>(\<Sum>k\<in>{2..N+1}. (f (unif_part a b N ! k) - f (unif_part a b N ! (k - 1)))
                          * \<sigma> (w * (x - unif_part a b N ! k)))
          + f a * \<sigma> (w * (x - unif_part a b N ! 0)) - f x\<bar> < \<eta>"
    by blast

  (* Package the network as G_Nf, matching (2.2), to keep the rest of the proof legible. *)
  obtain G_Nf where G_Nf_def: "G_Nf \<equiv> (\<lambda>x.
       (\<Sum>k\<in>{2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
       + f a * \<sigma> (w * (x - xs N ! 0)))"
    by blast
  have sup_bound': "\<forall>x\<in>{a..b}. \<bar>G_Nf x - f x\<bar> < \<eta>"
    unfolding G_Nf_def xs_def using sup_bound by blast

  (* Step 3: G_Nf is Borel measurable.  Continuity of \<sigma> is NOT needed: what the L^p norm
     asks of the network is measurability, and \<sigma> measurable suffices, because the rest of
     each summand -- the affine map x \<mapsto> w(x - t) -- is continuous. *)
  have G_Nf_measurable: "G_Nf \<in> borel_measurable borel"
    unfolding G_Nf_def using sigma_shift_measurable[OF meas_sigmoidal] by measurable

  (* The interval and its measure-theoretic facts, mirroring Theorem 5.3's setup. *)
  have ab_lborel: "{a..b} \<in> sets lborel" by simp
  have ab_lebesgue: "{a..b} \<in> sets lebesgue"
    using ab_lborel by (intro sets_completionI_sets)
  have ab_lmeasurable: "{a..b} \<in> lmeasurable"
    by (metis cbox_interval lmeasurable_cbox)
  have ab_finite: "finite_measure (lebesgue_on {a..b})"
    using finite_measure_lebesgue_on[OF ab_lmeasurable] .

  have G_meas_ab: "G_Nf \<in> borel_measurable (lebesgue_on {a..b})"
    by (rule borel_measurable_lebesgue_onI[OF G_Nf_measurable])
  have f_meas_ab: "f \<in> borel_measurable (lebesgue_on {a..b})"
    using continuous_imp_measurable_on_sets_lebesgue[OF contin_f ab_lebesgue] .
  have integrand_measurable:
      "(\<lambda>x. \<bar>G_Nf x - f x\<bar> powr p) \<in> borel_measurable (lebesgue_on {a..b})"
    using G_meas_ab f_meas_ab by measurable

  (* Step 4: the uniform bound yields integrability and the L^p estimate together. *)
  have pointwise_bound_ae:
      "AE x in (lebesgue_on {a..b}). \<bar>G_Nf x - f x\<bar> powr p \<le> \<eta> powr p"
  proof (rule AE_I2)
    fix x assume "x \<in> space (lebesgue_on {a..b})"
    then have x_in_ab: "x \<in> {a..b}" by (simp add: space_restrict_space)
    have "\<bar>G_Nf x - f x\<bar> \<le> \<eta>" using sup_bound' x_in_ab by force
    then show "\<bar>G_Nf x - f x\<bar> powr p \<le> \<eta> powr p"
      using p_geq_1 powr_mono2 by auto
  qed

  have integrand_integrable:
      "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>G_Nf x - f x\<bar> powr p)"
  proof (rule finite_measure.integrable_const_bound[OF ab_finite, where B = "\<eta> powr p"])
    show "AE x in (lebesgue_on {a..b}). norm (\<bar>G_Nf x - f x\<bar> powr p) \<le> \<eta> powr p"
      using pointwise_bound_ae by simp
    show "(\<lambda>x. \<bar>G_Nf x - f x\<bar> powr p) \<in> borel_measurable (lebesgue_on {a..b})"
      using integrand_measurable .
  qed

  have const_integrable: "integrable (lebesgue_on {a..b}) (\<lambda>x::real. \<eta> powr p)"
    using finite_measure.integrable_const[OF ab_finite] .

  have integral_le_const:
      "(\<integral>x. \<bar>G_Nf x - f x\<bar> powr p \<partial>(lebesgue_on {a..b}))
         \<le> (\<integral>x. \<eta> powr p \<partial>(lebesgue_on {a..b}))"
    using integral_mono_AE[OF integrand_integrable const_integrable pointwise_bound_ae] .

  have measure_ab_eq: "measure (lebesgue_on {a..b}) {a..b} = measure lborel {a..b}"
  proof -
    have "measure (lebesgue_on {a..b}) {a..b} = measure (completion lborel) {a..b}"
      using measure_restrict_space[of "{a..b}" "completion lborel" "{a..b}"] ab_lebesgue
      by simp
    also have "\<dots> = measure lborel {a..b}" using measure_completion[OF ab_lborel] .
    finally show ?thesis by simp
  qed

  have integral_const_val:
      "(\<integral>x. \<eta> powr p \<partial>(lebesgue_on {a..b})) = (b - a) * \<eta> powr p"
    using measure_ab_eq a_lt_b by simp

  have integral_nonneg_le:
      "0 \<le> (\<integral>x. \<bar>G_Nf x - f x\<bar> powr p \<partial>(lebesgue_on {a..b}))"
    by (rule Bochner_Integration.integral_nonneg) simp

  have Lp_norm_le: "Lp_norm p a b (\<lambda>x. G_Nf x - f x) \<le> ((b - a) * \<eta> powr p) powr (1 / p)"
  proof -
    have "Lp_norm p a b (\<lambda>x. G_Nf x - f x)
        = (\<integral>x. \<bar>G_Nf x - f x\<bar> powr p \<partial>(lebesgue_on {a..b})) powr (1 / p)"
      by (rule Lp_norm_integrable_eq[OF integrand_integrable])
    also have "\<dots> \<le> ((b - a) * \<eta> powr p) powr (1 / p)"
      by (rule powr_mono2,
          use p_geq_1 integral_nonneg_le integral_le_const integral_const_val in auto)
    finally show ?thesis .
  qed


  (* Simplify ((b-a) \<eta>^p)^(1/p) = (b-a)^(1/p) \<eta>. *)
  have simplify_rhs: "((b - a) * \<eta> powr p) powr (1 / p) = (b - a) powr (1 / p) * \<eta>"
  proof -
    have "((b - a) * \<eta> powr p) powr (1 / p) = (b - a) powr (1 / p) * (\<eta> powr p) powr (1 / p)"
      using b_minus_a_pos \<eta>_pos by (simp add: powr_mult)
    also have "(\<eta> powr p) powr (1 / p) = \<eta> powr (p * (1 / p))"
      by (rule powr_powr)
    also have "p * (1 / p) = 1"
      using p_geq_1 by simp
    also have "\<eta> powr 1 = \<eta>"
      using \<eta>_pos by simp
    finally show ?thesis
      by simp
  qed

  have final_eq: "(b - a) powr (1 / p) * \<eta> = \<epsilon>'"
    unfolding \<eta>_def using b_minus_a_powr_pos by simp

  have "Lp_norm p a b (\<lambda>x. G_Nf x - f x) \<le> \<epsilon>'"
    using Lp_norm_le simplify_rhs final_eq by simp
  also have "\<epsilon>' < \<epsilon>"
    using \<epsilon>'_def eps_pos by simp
  finally have Lp_bound: "Lp_norm p a b (\<lambda>x. G_Nf x - f x) < \<epsilon>".

  show ?thesis
  proof (intro exI[where x=N] exI[where x=w] conjI)
    show "w > 0" by (rule w_pos)
    show "N > 0" by (rule N_pos)
    show "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>
               (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x\<bar> powr p)"
      using integrand_integrable unfolding G_Nf_def by simp
    show "Lp_norm p a b (\<lambda>x.
               (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x) < \<epsilon>"
      using Lp_bound unfolding G_Nf_def by simp
  qed
qed

subsection \<open>Theorem 3.1 in the extended reals\<close>

text \<open>
  \<^const>\<open>Lp_norm\<close> is \<^typ>\<open>real\<close>-valued and so must exclude a divergent integral outright.
  \<^const>\<open>Lp_enorm\<close> (\<^file>\<open>Lp_Inequalities.thy\<close>) is the \<open>[0,\<infinity>]\<close>-valued object of the textbook
  definition, which assigns \<open>\<infinity>\<close> there instead.  The two agree on integrable arguments, so
  the \<open>L\<^sup>p\<close> theorems can be stated in the extended reals -- their proper home -- while the
  H\"older and Minkowski estimates that drive the proofs stay in \<^typ>\<open>real\<close>, where they
  are used only with integrability already in hand.
\<close>

(* Auxiliary for Theorem 3.1; not separately numbered. *)
lemma Lp_enorm_eq_Lp_norm:
  fixes h :: "real \<Rightarrow> real"
  assumes h_int: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>h x\<bar> powr p)"
  shows "Lp_enorm p (lebesgue_on {a..b}) h = ennreal (Lp_norm p a b h)"
  unfolding Lp_enorm_eq_seminorm[OF h_int] Lp_seminorm_def
            Lp_norm_integrable_eq[OF h_int]
  by (rule refl)

text \<open>Continuity on the compact interval gives the integrability the bridge needs.\<close>

(* Auxiliary for Theorem 3.1; not separately numbered. *)
lemma continuous_imp_powr_integrable:
  fixes h :: "real \<Rightarrow> real"
  assumes cont_h: "continuous_on {a..b} h" and p_pos: "0 < p"
  shows "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>h x\<bar> powr p)"
proof -
  have "continuous_on {a..b} (\<lambda>x. \<bar>h x\<bar> powr p)"
  proof (rule continuous_on_powr')
    show "continuous_on {a..b} (\<lambda>x. \<bar>h x\<bar>)" using cont_h by (intro continuous_intros)
    show "continuous_on {a..b} (\<lambda>x. p)" by (rule continuous_on_const)
    show "\<forall>x\<in>{a..b}. \<bar>h x\<bar> \<ge> 0 \<and> (\<bar>h x\<bar> = 0 \<longrightarrow> p > 0)" using p_pos by simp
  qed
  from continuous_imp_integrable_real[OF this] show ?thesis .
qed

(* Theorem 3.1: Lp approximation of continuous targets; measurable activation. *)
theorem sigmoidal_Lp_approximation_theorem:
  fixes f :: "real \<Rightarrow> real" and p \<epsilon> :: real
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  assumes a_lt_b: "a < b"
  assumes contin_f: "continuous_on {a..b} f"
  assumes p_geq_1: "p \<ge> (1::real)"
  assumes eps_pos: "0 < \<epsilon>"
  defines "xs N \<equiv> unif_part a b N"
  shows "\<exists>N::nat. \<exists>(w::real) > 0. (N > 0) \<and>
           Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x.
               (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x) < ennreal \<epsilon>"
proof -
  have p_pos: "0 < p" using p_geq_1 by simp
  \<comment> \<open>the real-valued form supplies the integrability of the integrand along with the
      estimate, which is exactly what the bridge to \<open>Lp_enorm\<close> needs; deriving it from
      continuity of the network is no longer possible, nor necessary\<close>
  obtain N w where w_pos: "w > 0" and N_pos: "N > 0"
    and int_diff: "integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>
           (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                          + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x\<bar> powr p)"
    and bound: "Lp_norm p a b (\<lambda>x.
           (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                          + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x) < \<epsilon>"
    using sigmoidal_Lp_approximation_real[OF sigmoidal_function bounded_sigmoidal
            meas_sigmoidal a_lt_b contin_f p_geq_1 eps_pos]
    unfolding xs_def by blast

  show ?thesis
  proof (intro exI[where x=N] exI[where x=w] conjI)
    show "w > 0" by (rule w_pos)
    show "N > 0" by (rule N_pos)
    show "Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x.
             (\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                            + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x) < ennreal \<epsilon>"
      unfolding Lp_enorm_eq_Lp_norm[OF int_diff]
      by (rule ennreal_lessI[OF eps_pos bound])
  qed
qed

end
