section \<open>Applications to Specific Sigmoidal Functions\<close>

theory Concrete_Sigmoidal_Examples
  imports Universal_Approximation_1d Simultaneous_Approximation Lp_Approximation Simultaneous_Approximation_General_j
begin

text \<open>
  This theory formalizes the first part of Section 6 of Costarelli and Spigler
  ~\cite{CostarelliSpigler}, Corollary 6.1: the logistic function \<open>\<sigma>(x)=(1+e\<^sup>-\<^sup>x)\<^sup>-\<^sup>1\<close> is
  exactly the \<open>sigmoid\<close> already fixed throughout this whole development
  (theory \<open>Sigmoid_Definition\<close>, \<open>sigmoid x = exp x / (1 + exp x) = inverse (1 + exp(-x))\<close> by
  \<open>sigmoid_alt_def\<close>), so Theorem 2.1 applies to it directly once it is shown to be a bounded
  sigmoidal function -- \<open>sigmoidal\<close> is already available (\<open>sigmoid_is_sigmoidal\<close>, theory
  \<open>Asymptotic_Qualitative_Properties\<close>); only boundedness remains, immediate from
  \<open>sigmoid_range\<close> (\<open>0 < sigmoid x < 1\<close> for every \<open>x\<close>).
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma sigmoid_is_bounded_function: "bounded_function sigmoid"
  unfolding bounded_function_def
proof (intro bdd_aboveI)
  fix y assume "y \<in> range (\<lambda>x. \<bar>sigmoid x\<bar>)"
  then obtain x where y_def: "y = \<bar>sigmoid x\<bar>"
    by blast
  show "y \<le> 1"
    unfolding y_def using sigmoid_range[of x] by simp
qed

text \<open>
  Corollary 6.1, part (i): specializing \<open>sigmoidal_approximation_theorem\<close> (Theorem 2.1) to
  \<open>\<sigma> = sigmoid\<close> gives the paper's own concrete uniform-approximation statement for the
  logistic-function network \<open>G_Nf\<close>, with no further hypotheses on \<open>\<sigma>\<close> to discharge.
\<close>
(* Corollary 6.1(i): existence-only specialization; prescribed weight is not asserted here. *)
corollary logistic_approximation_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b"
  assumes contin_f: "continuous_on {a..b} f"
  assumes eps_pos: "0 < \<epsilon>"
  defines "xs N \<equiv> unif_part a b N"
  shows "\<exists>N::nat. \<exists>(w::real) > 0. (N > 0) \<and>
           (\<forall>x \<in> {a..b}.
               \<bar>(\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * sigmoid(w * (x - xs N ! k)))
                              + f(a) * sigmoid(w * (x - xs N ! 0)) - f x\<bar> < \<epsilon>)"
  unfolding xs_def
  by (rule sigmoidal_approximation_theorem[OF sigmoid_is_sigmoidal sigmoid_is_bounded_function
        a_lt_b contin_f eps_pos])

text \<open>
  Corollary 6.1, part (ii): the simultaneous-derivative analogue, specializing
  \<open>forward_diff_one_approximation\<close> (Theorem 4.1, \<open>j=1\<close> case, theory
  \<open>Simultaneous_Approximation\<close> -- now fully assembled) to \<open>\<sigma>=sigmoid\<close>. Unlike part (i), this
  needs \<open>f\<in>C^2\<close> (\<open>C_k_on 2 f U\<close>), matching the paper's own \<open>f\<in>C_b^{n+1}[a,b]\<close> hypothesis for
  \<open>n=1\<close>.
\<close>
(* Corollary 6.1(ii): first-derivative, existence-only specialization. *)
corollary logistic_approximation_theorem_derivative:
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>N w. N > 3 \<and> w > 0 \<and>
           (\<forall>x \<in> {a..b}. \<bar>Gj_network sigmoid f (unif_part a b N) ((b - a) / real N) N 1 w x
                          - deriv f x\<bar> < \<epsilon>)"
  by (rule forward_diff_one_approximation[OF sigmoid_is_sigmoidal sigmoid_is_bounded_function
        a_lt_b Ck ab_subset eps_pos])

text \<open>
  Before Corollary 6.1 the paper isolates a sharper, fully explicit form of the generic
  saturation lemma (\<open>sigmoidal_uniform_approximation\<close>, theory
  \<open>Asymptotic_Qualitative_Properties\<close>) specific to the logistic function: for \<open>N>2\<close> the
  threshold \<open>\<omega>\<close> that lemma only asserts \<^emph>\<open>exists\<close> can be written down explicitly, as
  \<open>\<omega> = (1/h)\<sqdot>ln(N-1)\<close>, and the saturation error is exactly \<open>1/N\<close> rather than an arbitrary
  \<open>\<epsilon>\<close>. This is the fact used (with a fixed \<open>N\<close>, not an \<open>\<epsilon>\<close>-driven one) to write down the
  concrete network in Corollary 6.1. Both directions reduce to the same algebra: for
  \<open>t>ln(N-1)\<close>, \<open>e\<^sup>-\<^sup>t<1/(N-1)\<close>, and \<open>1-\<sigma>(t) = e\<^sup>-\<^sup>t/(1+e\<^sup>-\<^sup>t) < 1/N\<close> exactly when
  \<open>(N-1)e\<^sup>-\<^sup>t<1\<close>, which is the same inequality; the lower-tail case is the mirror image via
  \<open>\<sigma>(-t) = 1-\<sigma>(t)\<close> (\<open>sigmoid_symmetry\<close>).
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma sigmoid_saturation_upper:
  fixes t :: real and N :: nat
  assumes N_gt: "N > 2"
  assumes t_gt: "t > ln (real N - 1)"
  shows "\<bar>sigmoid t - 1\<bar> < 1 / real N"
proof -
  have N1_pos: "real N - 1 > 0"
    using N_gt by simp
  have et_lt: "exp (- t) < 1 / (real N - 1)"
  proof -
    have "exp (- t) < exp (- ln (real N - 1))"
      using t_gt by simp
    also have "exp (- ln (real N - 1)) = 1 / (real N - 1)"
      using N1_pos by (simp add: exp_minus exp_ln inverse_eq_divide)
    finally show ?thesis .
  qed
  have one_minus: "1 - sigmoid t = exp (- t) / (1 + exp (- t))"
  proof -
    have pos: "(0::real) < 1 + exp (- t)"
      using exp_gt_zero[of "- t"] by linarith
    show ?thesis
      unfolding sigmoid_alt_def inverse_eq_divide
      using pos by (simp add: divide_simps)
  qed
  have abs_eq: "\<bar>sigmoid t - 1\<bar> = exp (- t) / (1 + exp (- t))"
    using one_minus sigmoid_less_1[of t] by simp
  have cross: "exp (- t) / (1 + exp (- t)) < 1 / real N \<longleftrightarrow> (real N - 1) * exp (- t) < 1"
  proof -
    have pos1: "1 + exp (- t) > 0"
      using exp_gt_zero[of "- t"] by linarith
    have pos2: "real N > 0"
      using N_gt by simp
    show ?thesis
      using pos1 pos2 by (simp add: field_simps)
  qed
  have "(real N - 1) * exp (- t) < 1"
    using et_lt N1_pos by (simp add: field_simps)
  then show ?thesis
    unfolding abs_eq using cross by simp
qed

(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma sigmoid_saturation_lower:
  fixes t :: real and N :: nat
  assumes N_gt: "N > 2"
  assumes t_gt: "t > ln (real N - 1)"
  shows "\<bar>sigmoid (- t)\<bar> < 1 / real N"
proof -
  have "sigmoid (- t) = 1 - sigmoid t"
    by (rule sigmoid_symmetry)
  then have "\<bar>sigmoid (- t)\<bar> = \<bar>sigmoid t - 1\<bar>"
    by simp
  then show ?thesis
    using sigmoid_saturation_upper[OF N_gt t_gt] by simp
qed

text \<open>
  Bundling both directions with the paper's own explicit threshold
  \<open>\<omega> := (1/h)\<sqdot>ln(N-1)\<close> (for a mesh width \<open>h>0\<close> and node \<open>x_k\<close>): this is the concrete,
  \<open>N\<close>-driven counterpart of \<open>sigmoidal_uniform_approximation_dist\<close> used implicitly in
  Corollary 6.1's statement of \<open>G_Nf\<close> with the specific weight \<open>w \<ge> (N/(b-a))\<sqdot>ln(N-1)\<close>.
\<close>
(* Section 6: explicit logistic threshold preceding Corollary 6.1 (unnumbered). *)
lemma logistic_step_saturation:
  fixes h w xk x :: real and N :: nat
  assumes N_gt: "N > 2" and h_pos: "h > 0"
  assumes w_gt: "w > (1 / h) * ln (real N - 1)"
  shows "x - xk \<ge> h \<Longrightarrow> \<bar>sigmoid (w * (x - xk)) - 1\<bar> < 1 / real N"
    and "x - xk \<le> - h \<Longrightarrow> \<bar>sigmoid (w * (x - xk))\<bar> < 1 / real N"
proof -
  have N1_pos: "real N - 1 > 1"
    using N_gt by simp
  have ln_pos: "ln (real N - 1) > 0"
    using N1_pos by simp
  have wh_gt: "w * h > ln (real N - 1)"
    using w_gt h_pos by (simp add: field_simps)
  have w_pos: "w > 0"
  proof -
    have "(1 / h) * ln (real N - 1) > 0"
      using h_pos ln_pos by simp
    then show ?thesis
      using w_gt by linarith
  qed
  {
    assume "x - xk \<ge> h"
    then have "w * (x - xk) \<ge> w * h"
      using w_pos by (intro mult_left_mono) auto
    then have "w * (x - xk) > ln (real N - 1)"
      using wh_gt by simp
    then show "\<bar>sigmoid (w * (x - xk)) - 1\<bar> < 1 / real N"
      using sigmoid_saturation_upper[OF N_gt] by simp
  }
  {
    assume "x - xk \<le> - h"
    then have "- (x - xk) \<ge> h"
      by simp
    then have "w * (- (x - xk)) \<ge> w * h"
      using w_pos by (intro mult_left_mono) auto
    then have t_gt: "w * (- (x - xk)) > ln (real N - 1)"
      using wh_gt by simp
    have lower: "\<bar>sigmoid (- (w * (- (x - xk))))\<bar> < 1 / real N"
      using sigmoid_saturation_lower[OF N_gt t_gt] .
    have arg_eq: "- (w * (- (x - xk))) = w * (x - xk)"
    proof -
      have "w * (- (x - xk)) = w * xk - w * x"
        by (simp add: right_diff_distrib)
      moreover have "w * (x - xk) = w * x - w * xk"
        by (simp add: right_diff_distrib)
      ultimately show ?thesis
        by simp
    qed
    show "\<bar>sigmoid (w * (x - xk))\<bar> < 1 / real N"
      using lower unfolding arg_eq .
  }
qed

text \<open>
  The second family of Section 6, the Gompertz sigmoids (6.1), \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x)=e\<^sup>-\<^sup>\<alpha>\<^sup>e\<^sup>-\<^sup>\<beta>\<^sup>x\<close> for
  \<open>\<alpha>,\<beta>>0\<close>: unlike \<open>sigmoid\<close>, this is genuinely new work (the project never fixed a Gompertz
  function anywhere), so both \<open>sigmoidal\<close> and boundedness are proved from scratch here.
\<close>
(* Equation (6.1): Gompertz sigmoidal function. *)
definition sigmoid_gompertz :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "sigmoid_gompertz \<alpha> \<beta> x = exp (- \<alpha> * exp (- \<beta> * x))"

text \<open>
  \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x) \<longrightarrow> 1\<close> as \<open>x \<longrightarrow> \<infinity>\<close>: \<open>-\<beta>x \<longrightarrow> -\<infinity>\<close> (since \<open>\<beta>>0\<close>), so \<open>e\<^sup>-\<^sup>\<beta>\<^sup>x \<longrightarrow> 0\<close>
  (\<open>exp_at_bot\<close>), so \<open>-\<alpha> e\<^sup>-\<^sup>\<beta>\<^sup>x \<longrightarrow> 0\<close>, so \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x)=exp(\<dots>) \<longrightarrow> exp 0 = 1\<close>.
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_tendsto_1_at_top:
  fixes \<alpha> \<beta> :: real
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0"
  shows "(sigmoid_gompertz \<alpha> \<beta> \<longlongrightarrow> 1) at_top"
proof -
  have h1: "filterlim (\<lambda>x::real. x) at_top at_top"
    by (rule filterlim_ident)
  have h2: "filterlim (\<lambda>x::real. - \<beta> * x) at_bot at_top"
    using filterlim_cmult_at_bot_at_top[OF h1, of "- \<beta>" at_bot] \<beta>_pos by simp
  have h3: "((\<lambda>x. exp (- \<beta> * x)) \<longlongrightarrow> 0) at_top"
    using filterlim_compose[OF exp_at_bot h2] .
  have h4: "((\<lambda>x. - \<alpha> * exp (- \<beta> * x)) \<longlongrightarrow> - \<alpha> * 0) at_top"
    by (rule tendsto_mult_left[OF h3])
  then have h4': "((\<lambda>x. - \<alpha> * exp (- \<beta> * x)) \<longlongrightarrow> 0) at_top"
    by simp
  have "((\<lambda>x. exp (- \<alpha> * exp (- \<beta> * x))) \<longlongrightarrow> exp 0) at_top"
    by (rule tendsto_exp[OF h4'])
  then show ?thesis
    unfolding sigmoid_gompertz_def by simp
qed

text \<open>
  \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x) \<longrightarrow> 0\<close> as \<open>x \<longrightarrow> -\<infinity>\<close>: \<open>-\<beta>x \<longrightarrow> \<infinity>\<close>, so \<open>e\<^sup>-\<^sup>\<beta>\<^sup>x \<longrightarrow> \<infinity>\<close> (\<open>exp_at_top\<close>), so
  \<open>-\<alpha> e\<^sup>-\<^sup>\<beta>\<^sup>x \<longrightarrow> -\<infinity>\<close>, so \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x)=exp(\<dots>) \<longrightarrow> 0\<close> (\<open>exp_at_bot\<close> again, one level up).
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_tendsto_0_at_bot:
  fixes \<alpha> \<beta> :: real
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0"
  shows "(sigmoid_gompertz \<alpha> \<beta> \<longlongrightarrow> 0) at_bot"
proof -
  have h1: "filterlim (\<lambda>x::real. - x) at_top at_bot"
    by (rule filterlim_uminus_at_top_at_bot)
  have h2: "filterlim (\<lambda>x::real. \<beta> * (- x)) at_top at_bot"
    using filterlim_cmult_at_bot_at_top[OF h1, of \<beta> at_top] \<beta>_pos by simp
  have h2': "filterlim (\<lambda>x::real. - \<beta> * x) at_top at_bot"
    using h2 by (simp add: mult.commute)
  have h3: "filterlim (\<lambda>x. exp (- \<beta> * x)) at_top at_bot"
    using filterlim_compose[OF exp_at_top h2'] .
  have h4: "filterlim (\<lambda>x. - \<alpha> * exp (- \<beta> * x)) at_bot at_bot"
    using filterlim_tendsto_neg_mult_at_bot[of "\<lambda>x. - \<alpha>" "- \<alpha>" at_bot "\<lambda>x. exp (- \<beta> * x)"]
          \<alpha>_pos h3 by simp
  have "((\<lambda>x. exp (- \<alpha> * exp (- \<beta> * x))) \<longlongrightarrow> 0) at_bot"
    using filterlim_compose[OF exp_at_bot h4] .
  then show ?thesis
    unfolding sigmoid_gompertz_def by simp
qed

(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_is_sigmoidal:
  assumes "\<alpha> > 0" and "\<beta> > 0"
  shows "sigmoidal (sigmoid_gompertz \<alpha> \<beta>)"
  unfolding sigmoidal_def
  using gompertz_tendsto_1_at_top[OF assms] gompertz_tendsto_0_at_bot[OF assms] by blast

text \<open>
  \<open>0 < \<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x) < 1\<close> for every \<open>x\<close>, exactly as for \<open>sigmoid\<close> (\<open>sigmoid_range\<close>): \<open>exp\<close> is always
  positive, and \<open>-\<alpha> e\<^sup>-\<^sup>\<beta>\<^sup>x < 0\<close> since \<open>\<alpha> > 0\<close> and \<open>e\<^sup>-\<^sup>\<beta>\<^sup>x > 0\<close>, so \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(x) = exp(\<dots>) < exp 0 = 1\<close>.
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_range:
  assumes "\<alpha> > 0"
  shows "0 < sigmoid_gompertz \<alpha> \<beta> x \<and> sigmoid_gompertz \<alpha> \<beta> x < 1"
proof
  show "0 < sigmoid_gompertz \<alpha> \<beta> x"
    unfolding sigmoid_gompertz_def by simp
next
  have "- \<alpha> * exp (- \<beta> * x) < 0"
    using assms by simp
  then show "sigmoid_gompertz \<alpha> \<beta> x < 1"
    unfolding sigmoid_gompertz_def by simp
qed

(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_is_bounded_function:
  assumes "\<alpha> > 0"
  shows "bounded_function (sigmoid_gompertz \<alpha> \<beta>)"
  unfolding bounded_function_def
proof (intro bdd_aboveI)
  fix y assume "y \<in> range (\<lambda>x. \<bar>sigmoid_gompertz \<alpha> \<beta> x\<bar>)"
  then obtain x where y_def: "y = \<bar>sigmoid_gompertz \<alpha> \<beta> x\<bar>"
    by blast
  show "y \<le> 1"
    unfolding y_def using gompertz_range[OF assms, of \<beta> x] by simp
qed

text \<open>
  The Gompertz analogue of \<open>logistic_step_saturation\<close>, from the paper's preamble to
  Corollary 6.2. Unlike the logistic function, \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>\<close> is \<^emph>\<open>not\<close> symmetric
  (\<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(-t) \<noteq> 1-\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(t)\<close> in general, unlike \<open>sigmoid_symmetry\<close>), so the two directions need
  two independent threshold computations rather than one plus a reflection. Both reduce to the
  same two-step algebra: solve \<open>\<sigma>\<^sub>\<alpha>\<^sub>\<beta>(t) > c\<close> (or \<open>< c\<close>) for \<open>t\<close> by peeling the two nested
  exponentials with \<open>ln\<close>, in reverse order.
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_saturation_upper:
  fixes t :: real and N :: nat
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0" and N_gt: "N > 1"
  assumes t_gt: "t > (1 / \<beta>) * ln (\<alpha> / ln (real N / (real N - 1)))"
  shows "\<bar>sigmoid_gompertz \<alpha> \<beta> t - 1\<bar> < 1 / real N"
proof -
  have N1_pos: "real N - 1 > 0"
    using N_gt by simp
  have ratio_gt1: "real N / (real N - 1) > 1"
    using N1_pos by simp
  have ln_ratio_pos: "ln (real N / (real N - 1)) > 0"
    using ratio_gt1 by simp
  have bt_lt: "- \<beta> * t < - ln (\<alpha> / ln (real N / (real N - 1)))"
    using t_gt \<beta>_pos by (simp add: field_simps)
  have exp_lt: "exp (- \<beta> * t) < ln (real N / (real N - 1)) / \<alpha>"
  proof -
    have "exp (- \<beta> * t) < exp (- ln (\<alpha> / ln (real N / (real N - 1))))"
      using bt_lt by simp
    also have "\<dots> = ln (real N / (real N - 1)) / \<alpha>"
      using \<alpha>_pos ln_ratio_pos by (simp add: exp_minus exp_ln field_simps)
    finally show ?thesis .
  qed
  have key: "\<alpha> * exp (- \<beta> * t) < ln (real N / (real N - 1))"
    using exp_lt \<alpha>_pos by (simp add: field_simps)
  have gt: "- \<alpha> * exp (- \<beta> * t) > - ln (real N / (real N - 1))"
    using key by simp
  also have "- ln (real N / (real N - 1)) = ln (real N - 1) - ln (real N)"
    using N1_pos N_gt by (simp add: ln_div)
  finally have gt': "- \<alpha> * exp (- \<beta> * t) > ln (real N - 1) - ln (real N)"
    by simp
  have "sigmoid_gompertz \<alpha> \<beta> t > exp (ln (real N - 1) - ln (real N))"
    unfolding sigmoid_gompertz_def using gt' by simp
  also have "exp (ln (real N - 1) - ln (real N)) = (real N - 1) / real N"
    using N1_pos N_gt by (simp add: exp_diff exp_ln)
  finally have "sigmoid_gompertz \<alpha> \<beta> t > (real N - 1) / real N" .
  then have "1 - sigmoid_gompertz \<alpha> \<beta> t < 1 / real N"
    using N_gt by (simp add: field_simps)
  then show ?thesis
    using gompertz_range[OF \<alpha>_pos, of \<beta> t] by simp
qed

(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma gompertz_saturation_lower:
  fixes t :: real and N :: nat
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0" and N_gt: "N > 1"
  assumes t_lt: "t < (1 / \<beta>) * ln (\<alpha> / ln (real N))"
  shows "\<bar>sigmoid_gompertz \<alpha> \<beta> t\<bar> < 1 / real N"
proof -
  have lnN_pos: "ln (real N) > 0"
    using N_gt by simp
  have step1: "\<beta> * t < ln (\<alpha> / ln (real N))"
    using t_lt \<beta>_pos by (simp add: field_simps)
  have step2: "ln (\<alpha> / ln (real N)) = - ln (ln (real N) / \<alpha>)"
    using \<alpha>_pos lnN_pos by (simp add: ln_div)
  have bt_gt: "- \<beta> * t > ln (ln (real N) / \<alpha>)"
    using step1 step2 by simp
  have pos_frac: "ln (real N) / \<alpha> > 0"
    using \<alpha>_pos lnN_pos by simp
  have exp_gt: "exp (- \<beta> * t) > ln (real N) / \<alpha>"
  proof -
    have eq1: "exp (ln (ln (real N) / \<alpha>)) = ln (real N) / \<alpha>"
      using pos_frac by (rule exp_ln)
    have "exp (- \<beta> * t) > exp (ln (ln (real N) / \<alpha>))"
      using bt_gt by simp
    then show ?thesis
      unfolding eq1 .
  qed
  have key: "\<alpha> * exp (- \<beta> * t) > ln (real N)"
  proof -
    have "\<alpha> * (ln (real N) / \<alpha>) < \<alpha> * exp (- \<beta> * t)"
      using exp_gt \<alpha>_pos by (intro mult_strict_left_mono) auto
    then show ?thesis
      using \<alpha>_pos by simp
  qed
  have "- \<alpha> * exp (- \<beta> * t) < - ln (real N)"
    using key by simp
  then have "sigmoid_gompertz \<alpha> \<beta> t < exp (- ln (real N))"
    unfolding sigmoid_gompertz_def by simp
  also have "exp (- ln (real N)) = 1 / real N"
    using lnN_pos N_gt by (simp add: exp_minus exp_ln field_simps)
  finally show ?thesis
    using gompertz_range[OF \<alpha>_pos, of \<beta> t] by simp
qed

text \<open>
  Bundling both directions with an explicit threshold, exactly as \<open>logistic_step_saturation\<close>
  does for the logistic family.
\<close>
(* Section 6: sufficient Gompertz threshold preceding Corollary 6.2 (unnumbered). *)
lemma gompertz_step_saturation:
  fixes h w xk x :: real and N :: nat
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0" and N_gt: "N > 1" and h_pos: "h > 0"
  assumes w_pos: "w > 0"
  assumes w_gt: "w > (1 / h) * max ((1 / \<beta>) * ln (\<alpha> / ln (real N / (real N - 1))))
                                    (- ((1 / \<beta>) * ln (\<alpha> / ln (real N))))"
  shows "x - xk \<ge> h \<Longrightarrow> \<bar>sigmoid_gompertz \<alpha> \<beta> (w * (x - xk)) - 1\<bar> < 1 / real N"
    and "x - xk \<le> - h \<Longrightarrow> \<bar>sigmoid_gompertz \<alpha> \<beta> (w * (x - xk))\<bar> < 1 / real N"
proof -
  define U where "U = (1 / \<beta>) * ln (\<alpha> / ln (real N / (real N - 1)))"
  define L where "L = (1 / \<beta>) * ln (\<alpha> / ln (real N))"
  have w_gt': "w > (1 / h) * max U (- L)"
    using w_gt unfolding U_def L_def .
  have wh_gt_U: "w * h > U" and wh_gt_negL: "w * h > - L"
    using w_gt' h_pos by (simp_all add: field_simps)
  {
    assume "x - xk \<ge> h"
    then have "w * (x - xk) \<ge> w * h"
      using w_pos by (intro mult_left_mono) auto
    then have "w * (x - xk) > U"
      using wh_gt_U by simp
    then show "\<bar>sigmoid_gompertz \<alpha> \<beta> (w * (x - xk)) - 1\<bar> < 1 / real N"
      unfolding U_def using gompertz_saturation_upper[OF \<alpha>_pos \<beta>_pos N_gt] by simp
  }
  {
    assume "x - xk \<le> - h"
    then have "w * (x - xk) \<le> - (w * h)"
      using w_pos by (metis mult_le_cancel_left_pos mult_minus_right)
    then have "w * (x - xk) < L"
      using wh_gt_negL by simp
    then show "\<bar>sigmoid_gompertz \<alpha> \<beta> (w * (x - xk))\<bar> < 1 / real N"
      unfolding L_def using gompertz_saturation_lower[OF \<alpha>_pos \<beta>_pos N_gt] by simp
  }
qed

text \<open>
  Corollary 6.2, part (i), the exact analogue of \<open>logistic_approximation_theorem\<close> above:
  Theorem 2.1 applies directly to any Gompertz sigmoid.
\<close>
(* Corollary 6.2(i): existence-only specialization; prescribed weight is not asserted here. *)
corollary gompertz_approximation_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0"
  assumes a_lt_b: "a < b"
  assumes contin_f: "continuous_on {a..b} f"
  assumes eps_pos: "0 < \<epsilon>"
  defines "xs N \<equiv> unif_part a b N"
  shows "\<exists>N::nat. \<exists>(w::real) > 0. (N > 0) \<and>
           (\<forall>x \<in> {a..b}.
               \<bar>(\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * sigmoid_gompertz \<alpha> \<beta> (w * (x - xs N ! k)))
                              + f(a) * sigmoid_gompertz \<alpha> \<beta> (w * (x - xs N ! 0)) - f x\<bar> < \<epsilon>)"
  unfolding xs_def
  by (rule sigmoidal_approximation_theorem[OF gompertz_is_sigmoidal[OF \<alpha>_pos \<beta>_pos]
        gompertz_is_bounded_function[OF \<alpha>_pos] a_lt_b contin_f eps_pos])

text \<open>
  Corollary 6.2, part (ii): the simultaneous-derivative analogue for the Gompertz family,
  mirroring \<open>logistic_approximation_theorem_derivative\<close> exactly.
\<close>
(* Corollary 6.2(ii): first-derivative, existence-only specialization. *)
corollary gompertz_approximation_theorem_derivative:
  fixes f :: "real \<Rightarrow> real"
  assumes \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>N w. N > 3 \<and> w > 0 \<and>
           (\<forall>x \<in> {a..b}. \<bar>Gj_network (sigmoid_gompertz \<alpha> \<beta>) f (unif_part a b N)
                            ((b - a) / real N) N 1 w x - deriv f x\<bar> < \<epsilon>)"
  by (rule forward_diff_one_approximation[OF gompertz_is_sigmoidal[OF \<alpha>_pos \<beta>_pos]
        gompertz_is_bounded_function[OF \<alpha>_pos] a_lt_b Ck ab_subset eps_pos])

text \<open>
  A third example, of a different kind.  The logistic and Gompertz sigmoids are both smooth;
  \<^const>\<open>heaviside\<close> is the discontinuous one, and it is what shows that the hypothesis the
  \<open>L\<^sup>p\<close> theorems carry -- \<open>\<sigma> \<in> borel_measurable borel\<close> -- is genuinely weaker than the
  \<open>continuous_on UNIV \<sigma>\<close> they used to carry, rather than a cosmetic restatement.

  The paper assumes only that \<open>\<sigma>\<close> is a bounded sigmoidal function.  That is too weak for an
  \<open>L\<^sup>p\<close> statement to have content, since a bounded sigmoidal built from a non-measurable set
  makes the network non-measurable (see the discussion at \<open>Lp_norm\<close> in
  \<^file>\<open>Lp_Approximation.thy\<close>); measurability is the minimal repair, and \<^const>\<open>heaviside\<close>
  shows it is a repair rather than an over-correction: it is admitted here, and was not
  admitted under continuity.  \<open>heaviside_is_sigmoidal\<close> is proved in
  \<^file>\<open>Asymptotic_Qualitative_Properties.thy\<close>.
\<close>

(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma heaviside_is_bounded_function: "bounded_function heaviside"
  unfolding bounded_function_def
  by (rule bdd_aboveI[of _ 1]) (auto simp: heaviside_def)

(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma heaviside_measurable: "heaviside \<in> borel_measurable borel"
proof -
  have eq: "heaviside = indicat_real {0..}"
    by (rule ext) (simp add: heaviside_def indicator_def)
  have "indicat_real {0..} \<in> borel_measurable (borel :: real measure)"
    by (rule borel_measurable_indicator) simp
  then show ?thesis unfolding eq .
qed

text \<open>
  \<^const>\<open>heaviside\<close> is not continuous, so it does \<^emph>\<open>not\<close> satisfy the hypothesis the \<open>L\<^sup>p\<close>
  theorems previously carried.  Continuity at \<open>0\<close> would force a \<open>\<delta>\<close> for \<open>\<epsilon> = 1/2\<close>, but
  \<open>-\<delta>/2\<close> is within \<open>\<delta>\<close> of \<open>0\<close> while its value differs from \<open>heaviside 0 = 1\<close> by exactly \<open>1\<close>.
\<close>
(* Auxiliary for Corollaries 6.1-6.2; not separately numbered. *)
lemma heaviside_not_continuous: "\<not> continuous_on UNIV heaviside"
proof
  assume c: "continuous_on UNIV heaviside"
  have isc: "isCont heaviside 0"
    using c by (simp add: continuous_on_eq_continuous_at)
  have half: "(0::real) < 1/2" by simp
  from isc[unfolded continuous_at_eps_delta, rule_format, OF half]
  obtain d :: real where d_pos: "0 < d"
    and d: "\<And>x. dist x 0 < d \<Longrightarrow> dist (heaviside x) (heaviside 0) < 1/2"
    using dist_real_def by auto
  have neg: "dist (- d / 2) (0::real) < d" using d_pos by (simp only: dist_real_def)
  have "dist (heaviside (- d / 2)) (heaviside 0) = 1"
    using d_pos by (simp add: heaviside_def dist_real_def)
  moreover have "dist (heaviside (- d / 2)) (heaviside 0) < 1/2"
    using d[OF neg] .
  ultimately show False by simp
qed

text \<open>
  Theorem 3.1 for the Heaviside step function.  This is not provable from the hypotheses the
  \<open>L\<^sup>p\<close> theorems carried before the weakening, by \<open>heaviside_not_continuous\<close>.
\<close>
(* Theorem 3.1 specialized to the unnumbered Heaviside example in Section 6. *)
corollary heaviside_Lp_approximation_theorem:
  fixes f :: "real \<Rightarrow> real" and p \<epsilon> :: real
  assumes a_lt_b: "a < b"
  assumes contin_f: "continuous_on {a..b} f"
  assumes p_geq_1: "p \<ge> (1::real)"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>N::nat. \<exists>(w::real) > 0. (N > 0) \<and>
           Lp_enorm p (lebesgue_on {a..b}) (\<lambda>x.
               (\<Sum>k\<in>{2..N+1}. (f(unif_part a b N ! k) - f(unif_part a b N ! (k - 1)))
                              * heaviside (w * (x - unif_part a b N ! k)))
                 + f a * heaviside (w * (x - unif_part a b N ! 0)) - f x) < ennreal \<epsilon>"
  by (rule sigmoidal_Lp_approximation_theorem
        [OF heaviside_is_sigmoidal heaviside_is_bounded_function heaviside_measurable
            a_lt_b contin_f p_geq_1 eps_pos])


subsection \<open>Corollaries 6.1 and 6.2: the prescribed weights\<close>

(* Corollary 6.1: the prescribed logistic weight, including the positive slack delta. *)
definition logistic_paper_weight where
  "logistic_paper_weight a b delta N = real N/(b-a) * ln (real N-1) + delta"

(* Corollary 6.1: one N approximates f and every derivative through order n. *)
corollary logistic_paper_joint_approximation:
  assumes ab: "a < b" and ck: "C_k_on (Suc n) f U" and sub: "{a..b} \<subseteq> U"
    and n: "1 \<le> n" and e: "0 < e" and delta: "0 < delta"
  shows "\<exists>N. n+3 < N \<and> 0 < logistic_paper_weight a b delta N \<and>
    Sup ((\<lambda>x. \<bar>G_network sigmoid f a b N (logistic_paper_weight a b delta N) x - f x\<bar>) ` {a..b}) < e \<and>
    (\<forall>j\<in>{1..n}. Sup ((\<lambda>x. \<bar>Gj_network sigmoid f (unif_part a b N) ((b-a)/N)
        N j (logistic_paper_weight a b delta N) x - (deriv ^^ j) f x\<bar>) ` {a..b}) < e)"
proof (rule joint_approximation_prescribed_weights[OF sigmoid_is_bounded_function ab ck sub n e])
  fix N :: nat assume N: "3 < N"
  have lp: "0 < ln (real N-1)" using N by simp
  have "0 < real N/(b-a) * ln (real N-1)" using ab N lp by (intro mult_pos_pos divide_pos_pos) auto
  then show "0 < logistic_paper_weight a b delta N"
    unfolding logistic_paper_weight_def using delta by linarith
next
  fix N :: nat assume N: "3 < N"
  have h: "0 < (b-a)/real N" using ab N by simp
  have w: "(1 / ((b-a)/real N)) * ln (real N-1) < logistic_paper_weight a b delta N"
    unfolding logistic_paper_weight_def using delta by simp
  show "\<forall>k < N+2.
      (\<forall>y. y - unif_part a b N ! k \<ge> (b-a)/N \<longrightarrow> \<bar>sigmoid (logistic_paper_weight a b delta N*(y-unif_part a b N ! k))-1\<bar> < 1/N) \<and>
      (\<forall>y. y - unif_part a b N ! k \<le> -((b-a)/N) \<longrightarrow> \<bar>sigmoid (logistic_paper_weight a b delta N*(y-unif_part a b N ! k))\<bar> < 1/N)"
    using logistic_step_saturation[OF _ h w] N by auto
qed

(* Corollary 6.2: the printed Gompertz weight; the logarithms are inside absolute values. *)
definition gompertz_paper_weight where
  "gompertz_paper_weight alpha beta a b delta N =
    real N / ((b-a)*beta) *
      max \<bar>ln (-(1/alpha) * ln ((real N-1)/real N))\<bar>
          \<bar>ln ((1/alpha) * ln (real N))\<bar> + delta"

(* Auxiliary for Corollary 6.2: rewrite the printed weight into the tail-bound coordinates. *)
lemma gompertz_paper_weight_eq:
  assumes alpha: "0 < alpha" and N: "1 < N"
  shows "gompertz_paper_weight alpha beta a b delta N =
    real N / ((b-a)*beta) *
      max \<bar>ln (alpha / ln (real N / (real N-1)))\<bar>
          \<bar>ln (alpha / ln (real N))\<bar> + delta"
proof -
  have np: "0 < real N" and nm: "0 < real N-1" using N by auto
  have lnN: "0 < ln (real N)" using N by simp
  have ratio: "1 < real N / (real N-1)" using N by (simp add: divide_less_eq)
  have lnR: "0 < ln (real N / (real N-1))" using ratio by simp
  have logratio: "- ln ((real N-1)/real N) = ln (real N/(real N-1))"
    using np nm by (simp add: ln_div)
  have arg: "-(1/alpha) * ln ((real N-1)/real N) = ln (real N/(real N-1))/alpha"
    using arg_cong[OF logratio, of "\<lambda>x. x/alpha"] by simp
  show ?thesis unfolding gompertz_paper_weight_def arg
    using alpha lnN lnR by (simp add: ln_div abs_minus_commute)
qed

(* Auxiliary for Corollary 6.2: the prescribed weight is positive and exceeds both tail thresholds. *)
lemma gompertz_paper_weight_sufficient:
  assumes alpha: "0 < alpha" and beta: "0 < beta" and ab: "a < b"
    and delta: "0 < delta" and N: "3 < N"
  shows "0 < gompertz_paper_weight alpha beta a b delta N"
    and "(1 / ((b-a)/real N)) *
      max ((1/beta) * ln (alpha / ln (real N/(real N-1))))
          (- ((1/beta) * ln (alpha / ln (real N))))
      < gompertz_paper_weight alpha beta a b delta N"
proof -
  let ?A = "ln (alpha / ln (real N/(real N-1)))"
  let ?B = "ln (alpha / ln (real N))"
  have N1: "1 < N" using N by simp
  have pref: "0 < real N/((b-a)*beta)" using N ab beta by simp
  have eq: "gompertz_paper_weight alpha beta a b delta N =
      real N/((b-a)*beta) * max \<bar>?A\<bar> \<bar>?B\<bar> + delta"
    by (rule gompertz_paper_weight_eq[OF alpha N1])
  show "0 < gompertz_paper_weight alpha beta a b delta N"
    unfolding eq using pref delta by (smt (verit) abs_ge_zero mult_nonneg_nonneg)
  have scaled: "max ((1/beta)*?A) (-((1/beta)*?B)) = (1/beta) * max ?A (-?B)"
    using beta by (simp add: max_divide_distrib_right)
  have max_le: "max ?A (-?B) \<le> max \<bar>?A\<bar> \<bar>?B\<bar>"
    by (intro max.mono) auto
  have bound: "real N/((b-a)*beta) * max ?A (-?B)
      \<le> real N/((b-a)*beta) * max \<bar>?A\<bar> \<bar>?B\<bar>"
    using max_le pref by (intro mult_left_mono) auto
  have coeff: "(1 / ((b-a)/real N)) * ((1/beta) * max ?A (-?B)) =
      real N/((b-a)*beta) * max ?A (-?B)"
    by (simp add: algebra_simps)
  show "(1 / ((b-a)/real N)) * max ((1/beta)*?A) (-((1/beta)*?B))
      < gompertz_paper_weight alpha beta a b delta N"
    unfolding eq scaled coeff using bound delta by argo
qed

(* Corollary 6.2: the printed weight, one N, f, and every derivative through order n. *)
corollary gompertz_paper_joint_approximation:
  assumes alpha: "0 < alpha" and beta: "0 < beta"
    and ab: "a < b" and ck: "C_k_on (Suc n) f U" and sub: "{a..b} \<subseteq> U"
    and n: "1 \<le> n" and e: "0 < e" and delta: "0 < delta"
  shows "\<exists>N. n+3 < N \<and> 0 < gompertz_paper_weight alpha beta a b delta N \<and>
    Sup ((\<lambda>x. \<bar>G_network (sigmoid_gompertz alpha beta) f a b N
      (gompertz_paper_weight alpha beta a b delta N) x - f x\<bar>) ` {a..b}) < e \<and>
    (\<forall>j\<in>{1..n}. Sup ((\<lambda>x. \<bar>Gj_network (sigmoid_gompertz alpha beta) f
      (unif_part a b N) ((b-a)/N) N j (gompertz_paper_weight alpha beta a b delta N) x
        - (deriv ^^ j) f x\<bar>) ` {a..b}) < e)"
proof (rule joint_approximation_prescribed_weights[OF gompertz_is_bounded_function[OF alpha] ab ck sub n e])
  fix N :: nat assume N: "3 < N"
  show "0 < gompertz_paper_weight alpha beta a b delta N"
    by (rule gompertz_paper_weight_sufficient(1)[OF alpha beta ab delta N])
next
  fix N :: nat assume N: "3 < N"
  have N1: "1 < N" using N by simp
  have h: "0 < (b-a)/real N" using ab N by simp
  note w = gompertz_paper_weight_sufficient[OF alpha beta ab delta N]
  show "\<forall>k < N+2.
      (\<forall>y. y - unif_part a b N ! k \<ge> (b-a)/N \<longrightarrow>
        \<bar>sigmoid_gompertz alpha beta (gompertz_paper_weight alpha beta a b delta N*(y-unif_part a b N ! k))-1\<bar> < 1/N) \<and>
      (\<forall>y. y - unif_part a b N ! k \<le> -((b-a)/N) \<longrightarrow>
        \<bar>sigmoid_gompertz alpha beta (gompertz_paper_weight alpha beta a b delta N*(y-unif_part a b N ! k))\<bar> < 1/N)"
    using gompertz_step_saturation[OF alpha beta N1 h w] by (auto simp: minus_divide_left)
qed

end
