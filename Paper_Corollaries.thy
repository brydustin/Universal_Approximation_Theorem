theory Paper_Corollaries
  imports Concrete_Sigmoidal_Examples Simultaneous_Approximation_General_j
begin

(* Auxiliary for Theorem 4.2 and Corollaries 6.1-6.2: an N-independent rate numerator. *)
definition derivative_rate_constant where
  "derivative_rate_constant \<sigma> f a b j =
    (2 * real j + 1) * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * (b-a)
    + real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * (b-a)
    + Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})
    + Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * (b-a)
      * (2 * (2 * real j + 1) * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV) + 2 * real j + 2)"

(* Auxiliary for Theorem 4.2: remove the N-dependence from the rate numerator. *)
lemma derivative_rate_constant_bound:
  fixes \<sigma> f :: "real \<Rightarrow> real"
  assumes ab: "a < b" and ck: "C_k_on (Suc j) f U" and sub: "{a..b} \<subseteq> U"
    and bnd: "bounded_function \<sigma>" and j: "1 \<le> j" and N: "j+3 < N"
    and x: "x \<in> {a..b}"
    and sat: "\<forall>k < N+2.
      (\<forall>y. y - unif_part a b N ! k \<ge> (b-a)/N \<longrightarrow> \<bar>\<sigma> (w*(y-unif_part a b N ! k))-1\<bar> < 1/N) \<and>
      (\<forall>y. y - unif_part a b N ! k \<le> -((b-a)/N) \<longrightarrow> \<bar>\<sigma> (w*(y-unif_part a b N ! k))\<bar> < 1/N)"
  shows "\<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j w x - (deriv ^^ j) f x\<bar>
    \<le> derivative_rate_constant \<sigma> f a b j / N"
proof -
  let ?L = "Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  have L: "0 \<le> ?L" by (rule Lj_nonneg[OF ck sub ab])
  have h: "(b-a)/real N \<le> b-a" using ab N by (simp add: divide_le_eq)
  have num: "real j * ?L * ((b-a)/real N) \<le> real j * ?L * (b-a)"
    using h L by (intro mult_left_mono) auto
  note raw = forward_diff_rate_gen[OF ab refl refl ck sub bnd j N x sat]
  show ?thesis using raw num N
    unfolding derivative_rate_constant_def
    by (smt (verit) divide_right_mono of_nat_0_le_iff)
qed

(* Auxiliary for uniform-norm conclusions: retain a strict margin when taking a supremum. *)
lemma strict_sup_from_half_bound:
  fixes F :: "'a \<Rightarrow> real"
  assumes ne: "A \<noteq> {}" and e: "0 < e" and bound: "\<And>x. x \<in> A \<Longrightarrow> F x < e/2"
  shows "Sup (F ` A) < e"
proof -
  have "Sup (F ` A) \<le> e/2"
    by (rule cSup_least) (use ne in simp, use bound in fastforce)
  then show ?thesis using e by linarith
qed

(* Theorem 2.1: strict supremum formulation for arbitrary continuous targets. *)
theorem sigmoidal_uniform_approximation_sup:
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and ab: "a < b" and fc: "continuous_on {a..b} f" and e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Sup ((\<lambda>x. \<bar>G_network \<sigma> f a b N w x-f x\<bar>) ` {a..b}) < e"
proof -
  have e2: "0 < e/2" using e by simp
  obtain N w where N: "0 < N" and w: "0 < w"
    and bd: "\<forall>x\<in>{a..b}. \<bar>G_network \<sigma> f a b N w x-f x\<bar> < e/2"
    using sigmoidal_approximation_theorem[OF sig bnd ab fc e2]
    unfolding G_network_def by blast
  have sup: "Sup ((\<lambda>x. \<bar>G_network \<sigma> f a b N w x-f x\<bar>) ` {a..b}) < e"
    by (rule strict_sup_from_half_bound) (use ab e bd in auto)
  show ?thesis by (intro exI[where x=N] exI[where x=w]) (use N w sup in simp)
qed

(* Theorem 4.1: strict supremum formulation, matching the printed norm conclusion. *)
theorem forward_diff_simultaneous_approximation_sup:
  fixes a b e :: real and n :: nat and f \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and ab: "a < b" and ck: "C_k_on (Suc n) f U" and sub: "{a..b} \<subseteq> U"
    and n: "1 \<le> n" and e: "0 < e"
  shows "\<exists>N w. n + 3 < N \<and> 0 < w \<and>
    (\<forall>j\<in>{1..n}. Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/real N) N j w x
                             - (deriv ^^ j) f x\<bar>) ` {a..b}) < e)"
proof -
  have e2: "0 < e/2" using e by simp
  obtain N w where N: "n + 3 < N" and w: "0 < w"
    and bd: "\<forall>j\<in>{1..n}. \<forall>x\<in>{a..b}.
      \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/real N) N j w x - (deriv ^^ j) f x\<bar> < e/2"
    using forward_diff_simultaneous_approximation[OF sig bnd ab ck sub n e2] by blast
  have sup: "\<forall>j\<in>{1..n}. Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/real N) N j w x
                                     - (deriv ^^ j) f x\<bar>) ` {a..b}) < e"
  proof
    fix j assume j: "j \<in> {1..n}"
    show "Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/real N) N j w x
                      - (deriv ^^ j) f x\<bar>) ` {a..b}) < e"
      by (rule strict_sup_from_half_bound) (use ab e bd j in auto)
  qed
  show ?thesis by (intro exI[where x=N] exI[where x=w]) (use N w sup in simp)
qed

(* Corollaries 6.1-6.2, shared proof: a prescribed saturated weight, one N, and all orders. *)
theorem joint_approximation_prescribed_weights:
  fixes \<sigma> f :: "real \<Rightarrow> real" and W :: "nat \<Rightarrow> real"
  assumes bnd: "bounded_function \<sigma>" and ab: "a < b"
    and ck: "C_k_on (Suc n) f U" and sub: "{a..b} \<subseteq> U"
    and n: "1 \<le> n" and e: "0 < e"
    and Wpos: "\<And>N. 3 < N \<Longrightarrow> 0 < W N"
    and Wsat: "\<And>N. 3 < N \<Longrightarrow> \<forall>k < N+2.
      (\<forall>y. y - unif_part a b N ! k \<ge> (b-a)/N \<longrightarrow> \<bar>\<sigma> (W N*(y-unif_part a b N ! k))-1\<bar> < 1/N) \<and>
      (\<forall>y. y - unif_part a b N ! k \<le> -((b-a)/N) \<longrightarrow> \<bar>\<sigma> (W N*(y-unif_part a b N ! k))\<bar> < 1/N)"
  shows "\<exists>N. n+3 < N \<and> 0 < W N \<and>
    Sup ((\<lambda>x. \<bar>G_network \<sigma> f a b N (W N) x - f x\<bar>) ` {a..b}) < e \<and>
    (\<forall>j\<in>{1..n}. Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N)
        N j (W N) x - (deriv ^^ j) f x\<bar>) ` {a..b}) < e)"
proof -
  have ck1: "C_k_on 1 f U" using C_k_on_mono[OF ck, of 1] by simp
  have fc: "continuous_on {a..b} f"
    using ck1 sub unfolding C_k_on_def
    by (auto intro: continuous_on_subset differentiable_imp_continuous_on)
  let ?M = "Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})"
  let ?S = "Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)"
  have Mb: "bdd_above ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})"
    using fc ab continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have M: "0 \<le> ?M"
    using cSUP_upper[OF _ Mb, of a] ab by (smt (verit) atLeastAtMost_iff abs_ge_zero)
  have S: "0 \<le> ?S"
    using bnd unfolding bounded_function_def by (meson UNIV_I abs_ge_zero cSUP_upper2)
  define eta where "eta = (e/2) / (?M + 2*?S + 2)"
  have eta: "0 < eta" unfolding eta_def using e M S by simp
  obtain d where d: "0 < d"
    and dc: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x-y\<bar> < d \<longrightarrow> \<bar>f x-f y\<bar> < eta"
    using uniform_continuity_interval[OF ab fc eta] by blast
  define K where "K = Max ((derivative_rate_constant \<sigma> f a b) ` {1..n})"
  have K: "\<And>j. j \<in> {1..n} \<Longrightarrow> derivative_rate_constant \<sigma> f a b j \<le> K"
    unfolding K_def by (rule Max_ge) auto
  obtain N :: nat where big:
    "max (real (n+3)) (max (2*(b-a)/d) (max (1/eta) (2*K/e))) < real N"
    using reals_Archimedean2 by blast
  have N: "n+3 < N" and N3: "3 < N" using big by auto
  have growth: "2*(b-a)/d < real N \<and> 3 < N \<and> 1/eta < real N"
    using big N3 by auto
  have KN: "K / real N < e/2"
  proof -
    have "2*K/e < real N" using big by simp
    then show ?thesis using e N by (simp add: field_simps)
  qed
  have value_point: "\<forall>x\<in>{a..b}. \<bar>G_network \<sigma> f a b N (W N) x - f x\<bar> < e/2"
    unfolding G_network_def
    by (rule sigmoidal_approximation_fixed_parameters[OF bnd ab fc eta_def eta d dc growth Wsat[OF N3]])
  have value_sup: "Sup ((\<lambda>x. \<bar>G_network \<sigma> f a b N (W N) x - f x\<bar>) ` {a..b}) < e"
    by (rule strict_sup_from_half_bound) (use ab e value_point in auto)
  have deriv_sup: "\<forall>j\<in>{1..n}. Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N)
        N j (W N) x - (deriv ^^ j) f x\<bar>) ` {a..b}) < e"
  proof (intro ballI)
    fix j assume j: "j \<in> {1..n}"
    have ck_j: "C_k_on (Suc j) f U" using C_k_on_mono[OF ck, of "Suc j"] j by simp
    have bound: "\<And>x. x \<in> {a..b} \<Longrightarrow>
      \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j (W N) x - (deriv ^^ j) f x\<bar> < e/2"
    proof -
      fix x assume x: "x \<in> {a..b}"
      have "\<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j (W N) x - (deriv ^^ j) f x\<bar>
        \<le> derivative_rate_constant \<sigma> f a b j / real N"
        by (rule derivative_rate_constant_bound[OF ab ck_j sub bnd _ _ x Wsat[OF N3]])
           (use j N in auto)
      also have "\<dots> \<le> K / real N" using K[OF j] by (intro divide_right_mono) auto
      finally show "\<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j (W N) x - (deriv ^^ j) f x\<bar> < e/2"
        using KN by linarith
    qed
    show "Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N)
        N j (W N) x - (deriv ^^ j) f x\<bar>) ` {a..b}) < e"
      by (rule strict_sup_from_half_bound) (use ab e bound in auto)
  qed
  show ?thesis
    by (intro exI[where x=N]) (use N Wpos[OF N3] value_sup deriv_sup in simp)
qed

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

(* Auxiliary for Theorem 4.2: a derivative-dependent consistency constant, independent of N and sigma. *)
definition paper_consistency_constant where
  "paper_consistency_constant f a b j =
    (2 * real j + 2) * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) + 1"

(* Equation (4.4), auxiliary for Theorem 4.2: the chosen constant dominates the proved consistency coefficient. *)
lemma paper_consistency_constant_valid:
  assumes ck: "C_k_on (Suc j) f U" and sub: "{a..b} \<subseteq> U" and ab: "a < b"
  shows "0 < paper_consistency_constant f a b j"
    and "real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})
      < paper_consistency_constant f a b j"
proof -
  let ?L = "Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  have L: "0 \<le> ?L" by (rule Lj_nonneg[OF ck sub ab])
  have jL: "0 \<le> real j * ?L" using L by simp
  show "0 < paper_consistency_constant f a b j"
    unfolding paper_consistency_constant_def using L jL by (simp only: algebra_simps; linarith)
  show "real j * ?L < paper_consistency_constant f a b j"
    unfolding paper_consistency_constant_def using L jL by (simp only: algebra_simps; linarith)
qed

(* Auxiliary for Theorem 4.2: comparison with the paper's displayed numerator. *)
lemma derivative_constant_lt_paper_numerator:
  fixes \<sigma> f :: "real \<Rightarrow> real"
  assumes ab: "a < b" and ck: "C_k_on (Suc j) f U" and sub: "{a..b} \<subseteq> U"
    and bnd: "bounded_function \<sigma>"
  defines "L \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
    and "M \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
    and "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "derivative_rate_constant \<sigma> f a b j <
    L*(b-a)*(2*S+1+max 2 (real j)) +
    paper_consistency_constant f a b j*(b-a)*(4*S+3) + M"
proof -
  have L: "0 \<le> L" unfolding L_def by (rule Lj_nonneg[OF ck sub ab])
  have S: "0 \<le> S"
    unfolding S_def using bnd unfolding bounded_function_def by (meson UNIV_I abs_ge_zero cSUP_upper2)
  have jS: "0 \<le> real j * S" using S by simp
  have coeff: "(5*real j+3)+(4*real j+2)*S \<le>
      2*S+1+max 2 (real j)+(2*real j+2)*(4*S+3)"
    using S jS max.cobounded1[of "2::real" "real j"]
    by (simp only: algebra_simps; linarith)
  have nonneg: "0 \<le> L*(b-a)" using L ab by simp
  have bd: "L*(b-a)*((5*real j+3)+(4*real j+2)*S) \<le>
      L*(b-a)*(2*S+1+max 2 (real j)+(2*real j+2)*(4*S+3))"
    by (rule mult_left_mono[OF coeff nonneg])
  have slack: "0 < (b-a)*(4*S+3)" using ab S by (intro mult_pos_pos) auto
  show ?thesis
    unfolding derivative_rate_constant_def paper_consistency_constant_def
      L_def[symmetric] M_def[symmetric] S_def[symmetric]
    using bd slack by (simp only: algebra_simps; linarith)
qed

(* Theorem 4.2: the paper's quantitative shape, with an explicit enlarged consistency constant and strict supremum. *)
theorem forward_diff_paper_rate:
  fixes \<sigma> f :: "real \<Rightarrow> real"
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and ab: "a < b" and ck: "C_k_on (Suc j) f U" and sub: "{a..b} \<subseteq> U"
    and j: "1 \<le> j" and N: "j+3 < N"
  defines "L \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
    and "M \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
    and "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<exists>w0>0. \<forall>w\<ge>w0.
    Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j w x
      - (deriv ^^ j) f x\<bar>) ` {a..b}) <
    (L*(b-a)*(2*S+1+max 2 (real j)) +
      paper_consistency_constant f a b j*(b-a)*(4*S+3) + M) / N"
proof -
  have Npos: "0 < N" using N by simp
  obtain w0 where w0: "0 < w0"
    and sat: "\<forall>w\<ge>w0. \<forall>k<N+2.
      (\<forall>y. y-unif_part a b N!k \<ge> (b-a)/N \<longrightarrow> \<bar>\<sigma> (w*(y-unif_part a b N!k))-1\<bar> < 1/N) \<and>
      (\<forall>y. y-unif_part a b N!k \<le> -((b-a)/N) \<longrightarrow> \<bar>\<sigma> (w*(y-unif_part a b N!k))\<bar> < 1/N)"
    using sigma_saturation_for_N[OF sig ab Npos refl] by blast
  let ?P = "L*(b-a)*(2*S+1+max 2 (real j)) +
      paper_consistency_constant f a b j*(b-a)*(4*S+3) + M"
  have strict: "derivative_rate_constant \<sigma> f a b j / real N < ?P / real N"
    using derivative_constant_lt_paper_numerator[OF ab ck sub bnd] Npos
    unfolding L_def M_def S_def by (intro divide_strict_right_mono) auto
  show ?thesis
  proof (intro exI[where x=w0] conjI w0 allI impI)
    fix w assume w: "w0 \<le> w"
    have bd: "\<And>x. x \<in> {a..b} \<Longrightarrow>
      \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j w x - (deriv ^^ j) f x\<bar>
      \<le> derivative_rate_constant \<sigma> f a b j / real N"
      by (rule derivative_rate_constant_bound[OF ab ck sub bnd j N]) (use sat w in auto)
    have "Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j w x
        - (deriv ^^ j) f x\<bar>) ` {a..b}) \<le> derivative_rate_constant \<sigma> f a b j / real N"
      by (rule cSup_least) (use ab in simp, use bd in fastforce)
    then show "Sup ((\<lambda>x. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j w x
        - (deriv ^^ j) f x\<bar>) ` {a..b}) < ?P / real N"
      using strict by linarith
  qed
qed

end
