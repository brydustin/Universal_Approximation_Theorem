theory Sigmoid_Definition
  imports "HOL-Analysis.Analysis" "HOL-Combinatorics.Stirling"
          Real_and_Complex_Analytic.Higher_Differentiability
begin

section \<open>Definition and Analytical Properties\<close>

text \<open>
  The logistic function is defined at an arbitrary real normed field that is also a Banach
  space, rather than at the reals alone, so that the holomorphic extension needed for real
  analyticity (theory Sigmoid\_Analytic) is \<^emph>\<open>this same constant\<close> read at type
  complex, rather than a second definition.  Both real and complex inhabit that class.

  Everything below is stated for real arguments, and that restriction is necessary rather
  than bookkeeping: the identities of this section run through \<open>1 + exp x \<noteq> 0\<close>,
  which is exactly what fails over the complex numbers at the odd multiples of i*pi -- the
  very poles that fix the radius of analyticity at pi.
\<close>
(* Section 6: logistic function (unnumbered). *)
definition sigmoid :: "'a::{real_normed_field,banach} \<Rightarrow> 'a" where
  "sigmoid x = exp x / (1 + exp x)"

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_alt_def: "sigmoid (x::real) = inverse (1 + exp(-x))"
  unfolding sigmoid_def by (simp add: field_simps exp_minus)

subsection \<open>Range, Monotonicity, and Symmetry\<close>

text \<open>Bounds\<close>
(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_pos: "sigmoid (x::real) > 0"
  by (simp add: add_pos_pos sigmoid_def)

text \<open>Prove that \(\sigma(x) < 1\) for all \(x\).\<close>
(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_less_1: "sigmoid (x::real) < 1"
  by (simp add: add_strict_increasing sigmoid_def)

text \<open>The sigmoid function \(\sigma(x)\) satisfies
  \[
    0 < \sigma(x) < 1
    \quad\text{for all }x \in \mathbb{R}.
  \]
\<close>
(* Supplementary logistic-function property for Section 6; no separate paper label. *)
corollary sigmoid_range: "0 < sigmoid (x::real) \<and> sigmoid x < 1"
  by (simp only: sigmoid_less_1 sigmoid_pos)

text \<open>
  Symmetry around the origin:
  The sigmoid function \(\sigma\) satisfies
  \[
    \sigma(-x) = 1 - \sigma(x)
    \quad\text{for all }x\in\mathbb{R},
  \]
  reflecting that negative inputs shift the output towards \(0\),
  while positive inputs shift it towards \(1\).
\<close>


(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_symmetry: "sigmoid (-x::real) = 1 - sigmoid x"
proof -
  have "sigmoid (-x) = inverse (1 + exp x)"
    by (simp add: sigmoid_alt_def)
  also have "... = 1 - exp x / (1 + exp x)"
    using add_pos_pos[OF zero_less_one exp_gt_zero[of x]] by (simp add: field_simps)
  also have "... = 1 - sigmoid x"
    by (simp add: sigmoid_def)
  finally show ?thesis.
qed

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
corollary "sigmoid(x::real) + sigmoid(-x) = 1"
  by (simp only: sigmoid_symmetry)

text \<open>The sigmoid function is strictly increasing.\<close>
(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_strictly_increasing:
  fixes x1 x2 :: real
  assumes "x1 < x2"
  shows "sigmoid x1 < sigmoid x2"
proof -
  have "exp x1 < exp x2" using assms by simp
  then have "exp x1 / (1 + exp x1) < exp x2 / (1 + exp x2)"
    using real_shrink_lt [of "exp x1" "exp x2"] by simp
  thus ?thesis unfolding sigmoid_def .
qed

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_at_zero: "sigmoid (0::real) = 1/2"
  by (simp add: sigmoid_def)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_left_dom_range:
  assumes "(x::real) < 0"
  shows "sigmoid x < 1/2"
  using assms sigmoid_at_zero sigmoid_strictly_increasing by moura

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_right_dom_range:
  assumes "(x::real) > 0"
  shows "sigmoid x > 1/2"
  using assms sigmoid_at_zero sigmoid_strictly_increasing by moura




subsection \<open>Differentiability and Derivative Identities\<close>
text \<open>
  Derivative:
  The derivative of the sigmoid function can be expressed in terms of itself:
  \[
    \sigma'(x) = \sigma(x)\,(1 - \sigma(x)).
  \]
  This identity is central to backpropagation for weight updates in neural
  networks, since it shows the derivative depends only on \(\sigma(x)\),
  simplifying optimisation computations.
\<close>


(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma uminus_derive_minus_one: "(uminus has_derivative (*) (-1 :: real)) (at a within A)"
  by (rule has_derivative_eq_rhs, (rule derivative_intros)+, fastforce)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_differentiable: 
  "(\<lambda>x::real. sigmoid x) differentiable_on UNIV"
proof -
  have "\<forall>x::real. sigmoid differentiable (at x)"
  proof 
    fix x :: real
    have num_diff: "(\<lambda>x. exp x) differentiable (at x)"
      by (simp only: field_differentiable_imp_differentiable field_differentiable_within_exp)
    have denom_diff: "(\<lambda>x. 1 + exp x) differentiable (at x)"
      by (simp add: num_diff)
    hence "(\<lambda>x. exp x / (1 + exp x)) differentiable (at x)"
      by (simp add: add_nonneg_eq_0_iff num_diff)
    thus "sigmoid differentiable (at x)"
      unfolding sigmoid_def by simp
  qed
  thus ?thesis
    by (simp add: differentiable_on_def)
qed

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_differentiable':
 "sigmoid field_differentiable at (x::real)"
  using DERIV_deriv_iff_field_differentiable DERIV_deriv_iff_real_differentiable 
        differentiable_on_def sigmoid_differentiable by blast


(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_derivative:
  shows "deriv sigmoid (x::real) = sigmoid x * (1 - sigmoid x)"
  unfolding sigmoid_def
proof -    
  (* The three side conditions of deriv_divide, named. *)
  have "deriv (\<lambda>x. exp x /(1 + exp x)) x = (deriv (\<lambda>x. exp x) x * (\<lambda>x. 1 + exp x) x - (\<lambda>x. exp x) x * deriv (\<lambda>x. 1 + exp x) x) / ((\<lambda>x. 1 + exp x) x)\<^sup>2"
  proof (rule deriv_divide)
    show "(\<lambda>x. exp x) field_differentiable at x"
      by (rule field_differentiable_within_exp)
    show "(\<lambda>x. 1 + exp x) field_differentiable at x"
      by (intro field_differentiable_add field_differentiable_const
                field_differentiable_within_exp)
    show "(\<lambda>x. 1 + exp x) x \<noteq> 0"
      using add_pos_pos[OF zero_less_one exp_gt_zero[of x]] by simp
  qed
  also have "... = ((exp x) * (1 + exp x) -(exp x)* (deriv (\<lambda>w. ((\<lambda>v. 1)w + (\<lambda> u. exp u)w)) x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = ((exp x) * (1 + exp x) -(exp x) * (deriv (\<lambda>v. 1) x  + deriv (\<lambda> u. exp u) x)) / (1 + exp x)\<^sup>2"
    by (subst deriv_add, simp, simp only: field_differentiable_within_exp, auto)
  also have "... = ((exp x) * (1 + exp x) -(exp x)  * (exp x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = (exp x + (exp x)\<^sup>2 -(exp x)\<^sup>2) / (1 + exp x)\<^sup>2"
    by (simp add: ring_class.ring_distribs(1))  
  also have "... = (exp x / (1 + exp x))*(1 / (1 + exp x))"
    by (simp add: power2_eq_square)
  also have "... = exp x / (1 + exp x)*(1 - exp x / (1 + exp x))"
    by (simp add: add_divide_eq_if_simps(4))
  finally show "deriv (\<lambda>x. exp x / (1 + exp x)) x = exp x / (1 + exp x) * (1 - exp x / (1 + exp x))".  
qed

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma  sigmoid_derivative': "(sigmoid has_real_derivative (sigmoid x * (1 - sigmoid x))) (at (x::real))"
  by (metis field_differentiable_derivI sigmoid_derivative sigmoid_differentiable')

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma deriv_one_minus_sigmoid:
  "deriv (\<lambda>y::real. 1 - sigmoid y) x = sigmoid x * (sigmoid x - 1)"
  apply (subst deriv_diff)
    apply simp
  apply (simp only: sigmoid_differentiable')
  apply (simp add: sigmoid_derivative vector_space_over_itself.scale_right_diff_distrib)  
  done
  


subsection \<open>Logit, Softmax, and the Tanh Connection\<close>


text \<open>Logit (Inverse of Sigmoid):
  The inverse of the sigmoid function, often called the logit function,
  is defined by
  \[
    \sigma^{-1}(y) \;=\; \ln\!\bigl(\tfrac{y}{1 - y}\bigr),
    \quad 0 < y < 1.
  \]
  This transformation converts a probability \(y\in(0,1)\) (the output of
  the sigmoid) back into the corresponding log-odds.\<close>

definition logit :: "real \<Rightarrow> real" where
  "logit p = (if 0 < p \<and> p < 1 then ln (p / (1 - p)) else undefined)"


(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_logit_comp:
  "0 < p \<and> p < 1 \<Longrightarrow> sigmoid (logit p) = p"
  by (smt (verit, del_insts) divide_pos_pos exp_ln_iff logit_def real_shrink_Galois sigmoid_def)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma logit_sigmoid_comp:
  "logit (sigmoid p ) = p"
  by (smt (verit, best) sigmoid_less_1 sigmoid_logit_comp sigmoid_pos sigmoid_strictly_increasing)

subsection \<open>The Logistic Function as an Embedding of the Line into the Unit Interval\<close>

text \<open>
  The two composition laws above already say that the logistic function and the logit are
  mutually inverse, but they say it one point at a time.  This subsection packages that
  into the three statements a reader is likely to want, namely that
  \[
    \sigma \colon \mathbb{R} \longrightarrow (0,1)
  \]
  is a bijection, an order isomorphism, a homeomorphism, and an isomorphism of measurable
  spaces.  Isabelle has no bundled types of order isomorphisms, homeomorphisms or
  measurable equivalences, so each is recorded in the idiom the library actually uses:
  \<open>bij_betw\<close>, a pair of strict-monotonicity facts, \<open>homeomorphism\<close>, and a pair of
  measurability facts against the restricted measurable space on the open unit interval.
  Nothing in Sections 3 to 7 needs any of this -- the approximation theorems ask only that
  the activation be sigmoidal, bounded and Borel measurable -- so these results are here to
  make the inverse explicit, not because a later proof consumes them.
\<close>

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_inj: "inj (sigmoid :: real \<Rightarrow> real)"
  by (rule inj_on_inverseI [where g = logit]) (rule logit_sigmoid_comp)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_bij_betw: "bij_betw (sigmoid :: real \<Rightarrow> real) UNIV {0<..<1}"
  by (rule bij_betw_byWitness [where f' = logit])
     (auto simp: logit_sigmoid_comp sigmoid_logit_comp sigmoid_pos sigmoid_less_1)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma logit_bij_betw: "bij_betw logit {0<..<1} UNIV"
  by (rule bij_betw_byWitness [where f' = sigmoid])
     (auto simp: logit_sigmoid_comp sigmoid_logit_comp sigmoid_pos sigmoid_less_1)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_range_eq: "range (sigmoid :: real \<Rightarrow> real) = {0<..<1}"
  using sigmoid_bij_betw by (simp add: bij_betw_def)

text \<open>Order isomorphism: both directions are strictly increasing.\<close>

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma strict_mono_sigmoid: "strict_mono (sigmoid :: real \<Rightarrow> real)"
  by (rule strict_monoI) (rule sigmoid_strictly_increasing)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_less_iff: "sigmoid (x::real) < sigmoid y \<longleftrightarrow> x < y"
  by (simp add: strict_mono_less strict_mono_sigmoid)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_le_iff: "sigmoid (x::real) \<le> sigmoid y \<longleftrightarrow> x \<le> y"
  by (simp add: strict_mono_less_eq strict_mono_sigmoid)

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma logit_strict_mono_on: "strict_mono_on {0<..<1} logit"
proof (rule strict_mono_onI)
  fix p q :: real
  assume "p \<in> {0<..<1}" "q \<in> {0<..<1}" "p < q"
  hence "sigmoid (logit p) < sigmoid (logit q)"
    by (simp add: sigmoid_logit_comp)
  thus "logit p < logit q" by (simp add: sigmoid_less_iff)
qed

text \<open>
  Topological isomorphism.  Continuity of the logit is the one ingredient that does not
  follow from the composition laws: it is proved on the open interval, where the quotient
  \(p/(1-p)\) is positive and the logarithm is therefore continuous.  Outside that interval
  the logit is a constant (the value of \<open>undefined\<close>), which is what makes the
  measurability statement below hold on the whole line.
\<close>

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_continuous_on: "continuous_on S (sigmoid :: real \<Rightarrow> real)"
proof -
  have nz: "1 + exp (x::real) \<noteq> 0" for x
    using add_pos_pos [OF zero_less_one exp_gt_zero [of x]] by simp
  show ?thesis
    unfolding sigmoid_def by (intro continuous_intros) (simp add: nz)
qed

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma logit_continuous_on: "continuous_on {0<..<1} logit"
proof -
  have "continuous_on {0<..<1} (\<lambda>p::real. ln (p / (1 - p)))"
    by (intro continuous_intros) auto
  moreover have "\<And>p::real. p \<in> {0<..<1} \<Longrightarrow> ln (p / (1 - p)) = logit p"
    by (simp add: logit_def)
  ultimately show ?thesis by (rule continuous_on_eq)
qed

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
theorem sigmoid_homeomorphism: "homeomorphism UNIV {0<..<1} sigmoid logit"
  unfolding homeomorphism_def
  using sigmoid_continuous_on logit_continuous_on sigmoid_bij_betw logit_bij_betw
  by (auto simp: logit_sigmoid_comp sigmoid_logit_comp bij_betw_def)

text \<open>Isomorphism of measurable spaces, with the unit interval carrying the subspace
  \(\sigma\)-algebra.\<close>

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma sigmoid_borel_measurable: "(sigmoid :: real \<Rightarrow> real) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI [OF sigmoid_continuous_on])

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
lemma logit_borel_measurable: "logit \<in> borel_measurable borel"
  unfolding logit_def by measurable

(* Supplementary logistic-function property for Section 6; no separate paper label. *)
theorem sigmoid_borel_iso:
  "(sigmoid :: real \<Rightarrow> real) \<in> borel \<rightarrow>\<^sub>M restrict_space borel {0<..<1}"
  "logit \<in> restrict_space borel {0<..<1} \<rightarrow>\<^sub>M borel"
proof -
  show "(sigmoid :: real \<Rightarrow> real) \<in> borel \<rightarrow>\<^sub>M restrict_space borel {0<..<1}"
    by (rule measurable_restrict_space2)
       (use sigmoid_borel_measurable sigmoid_pos sigmoid_less_1 in auto)
  show "logit \<in> restrict_space borel {0<..<1} \<rightarrow>\<^sub>M borel"
    by (rule measurable_restrict_space1 [OF logit_borel_measurable])
qed


definition softmax :: "real^'k \<Rightarrow> real^'k" where 
"softmax z = (\<chi> i. exp (z $ i) / (\<Sum> j\<in>UNIV. exp (z $ j)))"  

(* Section 6: hyperbolic-tangent example (unnumbered). *)
lemma tanh_sigmoid_relationship:
  "2 * sigmoid (2 * x::real) - 1 = tanh x"
proof -
  have exp_nz: "exp x \<noteq> 0"
    by (rule exp_not_eq_zero)
  have denom_nz: "1 + exp (- (2 * x)) \<noteq> 0"
    using add_pos_pos[OF zero_less_one exp_gt_zero[of "- (2 * x)"]] by simp
  have exp_prod: "exp x * exp (- (2 * x)) = exp (- x)"
    by (simp add: mult_exp_exp)
  have num: "exp x * (1 - exp (- (2 * x))) = exp x - exp (- x)"
    using exp_prod by (simp only: right_diff_distrib)
  have den: "exp x * (1 + exp (- (2 * x))) = exp x + exp (- x)"
    using exp_prod by (simp only: distrib_left)
  have "2 * sigmoid (2 * x) - 1 = 2 * (1 / (1 + exp (- (2 * x)))) - 1"
    by (simp only: inverse_eq_divide sigmoid_alt_def)
  also have "... = (2 - (1 + exp (- (2 * x)))) / (1 + exp (- (2 * x)))"
    using denom_nz by (simp add: field_simps)
  also have "... = (exp x * (1 - exp (- (2 * x)))) / (exp x * (1 + exp (- (2 * x))))"
    using nonzero_mult_divide_mult_cancel_left[OF exp_nz,
            of "1 - exp (- (2 * x))" "1 + exp (- (2 * x))"] by simp
  also have "... = (exp x - exp (- x)) / (exp x + exp (- x))"
    by (simp only: num den)
  also have "... = tanh x"
    by (simp only: tanh_altdef)
  finally show ?thesis .
qed

end
