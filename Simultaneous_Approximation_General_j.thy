section \<open>Node-level estimates for general \<open>j\<close>\<close>

theory Simultaneous_Approximation_General_j
  imports Forward_Difference_Consistency Simultaneous_Approximation_Rate
begin

text \<open>
  Groundwork for Theorem 4.1 at general \<open>j\<close> (Gap 3 of \<^file>\<open>SECTION_4_GAPS.md\<close>).  The \<open>j=1\<close>
  development in \<^file>\<open>Simultaneous_Approximation.thy\<close> rests on three node-level facts:

  \<^item> \<open>forward_diff_one_node_error\<close>: \<open>\<bar>\<Delta>\<^sup>1\<^sub>m f - f'(x\<^sub>m)\<bar> \<le> (C\<^sub>1/2)h\<close>;
  \<^item> \<open>forward_diff_one_node_diff_bound\<close>: \<open>\<bar>f'(x\<^sub>k) - f'(x\<^sub>k\<^sub>-\<^sub>1)\<bar> \<le> C\<^sub>1 h\<close>;
  \<^item> \<open>forward_diff_one_coefficient_error\<close>: the difference of the two, at adjacent nodes.

  Each is stated for \<open>j=1\<close> only, and each was derived from a bespoke \<open>j=1\<close> Taylor expansion.
  With \<open>forward_diff_consistency\<close> (\<^file>\<open>Forward_Difference_Consistency.thy\<close>, equation (4.4) for
  general \<open>j\<close>) all three generalise directly, with \<open>C\<^sub>1 = Sup\<bar>f''\<bar>\<close> replaced by
  \<open>L\<^sub>j = Sup\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar>\<close> throughout.  These are the facts every route to general-\<open>j\<close> Theorem 4.1 needs,
  independently of how its \<open>L\<^sub>i\<close> case split is organised.
\<close>

subsection \<open>The order-\<open>j+1\<close> supremum is a genuine bound\<close>

text \<open>
  \<open>C_k_on (Suc j) f U\<close> gives continuity of \<open>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<close> on \<open>U\<close> (its \<open>n=j\<close> clause), hence
  boundedness on the compact \<open>[a,b]\<close>.  The \<open>j=1\<close> development re-derives this inline at each of
  \<open>j=1,2,3,4\<close>; here it is done once.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma deriv_Sucj_bdd_above:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set" and j :: nat
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  shows "bdd_above ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
proof -
  have cont: "continuous_on U ((deriv ^^ Suc j) f)"
  proof -
    have all_n: "\<forall>n < Suc j. (deriv ^^ n) f differentiable_on U
                    \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
      using Ck unfolding C_k_on_def by simp
    have "j < Suc j" by simp
    with all_n show ?thesis by blast
  qed
  show ?thesis
    using a_lt_b cont ab_subset continuous_on_subset continuous_image_closed_interval
          continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
qed

(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma deriv_Sucj_le_Sup:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set" and j :: nat and t :: real
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  assumes t_in: "t \<in> {a..b}"
  shows "\<bar>(deriv ^^ Suc j) f t\<bar> \<le> Sup ((\<lambda>s. \<bar>(deriv ^^ Suc j) f s\<bar>) ` {a..b})"
  by (rule cSUP_upper[OF t_in deriv_Sucj_bdd_above[OF Ck ab_subset a_lt_b]])

(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma Ck_on_open: "C_k_on (Suc j) f U \<Longrightarrow> open U"
  unfolding C_k_on_def by (auto split: if_splits)

subsection \<open>\<open>f\<^sup>(\<^sup>j\<^sup>)\<close> is Lipschitz with constant \<open>L\<^sub>j = Sup\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar>\<close>\<close>

text \<open>
  The general-\<open>j\<close> counterpart of \<open>deriv_lipschitz_bound\<close> (\<^file>\<open>Derivative_Approximation.thy\<close>),
  which is the \<open>j=1\<close> case.  This is the \<open>L\<^sub>j\<close> of Theorem 4.2's statement.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma nth_deriv_lipschitz_bound:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set" and j :: nat and x y :: real
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  assumes x_in: "x \<in> {a..b}" and y_in: "y \<in> {a..b}"
  shows "\<bar>(deriv ^^ j) f x - (deriv ^^ j) f y\<bar>
           \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * \<bar>x - y\<bar>"
proof -
  define L where "L = Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  have key: "\<And>u v. \<lbrakk>u \<in> {a..b}; v \<in> {a..b}; u < v\<rbrakk>
               \<Longrightarrow> \<bar>(deriv ^^ j) f u - (deriv ^^ j) f v\<bar> \<le> L * (v - u)"
  proof -
    fix u v :: real
    assume u_in: "u \<in> {a..b}" and v_in: "v \<in> {a..b}" and u_lt_v: "u < v"
    have der: "\<And>t. \<lbrakk>u \<le> t; t \<le> v\<rbrakk>
                 \<Longrightarrow> DERIV ((deriv ^^ j) f) t :> (deriv ^^ Suc j) f t"
    proof -
      fix t :: real assume "u \<le> t" and "t \<le> v"
      then have t_ab: "t \<in> {a..b}" using u_in v_in by auto
      then have t_U: "t \<in> U" using ab_subset by blast
      show "DERIV ((deriv ^^ j) f) t :> (deriv ^^ Suc j) f t"
        using Ck_on_derivative_chain[OF Ck lessI t_U] by simp
    qed
    obtain z where z1: "u < z" and z2: "z < v"
      and zeq: "(deriv ^^ j) f v - (deriv ^^ j) f u = (v - u) * (deriv ^^ Suc j) f z"
      using MVT2[OF u_lt_v der] by blast
    have z_ab: "z \<in> {a..b}" using z1 z2 u_in v_in by auto
    have zL: "\<bar>(deriv ^^ Suc j) f z\<bar> \<le> L"
      unfolding L_def by (rule deriv_Sucj_le_Sup[OF Ck ab_subset a_lt_b z_ab])
    text \<open>Flip \<open>zeq\<close> explicitly: leaving the sign to \<open>simp\<close> with \<open>abs_minus_commute\<close> loops
      between the two orientations and closes neither.\<close>
    have flip: "(deriv ^^ j) f u - (deriv ^^ j) f v = (u - v) * (deriv ^^ Suc j) f z"
      using zeq by (simp add: algebra_simps)
    have uv: "\<bar>u - v\<bar> = v - u" using u_lt_v by simp
    have "\<bar>(deriv ^^ j) f u - (deriv ^^ j) f v\<bar> = \<bar>u - v\<bar> * \<bar>(deriv ^^ Suc j) f z\<bar>"
      unfolding flip by (rule abs_mult)
    also have "\<dots> = (v - u) * \<bar>(deriv ^^ Suc j) f z\<bar>"
      unfolding uv by (rule refl)
    also have "\<dots> \<le> (v - u) * L"
      using zL u_lt_v by (intro mult_left_mono) auto
    finally show "\<bar>(deriv ^^ j) f u - (deriv ^^ j) f v\<bar> \<le> L * (v - u)"
      by (simp add: mult.commute)
  qed
  show ?thesis
  proof (cases "x < y")
    case True
    then show ?thesis
      using key[OF x_in y_in True] unfolding L_def by simp
  next
    case ge: False
    show ?thesis
    proof (cases "y < x")
      case True
      then show ?thesis
        using key[OF y_in x_in True] unfolding L_def by (simp add: abs_minus_commute)
    next
      case False
      then have "x = y" using ge by simp
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>The three node-level estimates at general \<open>j\<close>\<close>

text \<open>
  Equation (4.4) at a partition node.  The cell \<open>[x\<^sub>m, x\<^sub>m\<^sub>+\<^sub>j]\<close> sits inside \<open>[a,b]\<close> exactly when
  \<open>m \<ge> 1\<close> and \<open>m+j \<le> N+1\<close> -- recall this project's indexing puts \<open>xs!0 = a-h\<close> outside \<open>[a,b]\<close>,
  so \<open>m \<ge> 1\<close> is the real content of the left constraint.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_node_error:
  fixes a b :: real and N j m :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes m_pos: "m \<ge> 1" and mj: "m + j \<le> N + 1"
  shows "\<bar>forward_diff f xs h j m - (deriv ^^ j) f (xs ! m)\<bar>
           \<le> real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have U_open: "open U" using Ck_on_open[OF Ck] .
  have m_in: "m \<in> {1..N+1}" using m_pos mj by auto
  have mj_in: "m + j \<in> {1..N+1}" using m_pos mj by auto
  have xm_ab: "xs ! m \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] m_in by blast
  have xmj_ab: "xs ! (m + j) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] mj_in by blast
  have cell_ab: "{xs ! m..xs ! (m + j)} \<subseteq> {a..b}"
    using xm_ab xmj_ab by auto
  have seg: "{xs ! m..xs ! (m + j)} \<subseteq> U"
    using cell_ab ab_subset by blast
  have bnd: "\<And>t. \<lbrakk>xs ! m \<le> t; t \<le> xs ! (m + j)\<rbrakk>
               \<Longrightarrow> \<bar>(deriv ^^ Suc j) f t\<bar> \<le> Sup ((\<lambda>s. \<bar>(deriv ^^ Suc j) f s\<bar>) ` {a..b})"
  proof -
    fix t :: real assume "xs ! m \<le> t" and "t \<le> xs ! (m + j)"
    then have "t \<in> {a..b}" using cell_ab by auto
    then show "\<bar>(deriv ^^ Suc j) f t\<bar> \<le> Sup ((\<lambda>s. \<bar>(deriv ^^ Suc j) f s\<bar>) ` {a..b})"
      by (rule deriv_Sucj_le_Sup[OF Ck ab_subset a_lt_b])
  qed
  show ?thesis
    by (rule forward_diff_consistency[OF h_def xs_def hpos mj U_open Ck seg bnd])
qed

text \<open>The general-\<open>j\<close> counterpart of \<open>forward_diff_one_node_diff_bound\<close>.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma nth_deriv_node_diff_bound:
  fixes a b :: real and N j k :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes k_range: "k \<in> {2..N}"
  shows "\<bar>(deriv ^^ j) f (xs ! k) - (deriv ^^ j) f (xs ! (k - 1))\<bar>
           \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have k_in: "k \<in> {1..N+1}" and km1_in: "k - 1 \<in> {1..N+1}"
    using k_range by auto
  have xk_ab: "xs ! k \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] k_in by blast
  have xkm1_ab: "xs ! (k - 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] km1_in by blast
  have step: "xs ! k - xs ! (k - 1) = h"
    using difference_of_adj_terms[OF h_def xs_def] k_range by auto
  have "\<bar>(deriv ^^ j) f (xs ! k) - (deriv ^^ j) f (xs ! (k - 1))\<bar>
          \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * \<bar>xs ! k - xs ! (k - 1)\<bar>"
    by (rule nth_deriv_lipschitz_bound[OF Ck ab_subset a_lt_b xk_ab xkm1_ab])
  also have "\<dots> = Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h"
    using step hpos by simp
  finally show ?thesis .
qed

text \<open>
  The general-\<open>j\<close> counterpart of \<open>forward_diff_one_coefficient_error\<close>: a \<open>G\<^sup>j\<^sub>N f\<close> coefficient
  differs from the corresponding \<open>f\<^sup>(\<^sup>j\<^sup>)\<close>-coefficient by at most twice the single-node bound.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_coefficient_error:
  fixes a b :: real and N j k :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes k_pos: "k \<ge> 1" and kj: "k + 1 + j \<le> N + 1"
  shows "\<bar>(forward_diff f xs h j (k + 1) - forward_diff f xs h j k)
           - ((deriv ^^ j) f (xs ! (k + 1)) - (deriv ^^ j) f (xs ! k))\<bar>
           \<le> 2 * (real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h)"
proof -
  have kj0: "k + j \<le> N + 1" using kj by simp
  have k1_pos: "k + 1 \<ge> 1" by simp
  have e1: "\<bar>forward_diff f xs h j k - (deriv ^^ j) f (xs ! k)\<bar>
              \<le> real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h"
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_pos kj0])
  have e2: "\<bar>forward_diff f xs h j (k + 1) - (deriv ^^ j) f (xs ! (k + 1))\<bar>
              \<le> real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h"
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k1_pos kj])
  have rearrange: "(forward_diff f xs h j (k + 1) - forward_diff f xs h j k)
                     - ((deriv ^^ j) f (xs ! (k + 1)) - (deriv ^^ j) f (xs ! k))
                   = (forward_diff f xs h j (k + 1) - (deriv ^^ j) f (xs ! (k + 1)))
                     - (forward_diff f xs h j k - (deriv ^^ j) f (xs ! k))"
    by simp
  show ?thesis
    unfolding rearrange using e1 e2 by linarith
qed

subsection \<open>The \<open>L\<^sub>i\<close> case split at general \<open>j\<close>\<close>

text \<open>
  The paper's \<open>L\<^sub>i\<close> (p.177, restated p.180) has \<^emph>\<open>four\<close> cases.  Translated into this project's
  indexing (\<open>xs!0 = x\<^sub>-\<^sub>1\<close>, so a paper index \<open>k\<close> is \<open>k+1\<close> here), and with the telescoping sums
  \<open>\<Sum>\<^sub>k\<^sub>=\<^sub>1\<^sup>m(\<Delta>\<^sup>j\<^sub>k f - \<Delta>\<^sup>j\<^sub>k\<^sub>-\<^sub>1 f) + \<Delta>\<^sup>j\<^sub>0 f = \<Delta>\<^sup>j\<^sub>m f\<close> already collapsed, they are:

  \<^item> \<^bold>\<open>Case 1\<close>, \<open>i \<in> {1,2}\<close>: \<open>\<Delta>\<^sup>j\<^sub>1 + (\<Delta>\<^sup>j\<^sub>3-\<Delta>\<^sup>j\<^sub>2)\<sigma>(w(x-x\<^sub>3)) + (\<Delta>\<^sup>j\<^sub>2-\<Delta>\<^sup>j\<^sub>1)\<sigma>(w(x-x\<^sub>2))\<close>;
  \<^item> \<^bold>\<open>Case 2\<close>, \<open>i \<in> {3..N-j}\<close>: \<open>\<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>1 + (\<Delta>\<^sup>j\<^sub>i-\<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>1)\<sigma>(w(x-x\<^sub>i)) + (\<Delta>\<^sup>j\<^sub>i\<^sub>+\<^sub>1-\<Delta>\<^sup>j\<^sub>i)\<sigma>(w(x-x\<^sub>i\<^sub>+\<^sub>1))\<close>;
  \<^item> \<^bold>\<open>Case 3\<close>, \<open>i = N-j+1\<close>: \<open>\<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j + (\<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1-\<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j)\<sigma>(w(x-x\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1))\<close>;
  \<^item> \<^bold>\<open>Case 4\<close>, \<open>i \<in> {N-j+2..N}\<close>: \<open>\<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1\<close>, with no \<open>\<sigma>\<close>-term at all.

  \<^bold>\<open>Case 4 is empty when \<open>j = 1\<close>\<close> (its range is \<open>{N+1..N}\<close>), which is exactly why the existing
  \<open>j=1\<close> development has only three cases and no analogue of it.  Cases 1, 2, 3 have the same
  shapes as its left-boundary, generic and right-boundary lemmas respectively.

  These bounds are derived here \<^emph>\<open>directly\<close> from (4.4) and the Lipschitz constant, rather than
  through an abstract modulus-of-continuity pair \<open>(\<delta>,\<eta>)\<close> as the \<open>j=1\<close> lemmas do.  That is both
  necessary (there is no \<open>j\<close>-generic \<open>\<eta>\<close> layer to instantiate) and sharper: at \<open>j=1\<close> Case 2 gives
  \<open>L\<^sub>1h(6S+3)\<close> where routing through \<open>\<eta>\<close> gives \<open>L\<^sub>1h(8S+3.5) + 3h(1+2S)\<close>.
\<close>

text \<open>Shared side conditions, proved once and reused by each case.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma sigma_abs_le_Sup:
  fixes \<sigma> :: "real \<Rightarrow> real" and t :: real
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  shows "\<bar>\<sigma> t\<bar> \<le> Sup ((\<lambda>s. \<bar>\<sigma> s\<bar>) ` UNIV)"
proof -
  have bdd: "bdd_above ((\<lambda>s. \<bar>\<sigma> s\<bar>) ` UNIV)"
    using bounded_sigmoidal unfolding bounded_function_def by simp
  show ?thesis by (intro cSUP_upper[OF UNIV_I bdd])
qed

(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma Lj_nonneg:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set" and j :: nat
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  shows "0 \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
proof -
  have ain: "a \<in> {a..b}" using a_lt_b by simp
  have "(0::real) \<le> \<bar>(deriv ^^ Suc j) f a\<bar>" by simp
  also have "\<dots> \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
    by (rule deriv_Sucj_le_Sup[OF Ck ab_subset a_lt_b ain])
  finally show ?thesis .
qed

text \<open>
  Case 2, the generic interior case.  The decomposition is the paper's own:
  \<open>L\<^sub>i - f\<^sup>(\<^sup>j\<^sup>)(x) = (\<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>1 - f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>i\<^sub>-\<^sub>1)) + (f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>i\<^sub>-\<^sub>1) - f\<^sup>(\<^sup>j\<^sup>)(x)) + c\<^sub>1\<sigma>\<^sub>1 + c\<^sub>2\<sigma>\<^sub>2\<close>, with each
  coefficient \<open>c\<close> bounded by \<open>(2j+1)L\<^sub>jh\<close> through (4.4) at both of its nodes plus one Lipschitz
  step between them.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_generic_L_bound_gen:
  fixes a b :: real and N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1"
  assumes i_lo: "i \<ge> 3" and i_hi: "i + j \<le> N"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h j (i - 1)
           + (forward_diff f xs h j i - forward_diff f xs h j (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
               * \<sigma> (w * (x - xs ! (i + 1))))
          - (deriv ^^ j) f x\<bar>
       \<le> Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have S_nn: "0 \<le> S"
    unfolding S_def using sigma_abs_le_Sup[OF bounded_sigmoidal, of 0] by simp

  text \<open>Index bookkeeping.  \<open>j \<ge> 1\<close> is what keeps \<open>i+1 \<le> N\<close>.\<close>
  have i_le_N: "i \<le> N" using i_hi j_pos by simp
  have i1_le_N: "i + 1 \<le> N" using i_hi j_pos by simp
  have im1_in: "i - 1 \<in> {1..N+1}" and i_in: "i \<in> {1..N+1}" and ip1_in: "i + 1 \<in> {1..N+1}"
    using i_lo i_le_N i1_le_N by auto
  have xim1_ab: "xs ! (i - 1) \<in> {a..b}" and xi_ab: "xs ! i \<in> {a..b}"
    and xip1_ab: "xs ! (i + 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] im1_in i_in ip1_in by blast+
  have x_ab: "x \<in> {a..b}" using x_in_cell xi_ab xip1_ab by auto

  text \<open>Geometry: \<open>x\<close> is at most \<open>2h\<close> to the right of \<open>x\<^sub>i\<^sub>-\<^sub>1\<close>.\<close>
  have gap1: "xs ! i - xs ! (i - 1) = h"
    using difference_of_terms[OF h_def xs_def] im1_in i_in i_lo by auto
  have gap2: "xs ! (i + 1) - xs ! (i - 1) = 2 * h"
    using difference_of_terms[OF h_def xs_def] im1_in ip1_in i_lo by auto
  have dist_x: "\<bar>xs ! (i - 1) - x\<bar> \<le> 2 * h"
    using x_in_cell gap1 gap2 hpos by auto

  text \<open>The three node errors, from (4.4).\<close>
  have im1_pos: "i - 1 \<ge> 1" using i_lo by simp
  have e_im1: "\<bar>forward_diff f xs h j (i - 1) - (deriv ^^ j) f (xs ! (i - 1))\<bar>
                 \<le> real j * Lj * h"
    unfolding Lj_def
    using forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset im1_pos] i_hi i_lo
    by simp
  have e_i: "\<bar>forward_diff f xs h j i - (deriv ^^ j) f (xs ! i)\<bar> \<le> real j * Lj * h"
    unfolding Lj_def
    using forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of i] i_lo i_hi
    by simp
  have e_ip1: "\<bar>forward_diff f xs h j (i + 1) - (deriv ^^ j) f (xs ! (i + 1))\<bar>
                 \<le> real j * Lj * h"
    unfolding Lj_def
    using forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of "i + 1"] i_lo i_hi
    by simp

  text \<open>The two node differences, from the Lipschitz bound.\<close>
  have i_2N: "i \<in> {2..N}" using i_lo i_le_N by simp
  have ip1_2N: "i + 1 \<in> {2..N}" using i1_le_N i_lo by simp
  have d_i: "\<bar>(deriv ^^ j) f (xs ! i) - (deriv ^^ j) f (xs ! (i - 1))\<bar> \<le> Lj * h"
    unfolding Lj_def
    using nth_deriv_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset i_2N] by simp
  have d_ip1: "\<bar>(deriv ^^ j) f (xs ! (i + 1)) - (deriv ^^ j) f (xs ! i)\<bar> \<le> Lj * h"
    unfolding Lj_def
    using nth_deriv_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset ip1_2N] by simp

  text \<open>Hence the two \<open>\<sigma>\<close>-coefficients.\<close>
  have c1: "\<bar>forward_diff f xs h j i - forward_diff f xs h j (i - 1)\<bar>
              \<le> (2 * real j + 1) * Lj * h"
    using e_im1 e_i d_i by (simp add: algebra_simps)
  have c2: "\<bar>forward_diff f xs h j (i + 1) - forward_diff f xs h j i\<bar>
              \<le> (2 * real j + 1) * Lj * h"
    using e_i e_ip1 d_ip1 by (simp add: algebra_simps)

  text \<open>And the two remaining terms.\<close>
  have tail: "\<bar>(deriv ^^ j) f (xs ! (i - 1)) - (deriv ^^ j) f x\<bar> \<le> Lj * (2 * h)"
  proof -
    have "\<bar>(deriv ^^ j) f (xs ! (i - 1)) - (deriv ^^ j) f x\<bar> \<le> Lj * \<bar>xs ! (i - 1) - x\<bar>"
      unfolding Lj_def
      by (rule nth_deriv_lipschitz_bound[OF Ck ab_subset a_lt_b xim1_ab x_ab])
    also have "\<dots> \<le> Lj * (2 * h)"
      using dist_x Lj_nn by (intro mult_left_mono) auto
    finally show ?thesis .
  qed

  text \<open>Assemble.\<close>
  have prod1: "\<bar>(forward_diff f xs h j i - forward_diff f xs h j (i - 1))
                  * \<sigma> (w * (x - xs ! i))\<bar>
                 \<le> (2 * real j + 1) * Lj * h * S"
  proof -
    have "\<bar>(forward_diff f xs h j i - forward_diff f xs h j (i - 1))
             * \<sigma> (w * (x - xs ! i))\<bar>
            = \<bar>forward_diff f xs h j i - forward_diff f xs h j (i - 1)\<bar>
              * \<bar>\<sigma> (w * (x - xs ! i))\<bar>"
      by (rule abs_mult)
    also have "\<dots> \<le> ((2 * real j + 1) * Lj * h) * S"
      using c1 sigma_abs_le_Sup[OF bounded_sigmoidal] S_nn
      unfolding S_def by (intro mult_mono) auto
    finally show ?thesis by simp
  qed
  have prod2: "\<bar>(forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                  * \<sigma> (w * (x - xs ! (i + 1)))\<bar>
                 \<le> (2 * real j + 1) * Lj * h * S"
  proof -
    have "\<bar>(forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
             * \<sigma> (w * (x - xs ! (i + 1)))\<bar>
            = \<bar>forward_diff f xs h j (i + 1) - forward_diff f xs h j i\<bar>
              * \<bar>\<sigma> (w * (x - xs ! (i + 1)))\<bar>"
      by (rule abs_mult)
    also have "\<dots> \<le> ((2 * real j + 1) * Lj * h) * S"
      using c2 sigma_abs_le_Sup[OF bounded_sigmoidal] S_nn
      unfolding S_def by (intro mult_mono) auto
    finally show ?thesis by simp
  qed

  have split: "(forward_diff f xs h j (i - 1)
                 + (forward_diff f xs h j i - forward_diff f xs h j (i - 1))
                     * \<sigma> (w * (x - xs ! i))
                 + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                     * \<sigma> (w * (x - xs ! (i + 1))))
                - (deriv ^^ j) f x
              = (forward_diff f xs h j (i - 1) - (deriv ^^ j) f (xs ! (i - 1)))
                + ((deriv ^^ j) f (xs ! (i - 1)) - (deriv ^^ j) f x)
                + (forward_diff f xs h j i - forward_diff f xs h j (i - 1))
                    * \<sigma> (w * (x - xs ! i))
                + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                    * \<sigma> (w * (x - xs ! (i + 1)))"
    by simp
  text \<open>
    The triangle inequality must be applied by hand here: \<open>simp add: algebra_simps\<close> distributes
    \<open>(A-B)\<sqdot>\<sigma>\<close> into \<open>A\<sigma>-B\<sigma>\<close> on both sides, after which the four bounds no longer match the goal's
    grouping.  \<open>linarith\<close> then finishes, treating each \<open>\<bar>\<dots>\<bar>\<close> as an atom.
  \<close>
  let ?t1 = "forward_diff f xs h j (i - 1) - (deriv ^^ j) f (xs ! (i - 1))"
  let ?t2 = "(deriv ^^ j) f (xs ! (i - 1)) - (deriv ^^ j) f x"
  let ?t3 = "(forward_diff f xs h j i - forward_diff f xs h j (i - 1))
               * \<sigma> (w * (x - xs ! i))"
  let ?t4 = "(forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
               * \<sigma> (w * (x - xs ! (i + 1)))"
  have a1: "\<bar>?t1 + ?t2\<bar> \<le> \<bar>?t1\<bar> + \<bar>?t2\<bar>" by (rule abs_triangle_ineq)
  have a2: "\<bar>?t1 + ?t2 + ?t3\<bar> \<le> \<bar>?t1 + ?t2\<bar> + \<bar>?t3\<bar>" by (rule abs_triangle_ineq)
  have a3: "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar> \<le> \<bar>?t1 + ?t2 + ?t3\<bar> + \<bar>?t4\<bar>" by (rule abs_triangle_ineq)
  have tri: "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar> \<le> \<bar>?t1\<bar> + \<bar>?t2\<bar> + \<bar>?t3\<bar> + \<bar>?t4\<bar>"
    using a1 a2 a3 by linarith
  have bound: "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar> \<le> Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
  proof -
    have "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar>
            \<le> real j * Lj * h + Lj * (2 * h)
              + (2 * real j + 1) * Lj * h * S + (2 * real j + 1) * Lj * h * S"
      using tri e_im1 tail prod1 prod2 by linarith
    also have "\<dots> = Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding split using bound .
qed

text \<open>
  Case 4, the far-right plateau: \<open>L\<^sub>i\<close> is the single value \<open>\<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1\<close>, with no \<open>\<sigma>\<close>-term, so the
  estimate is just (4.4) plus one Lipschitz step of length at most \<open>jh\<close>.  This case does not
  arise at \<open>j = 1\<close>.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_plateau_L_bound_gen:
  fixes a b :: real and N j i :: nat and h x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1" and jN: "j \<le> N"
  assumes i_lo: "i \<ge> N - j + 2" and i_hi: "i \<le> N"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  shows "\<bar>forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f x\<bar> \<le> 2 * real j * Lj * h"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])

  have m_pos: "N - j + 1 \<ge> 1" by simp
  have mj: "(N - j + 1) + j \<le> N + 1" using jN by simp
  have m_in: "N - j + 1 \<in> {1..N+1}" using jN by auto
  have i_in: "i \<in> {1..N+1}" and ip1_in: "i + 1 \<in> {1..N+1}"
    using i_lo i_hi by auto
  have xm_ab: "xs ! (N - j + 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] m_in by blast
  have xi_ab: "xs ! i \<in> {a..b}" and xip1_ab: "xs ! (i + 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] i_in ip1_in by blast+
  have x_ab: "x \<in> {a..b}" using x_in_cell xi_ab xip1_ab by auto

  text \<open>\<open>x\<close> lies to the right of \<open>x\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1\<close> and at most \<open>jh\<close> beyond it, since \<open>x \<le> xs!(N+1)\<close>.\<close>
  text \<open>\<open>difference_of_terms\<close> is stated as a \<open>\<forall>\<close>-implication, so \<open>auto\<close> will not instantiate it;
    each use below names its two indices explicitly.\<close>
  have m_le_i: "N - j + 1 \<le> i" using i_lo by simp
  have Np1_in: "N + 1 \<in> {1..N+1}" by simp
  have rj: "real (N - j + 1) = real N - real j + 1" using jN by simp
  have lower: "xs ! (N - j + 1) \<le> x"
  proof -
    have step: "xs ! i - xs ! (N - j + 1) = h * (real i - real (N - j + 1))"
      using difference_of_terms[OF h_def xs_def, of "N - j + 1" i] m_in i_in m_le_i by simp
    have "0 \<le> real i - real (N - j + 1)" using m_le_i by simp
    then have "0 \<le> xs ! i - xs ! (N - j + 1)"
      using step hpos by simp
    then show ?thesis using x_in_cell by simp
  qed
  have upper: "x \<le> xs ! (N + 1)"
  proof -
    have step: "xs ! (N + 1) - xs ! (i + 1) = h * (real (N + 1) - real (i + 1))"
      using difference_of_terms[OF h_def xs_def, of "i + 1" "N + 1"] ip1_in Np1_in i_hi by simp
    have "0 \<le> real (N + 1) - real (i + 1)" using i_hi by simp
    then have "0 \<le> xs ! (N + 1) - xs ! (i + 1)"
      using step hpos by simp
    then show ?thesis using x_in_cell by simp
  qed
  have span: "xs ! (N + 1) - xs ! (N - j + 1) = real j * h"
  proof -
    have step: "xs ! (N + 1) - xs ! (N - j + 1) = h * (real (N + 1) - real (N - j + 1))"
      using difference_of_terms[OF h_def xs_def, of "N - j + 1" "N + 1"] m_in Np1_in jN by simp
    have "real (N + 1) - real (N - j + 1) = real j"
      unfolding rj by simp
    then show ?thesis using step by (simp add: mult.commute)
  qed
  have dist_x: "\<bar>xs ! (N - j + 1) - x\<bar> \<le> real j * h"
    using lower upper span by simp

  have e_m: "\<bar>forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1))\<bar>
               \<le> real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset m_pos mj])
  have tail: "\<bar>(deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f x\<bar> \<le> Lj * (real j * h)"
  proof -
    have "\<bar>(deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f x\<bar>
            \<le> Lj * \<bar>xs ! (N - j + 1) - x\<bar>"
      unfolding Lj_def
      by (rule nth_deriv_lipschitz_bound[OF Ck ab_subset a_lt_b xm_ab x_ab])
    also have "\<dots> \<le> Lj * (real j * h)"
      using dist_x Lj_nn by (intro mult_left_mono) auto
    finally show ?thesis .
  qed
  have split: "forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f x
                 = (forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1)))
                   + ((deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f x)"
    by simp
  have bound: "\<bar>(forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1)))
                 + ((deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f x)\<bar>
                 \<le> 2 * real j * Lj * h"
  proof -
    have "\<bar>(forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1)))
             + ((deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f x)\<bar>
            \<le> \<bar>forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1))\<bar>
              + \<bar>(deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f x\<bar>"
      by (rule abs_triangle_ineq)
    also have "\<dots> \<le> real j * Lj * h + Lj * (real j * h)"
      using e_m tail by linarith
    also have "\<dots> = 2 * real j * Lj * h"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding split using bound .
qed

text \<open>
  Case 1, the left boundary.  Structurally identical to Case 2 with the index triple
  \<open>(i-1, i, i+1)\<close> replaced by the fixed \<open>(1, 2, 3)\<close>, so it lands on the same constant.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_left_L_bound_gen:
  fixes a b :: real and N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes i_in12: "i \<in> {1, 2}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h j 1
           + (forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))
           + (forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2)))
          - (deriv ^^ j) f x\<bar>
       \<le> Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have S_nn: "0 \<le> S"
    unfolding S_def using sigma_abs_le_Sup[OF bounded_sigmoidal, of 0] by simp

  have jN2: "j + 3 \<le> N" using N_gt by simp
  have one_in: "(1::nat) \<in> {1..N+1}" and two_in: "(2::nat) \<in> {1..N+1}"
    and three_in: "(3::nat) \<in> {1..N+1}"
    using jN2 by auto
  have x1_ab: "xs ! 1 \<in> {a..b}" and x2_ab: "xs ! 2 \<in> {a..b}" and x3_ab: "xs ! 3 \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] one_in two_in three_in by blast+

  have i_in: "i \<in> {1..N+1}" and ip1_in: "i + 1 \<in> {1..N+1}" using i_in12 jN2 by auto
  have xi_ab: "xs ! i \<in> {a..b}" and xip1_ab: "xs ! (i + 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] i_in ip1_in by blast+
  have x_ab: "x \<in> {a..b}" using x_in_cell xi_ab xip1_ab by auto

  text \<open>\<open>x\<close> lies between \<open>x\<^sub>1\<close> and \<open>x\<^sub>3\<close>, so within \<open>2h\<close> of \<open>x\<^sub>1\<close>.\<close>
  have span13: "xs ! 3 - xs ! 1 = 2 * h"
    using difference_of_terms[OF h_def xs_def, of 1 3] one_in three_in by simp
  have lower: "xs ! 1 \<le> x"
  proof -
    have "xs ! 1 \<le> xs ! i"
      using difference_of_terms[OF h_def xs_def, of 1 i] one_in i_in i_in12 hpos by auto
    then show ?thesis using x_in_cell by simp
  qed
  have upper: "x \<le> xs ! 3"
  proof -
    have "xs ! (i + 1) \<le> xs ! 3"
      using difference_of_terms[OF h_def xs_def, of "i + 1" 3] ip1_in three_in i_in12 hpos by auto
    then show ?thesis using x_in_cell by simp
  qed
  have dist_x: "\<bar>xs ! 1 - x\<bar> \<le> 2 * h" using lower upper span13 by simp

  have e1: "\<bar>forward_diff f xs h j 1 - (deriv ^^ j) f (xs ! 1)\<bar> \<le> real j * Lj * h"
    unfolding Lj_def
    using forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 1] jN2 by simp
  have e2: "\<bar>forward_diff f xs h j 2 - (deriv ^^ j) f (xs ! 2)\<bar> \<le> real j * Lj * h"
    unfolding Lj_def
    using forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 2] jN2 by simp
  have e3: "\<bar>forward_diff f xs h j 3 - (deriv ^^ j) f (xs ! 3)\<bar> \<le> real j * Lj * h"
    unfolding Lj_def
    using forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 3] jN2 by simp
  have two_2N: "(2::nat) \<in> {2..N}" and three_2N: "(3::nat) \<in> {2..N}" using jN2 by auto
  have d2: "\<bar>(deriv ^^ j) f (xs ! 2) - (deriv ^^ j) f (xs ! 1)\<bar> \<le> Lj * h"
    unfolding Lj_def
    using nth_deriv_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset two_2N] by simp
  have d3: "\<bar>(deriv ^^ j) f (xs ! 3) - (deriv ^^ j) f (xs ! 2)\<bar> \<le> Lj * h"
    unfolding Lj_def
    using nth_deriv_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset three_2N] by simp

  have c1: "\<bar>forward_diff f xs h j 2 - forward_diff f xs h j 1\<bar> \<le> (2 * real j + 1) * Lj * h"
    using e1 e2 d2 by (simp add: algebra_simps)
  have c2: "\<bar>forward_diff f xs h j 3 - forward_diff f xs h j 2\<bar> \<le> (2 * real j + 1) * Lj * h"
    using e2 e3 d3 by (simp add: algebra_simps)

  have tail: "\<bar>(deriv ^^ j) f (xs ! 1) - (deriv ^^ j) f x\<bar> \<le> Lj * (2 * h)"
  proof -
    have "\<bar>(deriv ^^ j) f (xs ! 1) - (deriv ^^ j) f x\<bar> \<le> Lj * \<bar>xs ! 1 - x\<bar>"
      unfolding Lj_def
      by (rule nth_deriv_lipschitz_bound[OF Ck ab_subset a_lt_b x1_ab x_ab])
    also have "\<dots> \<le> Lj * (2 * h)"
      using dist_x Lj_nn by (intro mult_left_mono) auto
    finally show ?thesis .
  qed

  have prod1: "\<bar>(forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))\<bar>
                 \<le> (2 * real j + 1) * Lj * h * S"
  proof -
    have "\<bar>(forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))\<bar>
            = \<bar>forward_diff f xs h j 3 - forward_diff f xs h j 2\<bar> * \<bar>\<sigma> (w * (x - xs ! 3))\<bar>"
      by (rule abs_mult)
    also have "\<dots> \<le> ((2 * real j + 1) * Lj * h) * S"
      using c2 sigma_abs_le_Sup[OF bounded_sigmoidal] S_nn
      unfolding S_def by (intro mult_mono) auto
    finally show ?thesis by simp
  qed
  have prod2: "\<bar>(forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2))\<bar>
                 \<le> (2 * real j + 1) * Lj * h * S"
  proof -
    have "\<bar>(forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2))\<bar>
            = \<bar>forward_diff f xs h j 2 - forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 2))\<bar>"
      by (rule abs_mult)
    also have "\<dots> \<le> ((2 * real j + 1) * Lj * h) * S"
      using c1 sigma_abs_le_Sup[OF bounded_sigmoidal] S_nn
      unfolding S_def by (intro mult_mono) auto
    finally show ?thesis by simp
  qed

  let ?t1 = "forward_diff f xs h j 1 - (deriv ^^ j) f (xs ! 1)"
  let ?t2 = "(deriv ^^ j) f (xs ! 1) - (deriv ^^ j) f x"
  let ?t3 = "(forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))"
  let ?t4 = "(forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2))"
  have split: "(forward_diff f xs h j 1
                 + (forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))
                 + (forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2)))
                - (deriv ^^ j) f x
              = ?t1 + ?t2 + ?t3 + ?t4"
    by simp
  have a1: "\<bar>?t1 + ?t2\<bar> \<le> \<bar>?t1\<bar> + \<bar>?t2\<bar>" by (rule abs_triangle_ineq)
  have a2: "\<bar>?t1 + ?t2 + ?t3\<bar> \<le> \<bar>?t1 + ?t2\<bar> + \<bar>?t3\<bar>" by (rule abs_triangle_ineq)
  have a3: "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar> \<le> \<bar>?t1 + ?t2 + ?t3\<bar> + \<bar>?t4\<bar>" by (rule abs_triangle_ineq)
  have bound: "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar> \<le> Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
  proof -
    have "\<bar>?t1 + ?t2 + ?t3 + ?t4\<bar>
            \<le> real j * Lj * h + Lj * (2 * h)
              + (2 * real j + 1) * Lj * h * S + (2 * real j + 1) * Lj * h * S"
      using a1 a2 a3 e1 tail prod1 prod2 by linarith
    also have "\<dots> = Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding split using bound .
qed

text \<open>
  Case 3, the single cell \<open>i = N-j+1\<close>, which carries only one \<open>\<sigma>\<close>-term and so loses one factor
  of \<open>(2j+1)S\<close> relative to Cases 1 and 2.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_right_L_bound_gen:
  fixes a b :: real and N j :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes x_in_cell: "x \<in> {xs ! (N - j + 1) .. xs ! (N - j + 2)}"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h j (N - j)
           + (forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
               * \<sigma> (w * (x - xs ! (N - j + 1))))
          - (deriv ^^ j) f x\<bar>
       \<le> Lj * h * ((2 * real j + 1) * S + real j + 2)"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have S_nn: "0 \<le> S"
    unfolding S_def using sigma_abs_le_Sup[OF bounded_sigmoidal, of 0] by simp

  have jN: "j \<le> N" using N_gt by simp
  have mlo: "N - j \<ge> 4" using N_gt by simp
  have m_in: "N - j \<in> {1..N+1}" and m1_in: "N - j + 1 \<in> {1..N+1}"
    and m2_in: "N - j + 2 \<in> {1..N+1}"
    using jN mlo j_pos by auto
  have xm_ab: "xs ! (N - j) \<in> {a..b}" and xm1_ab: "xs ! (N - j + 1) \<in> {a..b}"
    and xm2_ab: "xs ! (N - j + 2) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] m_in m1_in m2_in by blast+
  have x_ab: "x \<in> {a..b}" using x_in_cell xm1_ab xm2_ab by auto

  have span: "xs ! (N - j + 2) - xs ! (N - j) = 2 * h"
    using difference_of_terms[OF h_def xs_def, of "N - j" "N - j + 2"] m_in m2_in by simp
  have gap: "xs ! (N - j + 1) - xs ! (N - j) = h"
    using difference_of_terms[OF h_def xs_def, of "N - j" "N - j + 1"] m_in m1_in by simp
  have dist_x: "\<bar>xs ! (N - j) - x\<bar> \<le> 2 * h"
    using x_in_cell gap span hpos by auto

  have m_pos: "N - j \<ge> 1" using mlo by simp
  have m1_pos: "N - j + 1 \<ge> 1" by simp
  have mj: "(N - j) + j \<le> N + 1" using jN by simp
  have m1j: "(N - j + 1) + j \<le> N + 1" using jN by simp
  have e_m: "\<bar>forward_diff f xs h j (N - j) - (deriv ^^ j) f (xs ! (N - j))\<bar>
               \<le> real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset m_pos mj])
  have e_m1: "\<bar>forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1))\<bar>
                \<le> real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset m1_pos m1j])
  have m1_2N: "N - j + 1 \<in> {2..N}" using mlo jN j_pos by auto
  have d_m1: "\<bar>(deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f (xs ! (N - j))\<bar> \<le> Lj * h"
  proof -
    have "N - j + 1 - 1 = N - j" by simp
    then show ?thesis
      unfolding Lj_def
      using nth_deriv_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset m1_2N] by simp
  qed
  text \<open>Here \<open>simp add: algebra_simps\<close> does not close the three-term triangle inequality (it
    does in Case 2, where the indices normalise differently), so it is spelled out.\<close>
  have c1: "\<bar>forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j)\<bar>
              \<le> (2 * real j + 1) * Lj * h"
  proof -
    let ?u1 = "forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f (xs ! (N - j + 1))"
    let ?u2 = "(deriv ^^ j) f (xs ! (N - j + 1)) - (deriv ^^ j) f (xs ! (N - j))"
    let ?u3 = "(deriv ^^ j) f (xs ! (N - j)) - forward_diff f xs h j (N - j)"
    have dec: "forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j)
                 = ?u1 + ?u2 + ?u3"
      by simp
    have b1: "\<bar>?u1 + ?u2\<bar> \<le> \<bar>?u1\<bar> + \<bar>?u2\<bar>" by (rule abs_triangle_ineq)
    have b2: "\<bar>?u1 + ?u2 + ?u3\<bar> \<le> \<bar>?u1 + ?u2\<bar> + \<bar>?u3\<bar>" by (rule abs_triangle_ineq)
    have u3: "\<bar>?u3\<bar> \<le> real j * Lj * h"
      using e_m by (simp add: abs_minus_commute)
    have "\<bar>?u1 + ?u2 + ?u3\<bar> \<le> real j * Lj * h + Lj * h + real j * Lj * h"
      using b1 b2 e_m1 d_m1 u3 by linarith
    also have "\<dots> = (2 * real j + 1) * Lj * h"
      by (simp add: algebra_simps)
    finally show ?thesis unfolding dec .
  qed

  have tail: "\<bar>(deriv ^^ j) f (xs ! (N - j)) - (deriv ^^ j) f x\<bar> \<le> Lj * (2 * h)"
  proof -
    have "\<bar>(deriv ^^ j) f (xs ! (N - j)) - (deriv ^^ j) f x\<bar> \<le> Lj * \<bar>xs ! (N - j) - x\<bar>"
      unfolding Lj_def
      by (rule nth_deriv_lipschitz_bound[OF Ck ab_subset a_lt_b xm_ab x_ab])
    also have "\<dots> \<le> Lj * (2 * h)"
      using dist_x Lj_nn by (intro mult_left_mono) auto
    finally show ?thesis .
  qed

  have prod1: "\<bar>(forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
                  * \<sigma> (w * (x - xs ! (N - j + 1)))\<bar>
                 \<le> (2 * real j + 1) * Lj * h * S"
  proof -
    have "\<bar>(forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
             * \<sigma> (w * (x - xs ! (N - j + 1)))\<bar>
            = \<bar>forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j)\<bar>
              * \<bar>\<sigma> (w * (x - xs ! (N - j + 1)))\<bar>"
      by (rule abs_mult)
    also have "\<dots> \<le> ((2 * real j + 1) * Lj * h) * S"
      using c1 sigma_abs_le_Sup[OF bounded_sigmoidal] S_nn
      unfolding S_def by (intro mult_mono) auto
    finally show ?thesis by simp
  qed

  let ?t1 = "forward_diff f xs h j (N - j) - (deriv ^^ j) f (xs ! (N - j))"
  let ?t2 = "(deriv ^^ j) f (xs ! (N - j)) - (deriv ^^ j) f x"
  let ?t3 = "(forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
               * \<sigma> (w * (x - xs ! (N - j + 1)))"
  have split: "(forward_diff f xs h j (N - j)
                 + (forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
                     * \<sigma> (w * (x - xs ! (N - j + 1))))
                - (deriv ^^ j) f x
              = ?t1 + ?t2 + ?t3"
    by simp
  have a1: "\<bar>?t1 + ?t2\<bar> \<le> \<bar>?t1\<bar> + \<bar>?t2\<bar>" by (rule abs_triangle_ineq)
  have a2: "\<bar>?t1 + ?t2 + ?t3\<bar> \<le> \<bar>?t1 + ?t2\<bar> + \<bar>?t3\<bar>" by (rule abs_triangle_ineq)
  have bound: "\<bar>?t1 + ?t2 + ?t3\<bar> \<le> Lj * h * ((2 * real j + 1) * S + real j + 2)"
  proof -
    have "\<bar>?t1 + ?t2 + ?t3\<bar>
            \<le> real j * Lj * h + Lj * (2 * h) + (2 * real j + 1) * Lj * h * S"
      using a1 a2 e_m tail prod1 by linarith
    also have "\<dots> = Lj * h * ((2 * real j + 1) * S + real j + 2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding split using bound .
qed

subsection \<open>The \<open>I\<^sub>1\<close> side: \<open>G\<^sup>j\<^sub>N f\<close> against \<open>L\<^sub>i\<close>\<close>

text \<open>
  The telescoping identity behind \<open>I\<^sub>1 = \<bar>G\<^sup>j\<^sub>N f(x) - L\<^sub>i(x)\<bar>\<close>, at general \<open>j\<close>.  This layer is
  purely algebraic -- it needs no hypothesis about \<open>f\<close>, \<open>\<sigma>\<close> or the partition at all, only index
  arithmetic -- so it is stated with none.

  Reindexing (4.3)'s sum \<open>k \<in> {1..N-j}\<close> by \<open>m = k+1\<close> puts \<open>G\<^sup>j\<^sub>N f\<close> in the shape
  \<open>\<Sum>\<^sub>m\<^sub>\<in>\<^sub>{\<^sub>2\<^sub>.\<^sub>.\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1\<^sub>}(\<Delta>\<^sup>j\<^sub>m-\<Delta>\<^sup>j\<^sub>m\<^sub>-\<^sub>1)\<sigma>\<^sub>m + \<Delta>\<^sup>j\<^sub>1\<sigma>\<^sub>0\<close>; \<open>L\<^sub>i\<close>'s leading \<open>\<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>1\<close> telescopes into the initial segment
  of that sum, and its two \<open>\<sigma>\<close>-terms cancel the \<open>m = i, i+1\<close> terms exactly.  What survives is the
  three-part remainder below: the nodes left of the active cell carry \<open>\<sigma>\<^sub>m - 1\<close>, those right of it
  carry \<open>\<sigma>\<^sub>m\<close>, and both are what the \<open>\<sigma>\<close>-saturation hypothesis drives to \<open>1/N\<close>.

  Only the upper summation limit differs from the \<open>j=1\<close> case: \<open>N-j+1\<close> in place of \<open>N\<close>.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_I1_generic_decomp_gen:
  fixes N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes i_lo: "i \<ge> 3" and i_hi: "i + j \<le> N"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j (i - 1)
             + (forward_diff f xs h j i - forward_diff f xs h j (i - 1)) * \<sigma> (w * (x - xs ! i))
             + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                 * \<sigma> (w * (x - xs ! (i + 1))))\<bar>
       \<le> (\<Sum>k=2..i - 1. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
              * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
         + \<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
         + (\<Sum>k=i+2..N-j+1. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
              * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
proof -
  define Df where "Df = (\<lambda>k. forward_diff f xs h j k)"
  have i_le: "i + 1 \<le> N - j + 1" using i_hi by simp

  text \<open>Reindex (4.3)'s sum from \<open>k \<in> {1..N-j}\<close> (shifted by \<open>k+1\<close>) to \<open>m \<in> {2..N-j+1}\<close>.\<close>
  have Gnet_eq: "Gj_network \<sigma> f xs h N j w x
      = (\<Sum>m=2..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        + Df 1 * \<sigma> (w * (x - xs ! 0))"
  proof -
    have "(\<Sum>k\<in>{1..N-j}. (Df (k + 1) - Df k) * \<sigma> (w * (x - xs ! (k + 1))))
        = (\<Sum>m\<in>{2..N-j+1}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>m. m - 1" "\<lambda>k. k + 1"]) auto
    then show ?thesis
      unfolding Gj_network_def Df_def by simp
  qed

  text \<open>Telescoping: the raw sum from \<open>2\<close> to \<open>i-1\<close>, plus \<open>\<Delta>\<^sup>j\<^sub>1\<close>, collapses to \<open>\<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>1\<close>.\<close>
  have telescope_shift: "(\<Sum>k=2..i - 1. Df k - Df (k - 1)) + Df 1 = Df (i - 1)"
  proof -
    have full: "(\<Sum>k=1..i - 1. Df k - Df (k - 1)) + Df 0 = Df (i - 1)"
      unfolding Df_def using forward_diff_telescope[of f xs h j "i - 1"] .
    have split: "(\<Sum>k=1..i - 1. Df k - Df (k - 1))
        = (Df 1 - Df 0) + (\<Sum>k=2..i - 1. Df k - Df (k - 1))"
      using i_lo by (subst sum.atLeast_Suc_atMost) (auto simp add: eval_nat_numeral)
    from full split show ?thesis by linarith
  qed

  have disjoint: "{2..i - 1} \<inter> {i..N-j+1} = {}"
    by auto
  have union: "{2..i - 1} \<union> {i..N-j+1} = {2..N-j+1}"
    using i_lo i_le by auto
  have sum_of_terms:
    "(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
     + (\<Sum>k=i..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
     = (\<Sum>k=2..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
  proof -
    have "(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
       + (\<Sum>k=i..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
       = (\<Sum>k\<in>{2..i - 1} \<union> {i..N-j+1}. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
      by (rule sum.union_disjoint[symmetric]) (auto simp add: disjoint)
    then show ?thesis
      using union by simp
  qed

  have step1: "Gj_network \<sigma> f xs h N j w x
      - (Df (i - 1)
         + (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
         + (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1))))
    = ((\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
       - (\<Sum>k=2..i - 1. Df k - Df (k - 1)))
      + (\<Sum>k=i..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
      + Df 1 * \<sigma> (w * (x - xs ! 0))
      - Df 1
      - (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
      - (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1)))"
    unfolding Gnet_eq sum_of_terms[symmetric] telescope_shift[symmetric] by simp

  have peel1: "(\<Sum>k=i..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
      = (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
        + (\<Sum>k=i+1..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
    using i_le by (subst sum.atLeast_Suc_atMost) auto
  have peel2: "(\<Sum>k=i+1..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
      = (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1)))
        + (\<Sum>k=i+2..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
    using i_le i_lo by (subst sum.atLeast_Suc_atMost) auto

  have step2: "Gj_network \<sigma> f xs h N j w x
      - (Df (i - 1)
         + (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
         + (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1))))
    = (\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)
      + (\<Sum>k=i+2..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
    unfolding step1 peel1 peel2
    by (simp add: sum_subtractf right_diff_distrib' left_diff_distrib')

  have abs_bound: "\<bar>(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)
      + (\<Sum>k=i+2..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))\<bar>
    \<le> (\<Sum>k=2..i - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
      + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
      + (\<Sum>k=i+2..N-j+1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
  proof -
    have t1: "\<bar>(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))\<bar>
        \<le> (\<Sum>k=2..i - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)"
      by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
    have t2: "\<bar>Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar> = \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
      by (simp add: abs_mult)
    have t3: "\<bar>(\<Sum>k=i+2..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))\<bar>
        \<le> (\<Sum>k=i+2..N-j+1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
      by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
    have tri: "\<And>p q r::real. \<bar>p + q + r\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar> + \<bar>r\<bar>"
    proof -
      fix p q r :: real
      have "\<bar>p + q + r\<bar> \<le> \<bar>p + q\<bar> + \<bar>r\<bar>" by (rule abs_triangle_ineq)
      moreover have "\<bar>p + q\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar>" by (rule abs_triangle_ineq)
      ultimately show "\<bar>p + q + r\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar> + \<bar>r\<bar>" by linarith
    qed
    show ?thesis
      using tri[of "(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))"
                   "Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
                   "(\<Sum>k=i+2..N-j+1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"]
            t1 t2 t3
      by linarith
  qed
  show ?thesis
    using Df_def abs_bound step2 by presburger
qed

subsection \<open>Per-term bounds for the \<open>I\<^sub>1\<close> sums\<close>

text \<open>
  A node-gap formula valid at \<^emph>\<open>every\<close> index of the extended partition, including \<open>0\<close>.
  \<open>difference_of_terms\<close> (\<^file>\<open>Partition_Facts.thy\<close>) covers only \<open>{1..N+1}\<close> and only in increasing
  order, but the \<open>I\<^sub>1\<close> decomposition's \<open>\<Delta>\<^sup>j\<^sub>1\<sigma>\<^sub>0\<close> term needs the node \<open>xs!0 = a-h\<close>, and the
  right-hand sum needs gaps in decreasing order.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma node_gap_general:
  fixes a b h :: real and N p q :: nat and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes p_in: "p \<in> {0..N+1}" and q_in: "q \<in> {0..N+1}"
  shows "xs ! q - xs ! p = (real q - real p) * h"
proof -
  have "xs ! q = a + (real q - 1) * h" using xs_els[OF h_def xs_def] q_in by blast
  moreover have "xs ! p = a + (real p - 1) * h" using xs_els[OF h_def xs_def] p_in by blast
  ultimately show ?thesis by (simp add: algebra_simps)
qed

text \<open>\<open>Sup\<bar>f\<^sup>(\<^sup>j\<^sup>)\<bar>\<close> is a genuine bound too -- \<open>C_k_on (Suc j)\<close> makes \<open>f\<^sup>(\<^sup>j\<^sup>)\<close> differentiable, hence
  continuous, on \<open>U\<close>.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma deriv_j_bdd_above:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set" and j :: nat
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  shows "bdd_above ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
proof -
  have diff: "(deriv ^^ j) f differentiable_on U"
  proof -
    have all_n: "\<forall>n < Suc j. (deriv ^^ n) f differentiable_on U
                    \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
      using Ck unfolding C_k_on_def by simp
    have "j < Suc j" by simp
    with all_n show ?thesis by blast
  qed
  have cont: "continuous_on U ((deriv ^^ j) f)"
    using diff by (rule differentiable_imp_continuous_on)
  show ?thesis
    using a_lt_b cont ab_subset continuous_on_subset continuous_image_closed_interval
          continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
qed

(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma deriv_j_le_Sup:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set" and j :: nat and t :: real
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  assumes t_in: "t \<in> {a..b}"
  shows "\<bar>(deriv ^^ j) f t\<bar> \<le> Sup ((\<lambda>s. \<bar>(deriv ^^ j) f s\<bar>) ` {a..b})"
  by (rule cSUP_upper[OF t_in deriv_j_bdd_above[OF Ck ab_subset a_lt_b]])

text \<open>
  The uniform per-term bound the \<open>I\<^sub>1\<close> sums need: every adjacent pair of \<open>\<Delta>\<^sup>j\<close>-values in range
  differs by at most \<open>(2j+1)L\<^sub>jh\<close>, regardless of where \<open>k\<close> sits relative to the active cell.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_adjacent_bound_gen:
  fixes a b :: real and N j k :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1"
  assumes k_lo: "k \<ge> 2" and k_hi: "k \<le> N - j + 1" and jN: "j \<le> N"
  shows "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
           \<le> (2 * real j + 1) * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h"
proof -
  define Lj where "Lj = Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  have km1_pos: "k - 1 \<ge> 1" using k_lo by simp
  have k_pos: "k \<ge> 1" using k_lo by simp
  have kj: "k + j \<le> N + 1" using k_hi jN by simp
  have km1j: "(k - 1) + j \<le> N + 1" using kj by simp
  have k_2N: "k \<in> {2..N}" using k_lo k_hi j_pos jN by auto
  have e_k: "\<bar>forward_diff f xs h j k - (deriv ^^ j) f (xs ! k)\<bar> \<le> real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_pos kj])
  have e_km1: "\<bar>forward_diff f xs h j (k - 1) - (deriv ^^ j) f (xs ! (k - 1))\<bar>
                 \<le> real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset km1_pos km1j])
  have d_k: "\<bar>(deriv ^^ j) f (xs ! k) - (deriv ^^ j) f (xs ! (k - 1))\<bar> \<le> Lj * h"
    unfolding Lj_def
    by (rule nth_deriv_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_2N])
  let ?u1 = "forward_diff f xs h j k - (deriv ^^ j) f (xs ! k)"
  let ?u2 = "(deriv ^^ j) f (xs ! k) - (deriv ^^ j) f (xs ! (k - 1))"
  let ?u3 = "(deriv ^^ j) f (xs ! (k - 1)) - forward_diff f xs h j (k - 1)"
  have dec: "forward_diff f xs h j k - forward_diff f xs h j (k - 1) = ?u1 + ?u2 + ?u3"
    by simp
  have b1: "\<bar>?u1 + ?u2\<bar> \<le> \<bar>?u1\<bar> + \<bar>?u2\<bar>" by (rule abs_triangle_ineq)
  have b2: "\<bar>?u1 + ?u2 + ?u3\<bar> \<le> \<bar>?u1 + ?u2\<bar> + \<bar>?u3\<bar>" by (rule abs_triangle_ineq)
  have u3: "\<bar>?u3\<bar> \<le> real j * Lj * h" using e_km1 by (simp add: abs_minus_commute)
  have "\<bar>?u1 + ?u2 + ?u3\<bar> \<le> real j * Lj * h + Lj * h + real j * Lj * h"
    using b1 b2 e_k d_k u3 by linarith
  also have "\<dots> = (2 * real j + 1) * Lj * h" by (simp add: algebra_simps)
  finally show ?thesis unfolding dec Lj_def .
qed

text \<open>The lone \<open>\<Delta>\<^sup>j\<^sub>1\<close> term of the decomposition, bounded by (4.4) plus \<open>\<parallel>f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity>\<close>.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_one_term_bound_gen:
  fixes a b :: real and N j :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes jN: "j \<le> N"
  shows "\<bar>forward_diff f xs h j 1\<bar>
           \<le> real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * h
             + Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
proof -
  define Lj where "Lj = Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  define Mj where "Mj = Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  have one_in: "(1::nat) \<in> {1..N+1}" using N_pos by simp
  have x1_ab: "xs ! 1 \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] one_in by blast
  have onej: "1 + j \<le> N + 1" using jN by simp
  have e1: "\<bar>forward_diff f xs h j 1 - (deriv ^^ j) f (xs ! 1)\<bar> \<le> real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset _ onej]) simp
  have d1: "\<bar>(deriv ^^ j) f (xs ! 1)\<bar> \<le> Mj"
    unfolding Mj_def by (rule deriv_j_le_Sup[OF Ck ab_subset a_lt_b x1_ab])
  have tri: "\<bar>forward_diff f xs h j 1\<bar>
               \<le> \<bar>forward_diff f xs h j 1 - (deriv ^^ j) f (xs ! 1)\<bar>
                 + \<bar>(deriv ^^ j) f (xs ! 1)\<bar>"
    using abs_triangle_ineq[of "forward_diff f xs h j 1 - (deriv ^^ j) f (xs ! 1)"
                               "(deriv ^^ j) f (xs ! 1)"]
    by simp
  show ?thesis
    unfolding Lj_def[symmetric] Mj_def[symmetric]
    using tri e1 d1 by linarith
qed

subsection \<open>Reaching the \<open>\<sigma>\<close>-saturation hypothesis\<close>

text \<open>
  Nodes strictly left of the active cell are at least \<open>h\<close> to the left of \<open>x\<close>, and nodes at least
  two steps right of it at least \<open>h\<close> to the right -- which is exactly what
  \<open>sigmoidal_uniform_approximation\<close>'s two clauses consume.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma sat_gap_left:
  fixes a b h x :: real and N i k :: nat and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes hpos: "0 < h"
  assumes i_in: "i \<in> {0..N+1}" and k_in: "k \<in> {0..N+1}"
  assumes k_lt: "k + 1 \<le> i"
  assumes x_ge: "xs ! i \<le> x"
  shows "h \<le> x - xs ! k"
proof -
  have gap: "xs ! i - xs ! k = (real i - real k) * h"
    by (rule node_gap_general[OF h_def xs_def k_in i_in])
  have one_le: "1 \<le> real i - real k" using k_lt by simp
  have "1 * h \<le> (real i - real k) * h"
    using one_le hpos by (intro mult_right_mono) auto
  then show ?thesis using gap x_ge by simp
qed

(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma sat_gap_right:
  fixes a b h x :: real and N i k :: nat and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes hpos: "0 < h"
  assumes i1_in: "i + 1 \<in> {0..N+1}" and k_in: "k \<in> {0..N+1}"
  assumes k_ge: "i + 2 \<le> k"
  assumes x_le: "x \<le> xs ! (i + 1)"
  shows "x - xs ! k \<le> - h"
proof -
  have gap: "xs ! (i + 1) - xs ! k = (real (i + 1) - real k) * h"
    by (rule node_gap_general[OF h_def xs_def k_in i1_in])
  have le_m1: "real (i + 1) - real k \<le> - 1" using k_ge by simp
  have "(real (i + 1) - real k) * h \<le> - 1 * h"
    using le_m1 hpos by (intro mult_right_mono) auto
  then show ?thesis using gap x_le by simp
qed

subsection \<open>\<open>I\<^sub>1\<close> at an explicit \<open>1/N\<close> rate, generic case\<close>

text \<open>
  Combining the decomposition, the per-term bounds and the saturation clause.  Both surviving
  sums have every term below \<open>(2j+1)L\<^sub>jh/N\<close>, and their index sets are disjoint subsets of a range
  of length at most \<open>N\<close>, so together they contribute at most \<open>(2j+1)L\<^sub>jh = (2j+1)L\<^sub>j(b-a)/N\<close>.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_I1_generic_rate_gen:
  fixes a b :: real and N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes i_lo: "i \<ge> 3" and i_hi: "i + j \<le> N"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j (i - 1)
             + (forward_diff f xs h j i - forward_diff f xs h j (i - 1)) * \<sigma> (w * (x - xs ! i))
             + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                 * \<sigma> (w * (x - xs ! (i + 1))))\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have jN: "j \<le> N" using N_gt by simp
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have Mj_nn: "0 \<le> Mj"
  proof -
    have ain: "a \<in> {a..b}" using a_lt_b by simp
    have "(0::real) \<le> \<bar>(deriv ^^ j) f a\<bar>" by simp
    also have "\<dots> \<le> Mj" unfolding Mj_def by (rule deriv_j_le_Sup[OF Ck ab_subset a_lt_b ain])
    finally show ?thesis .
  qed
  have C_nn: "0 \<le> (2 * real j + 1) * Lj * h" using Lj_nn hpos by simp
  have invN_nn: "0 \<le> 1 / real N" using N_pos by simp

  have i_in01: "i \<in> {0..N+1}" and ip1_in01: "i + 1 \<in> {0..N+1}"
    using i_lo i_hi by auto
  have x_ge: "xs ! i \<le> x" and x_le: "x \<le> xs ! (i + 1)" using x_in_cell by auto

  text \<open>Every term of the left sum.\<close>
  have term1: "\<And>k. k \<in> {2..i - 1}
      \<Longrightarrow> \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
  proof -
    fix k :: nat assume k_in: "k \<in> {2..i - 1}"
    have k_lo: "k \<ge> 2" and k_up: "k \<le> i - 1" using k_in by auto
    have k_in01: "k \<in> {0..N+1}" using k_up i_lo i_hi by auto
    have k_lt_N2: "k < N + 2" using k_up i_lo i_hi by auto
    have k1i: "k + 1 \<le> i" using k_up i_lo by simp
    have gap: "h \<le> x - xs ! k"
      by (rule sat_gap_left[OF h_def xs_def hpos i_in01 k_in01 k1i x_ge])
    have sat_k: "\<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> \<le> 1 / real N"
      using sat k_lt_N2 gap by fastforce
    have k_hi': "k \<le> N - j + 1" using k_up i_hi by simp
    have coef: "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                  \<le> (2 * real j + 1) * Lj * h"
      unfolding Lj_def
      by (rule forward_diff_adjacent_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset
            j_pos k_lo k_hi' jN])
    show "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
      using coef sat_k C_nn by (intro mult_mono) auto
  qed

  text \<open>Every term of the right sum.\<close>
  have term3: "\<And>k. k \<in> {i + 2..N - j + 1}
      \<Longrightarrow> \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! k))\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
  proof -
    fix k :: nat assume k_in: "k \<in> {i + 2..N - j + 1}"
    have k_lo: "i + 2 \<le> k" and k_up: "k \<le> N - j + 1" using k_in by auto
    have k_ge2: "k \<ge> 2" using k_lo i_lo by simp
    have k_in01: "k \<in> {0..N+1}" using k_up jN by auto
    have k_lt_N2: "k < N + 2" using k_up jN by simp
    have gap: "x - xs ! k \<le> - h"
      by (rule sat_gap_right[OF h_def xs_def hpos ip1_in01 k_in01 k_lo x_le])
    have sat_k: "\<bar>\<sigma> (w * (x - xs ! k))\<bar> \<le> 1 / real N"
      using sat k_lt_N2 gap by fastforce
    have coef: "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                  \<le> (2 * real j + 1) * Lj * h"
      unfolding Lj_def
      by (rule forward_diff_adjacent_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset
            j_pos k_ge2 k_up jN])
    show "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! k))\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
      using coef sat_k C_nn by (intro mult_mono) auto
  qed

  have sum1: "(\<Sum>k=2..i - 1. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                 * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
              \<le> real (card {2..i - 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))"
    using term1 by (rule sum_bounded_above)
  have sum3: "(\<Sum>k=i+2..N - j + 1. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                 * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)
              \<le> real (card {i + 2..N - j + 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))"
    using term3 by (rule sum_bounded_above)

  text \<open>The \<open>\<Delta>\<^sup>j\<^sub>1\<sigma>\<^sub>0\<close> term.\<close>
  have zero_in01: "(0::nat) \<in> {0..N+1}" by simp
  have zero_lt: "(0::nat) < N + 2" by simp
  have zero1i: "(0::nat) + 1 \<le> i" using i_lo by simp
  have gap0: "h \<le> x - xs ! 0"
    by (rule sat_gap_left[OF h_def xs_def hpos i_in01 zero_in01 zero1i x_ge])
  have sat0: "\<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar> \<le> 1 / real N"
    using sat zero_lt gap0 by fastforce
  have df1: "\<bar>forward_diff f xs h j 1\<bar> \<le> real j * Lj * h + Mj"
    unfolding Lj_def Mj_def
    by (rule forward_diff_one_term_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset jN])
  have df1_nn: "0 \<le> real j * Lj * h + Mj" using Lj_nn Mj_nn hpos by simp
  have mid: "\<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
               \<le> (real j * Lj * h + Mj) * (1 / real N)"
    using df1 sat0 df1_nn by (intro mult_mono) auto

  text \<open>The two index sets together have at most \<open>N\<close> elements.\<close>
  have card_bound: "real (card {2..i - 1}) + real (card {i + 2..N - j + 1}) \<le> real N"
  proof -
    have "card {2..i - 1} + card {i + 2..N - j + 1} \<le> N"
      using i_lo i_hi jN by simp
    then show ?thesis by (simp add: of_nat_mono flip: of_nat_add)
  qed

  have sums_bound: "real (card {2..i - 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))
                    + real (card {i + 2..N - j + 1})
                        * ((2 * real j + 1) * Lj * h * (1 / real N))
                    \<le> (2 * real j + 1) * Lj * (b - a) / real N"
  proof -
    have Cinv_nn: "0 \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
      using C_nn invN_nn by simp
    have "real (card {2..i - 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))
          + real (card {i + 2..N - j + 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))
        = (real (card {2..i - 1}) + real (card {i + 2..N - j + 1}))
            * ((2 * real j + 1) * Lj * h * (1 / real N))"
      by (simp add: algebra_simps add_divide_distrib)
    also have "\<dots> \<le> real N * ((2 * real j + 1) * Lj * h * (1 / real N))"
      using card_bound Cinv_nn by (rule mult_right_mono)
    also have "\<dots> = (2 * real j + 1) * Lj * h"
      using N_pos by simp
    also have "\<dots> = (2 * real j + 1) * Lj * (b - a) / real N"
      unfolding h_def by simp
    finally show ?thesis .
  qed

  have decomp: "\<bar>Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j (i - 1)
             + (forward_diff f xs h j i - forward_diff f xs h j (i - 1)) * \<sigma> (w * (x - xs ! i))
             + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                 * \<sigma> (w * (x - xs ! (i + 1))))\<bar>
       \<le> (\<Sum>k=2..i - 1. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
              * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
         + \<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
         + (\<Sum>k=i+2..N-j+1. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
              * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
    by (rule forward_diff_I1_generic_decomp_gen[OF i_lo i_hi])

  have final_eq: "(2 * real j + 1) * Lj * (b - a) / real N + (real j * Lj * h + Mj) * (1 / real N)
                    = ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
    by (simp add: add_divide_distrib)
  show ?thesis
    using decomp sum1 sum3 mid sums_bound final_eq by linarith
qed

subsection \<open>The two halves joined: the generic case at general \<open>j\<close>\<close>

text \<open>
  \<open>\<bar>G\<^sup>j\<^sub>N f(x) - f\<^sup>(\<^sup>j\<^sup>)(x)\<bar> \<le> I\<^sub>1 + J\<^sub>2\<close> for \<open>x\<close> in an interior cell, with both halves now explicit.
  Since \<open>h = (b-a)/N\<close> the \<open>J\<^sub>2\<close> part is \<open>O(1/N)\<close> too, so the whole estimate collapses into a single
  constant over \<open>N\<close> -- the general-\<open>j\<close> analogue of what Theorem 4.2 asserts, for the range
  \<open>i \<in> {3..N-j}\<close> (the paper's Case 2, which is where it confines its own \<open>J\<^sub>1\<close> estimate).

  The remaining three cases need only the same triangle step against
  \<open>forward_diff_{left,right,plateau}_L_bound_gen\<close> once their \<open>I\<^sub>1\<close> decompositions are in place.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
theorem forward_diff_generic_rate_gen:
  fixes a b :: real and N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes i_lo: "i \<ge> 3" and i_hi: "i + j \<le> N"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj
            + Lj * (b - a) * (2 * (2 * real j + 1) * S + real j + 2)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  let ?L = "forward_diff f xs h j (i - 1)
              + (forward_diff f xs h j i - forward_diff f xs h j (i - 1)) * \<sigma> (w * (x - xs ! i))
              + (forward_diff f xs h j (i + 1) - forward_diff f xs h j i)
                  * \<sigma> (w * (x - xs ! (i + 1)))"
  have I1: "\<bar>Gj_network \<sigma> f xs h N j w x - ?L\<bar>
              \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
    unfolding Lj_def Mj_def
    by (rule forward_diff_I1_generic_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset j_pos N_gt
          i_lo i_hi x_in_cell sat])
  have J2: "\<bar>?L - (deriv ^^ j) f x\<bar> \<le> Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
    unfolding Lj_def S_def
    by (rule forward_diff_generic_L_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset
          bounded_sigmoidal j_pos i_lo i_hi x_in_cell])
  have tri: "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
               \<le> \<bar>Gj_network \<sigma> f xs h N j w x - ?L\<bar> + \<bar>?L - (deriv ^^ j) f x\<bar>"
    using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N j w x - ?L" "?L - (deriv ^^ j) f x"]
    by simp
  have h_eq: "Lj * h * (2 * (2 * real j + 1) * S + real j + 2)
                = Lj * (b - a) * (2 * (2 * real j + 1) * S + real j + 2) / real N"
    unfolding h_def by simp
  show ?thesis
    using tri I1 J2 h_eq by (simp add: add_divide_distrib)
qed

subsection \<open>\<open>I\<^sub>1\<close> decompositions for the remaining three cases\<close>

text \<open>
  Cases 3 and 4 both have \<^emph>\<open>no\<close> node to the right of the active cell, so their remainders carry
  only a left sum.  They differ solely in where \<open>L\<^sub>i\<close>'s leading \<open>\<Delta>\<^sup>j\<close> sits, so one lemma
  parametrised by that cut point \<open>p\<close> covers both: \<open>p = N-j\<close> is Case 3 (the trailing sum is the
  single term \<open>m = N-j+1\<close>, i.e. \<open>L\<^sub>i\<close>'s one \<open>\<sigma>\<close>-term) and \<open>p = N-j+1\<close> is Case 4 (the trailing sum
  is empty, matching \<open>L\<^sub>i = \<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1\<close> with no \<open>\<sigma>\<close>-term at all).

  Stated as an \<^emph>\<open>equation\<close> rather than a bound: the cancellation is exact, and the absolute-value
  step is cleaner applied afterwards.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_I1_tail_decomp_gen:
  fixes N j p :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes p_lo: "p \<ge> 1" and p_hi: "p \<le> N - j + 1"
  shows "Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j p
             + (\<Sum>m=p+1..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                  * \<sigma> (w * (x - xs ! m))))
       = (\<Sum>k=2..p. (forward_diff f xs h j k - forward_diff f xs h j (k - 1))
              * (\<sigma> (w * (x - xs ! k)) - 1))
         + forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
proof -
  define Df where "Df = (\<lambda>k. forward_diff f xs h j k)"

  have Gnet_eq: "Gj_network \<sigma> f xs h N j w x
      = (\<Sum>m=2..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        + Df 1 * \<sigma> (w * (x - xs ! 0))"
  proof -
    have "(\<Sum>k\<in>{1..N-j}. (Df (k + 1) - Df k) * \<sigma> (w * (x - xs ! (k + 1))))
        = (\<Sum>m\<in>{2..N-j+1}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>m. m - 1" "\<lambda>k. k + 1"]) auto
    then show ?thesis
      unfolding Gj_network_def Df_def by simp
  qed

  have telescope_shift: "(\<Sum>k=2..p. Df k - Df (k - 1)) + Df 1 = Df p"
  proof -
    have full: "(\<Sum>k=1..p. Df k - Df (k - 1)) + Df 0 = Df p"
      unfolding Df_def using forward_diff_telescope[of f xs h j p] .
    have split: "(\<Sum>k=1..p. Df k - Df (k - 1))
        = (Df 1 - Df 0) + (\<Sum>k=2..p. Df k - Df (k - 1))"
      using p_lo by (subst sum.atLeast_Suc_atMost) (auto simp add: eval_nat_numeral)
    from full split show ?thesis by linarith
  qed

  have disjoint: "{2..p} \<inter> {p+1..N-j+1} = {}" by auto
  have union: "{2..p} \<union> {p+1..N-j+1} = {2..N-j+1}" using p_lo p_hi by auto
  have sum_split:
    "(\<Sum>m=2..p. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
     + (\<Sum>m=p+1..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
     = (\<Sum>m=2..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
  proof -
    have "(\<Sum>m=2..p. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
       + (\<Sum>m=p+1..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
       = (\<Sum>m\<in>{2..p} \<union> {p+1..N-j+1}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.union_disjoint[symmetric]) (auto simp add: disjoint)
    then show ?thesis using union by simp
  qed

  have "Gj_network \<sigma> f xs h N j w x
          - (Df p + (\<Sum>m=p+1..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m))))
        = ((\<Sum>m=2..p. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
             - (\<Sum>k=2..p. Df k - Df (k - 1)))
          + (Df 1 * \<sigma> (w * (x - xs ! 0)) - Df 1)"
    unfolding Gnet_eq sum_split[symmetric] telescope_shift[symmetric] by simp
  also have "\<dots> = (\<Sum>k=2..p. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
                  + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
    by (simp add: sum_subtractf right_diff_distrib')
  finally show ?thesis unfolding Df_def .
qed

text \<open>
  Case 1, the left boundary: here there is no node to the \<^emph>\<open>left\<close> of the active cell, so the
  remainder carries only a right sum, starting at \<open>m = 4\<close> because \<open>L\<^sub>i\<close>'s two \<open>\<sigma>\<close>-terms cancel the
  \<open>m = 2, 3\<close> terms.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_I1_head_decomp_gen:
  fixes N j :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes three_le: "3 \<le> N - j + 1"
  shows "Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j 1
             + (forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))
             + (forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2)))
       = (\<Sum>m=4..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
              * \<sigma> (w * (x - xs ! m)))
         + forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
proof -
  define Df where "Df = (\<lambda>k. forward_diff f xs h j k)"

  have Gnet_eq: "Gj_network \<sigma> f xs h N j w x
      = (\<Sum>m=2..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        + Df 1 * \<sigma> (w * (x - xs ! 0))"
  proof -
    have "(\<Sum>k\<in>{1..N-j}. (Df (k + 1) - Df k) * \<sigma> (w * (x - xs ! (k + 1))))
        = (\<Sum>m\<in>{2..N-j+1}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>m. m - 1" "\<lambda>k. k + 1"]) auto
    then show ?thesis
      unfolding Gj_network_def Df_def by simp
  qed

  have disjoint: "{2..3} \<inter> {4..N-j+1} = {}" by auto
  have union: "{2..3} \<union> {4..N-j+1} = {2..N-j+1}" using three_le by auto
  have sum_split:
    "(\<Sum>m=2..3. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
     + (\<Sum>m=4..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
     = (\<Sum>m=2..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
  proof -
    have "(\<Sum>m=2..3. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
       + (\<Sum>m=4..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
       = (\<Sum>m\<in>{2..3} \<union> {4..N-j+1}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.union_disjoint[symmetric]) (auto simp add: disjoint)
    then show ?thesis using union by simp
  qed

  have head: "(\<Sum>m=2..3. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
                = (Df 2 - Df 1) * \<sigma> (w * (x - xs ! 2))
                  + (Df 3 - Df 2) * \<sigma> (w * (x - xs ! 3))"
    by (simp add: eval_nat_numeral)

  have "Gj_network \<sigma> f xs h N j w x
          - (Df 1
             + (Df 3 - Df 2) * \<sigma> (w * (x - xs ! 3))
             + (Df 2 - Df 1) * \<sigma> (w * (x - xs ! 2)))
        = (\<Sum>m=4..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
          + (Df 1 * \<sigma> (w * (x - xs ! 0)) - Df 1)"
    unfolding Gnet_eq sum_split[symmetric] head by simp
  also have "\<dots> = (\<Sum>m=4..N-j+1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
                  + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
    by (simp add: right_diff_distrib')
  finally show ?thesis unfolding Df_def .
qed

subsection \<open>\<open>I\<^sub>1\<close> at an explicit \<open>1/N\<close> rate, remaining cases\<close>

text \<open>
  Cases 3 and 4 together.  The only geometric input is an anchor node \<open>x\<^sub>q\<close> with \<open>x\<^sub>q \<le> x\<close> and
  \<open>p+1 \<le> q\<close>, which puts every summation node at least \<open>h\<close> to the left of \<open>x\<close>.  Case 3 uses
  \<open>p = N-j\<close>, \<open>q = N-j+1\<close>; Case 4 uses \<open>p = N-j+1\<close> and \<open>q = i \<ge> N-j+2\<close>.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_I1_tail_rate_gen:
  fixes a b :: real and N j p q :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes p_lo: "p \<ge> 1" and p_hi: "p \<le> N - j + 1"
  assumes q_in: "q \<in> {0..N+1}" and pq: "p + 1 \<le> q"
  assumes x_ge: "xs ! q \<le> x"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j p
             + (\<Sum>m=p+1..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                  * \<sigma> (w * (x - xs ! m))))\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have jN: "j \<le> N" using N_gt by simp
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have Mj_nn: "0 \<le> Mj"
  proof -
    have ain: "a \<in> {a..b}" using a_lt_b by simp
    have "(0::real) \<le> \<bar>(deriv ^^ j) f a\<bar>" by simp
    also have "\<dots> \<le> Mj" unfolding Mj_def by (rule deriv_j_le_Sup[OF Ck ab_subset a_lt_b ain])
    finally show ?thesis .
  qed
  have C_nn: "0 \<le> (2 * real j + 1) * Lj * h" using Lj_nn hpos by simp
  have invN_nn: "0 \<le> 1 / real N" using N_pos by simp

  have term1: "\<And>k. k \<in> {2..p}
      \<Longrightarrow> \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
  proof -
    fix k :: nat assume k_in: "k \<in> {2..p}"
    have k_lo: "k \<ge> 2" and k_up: "k \<le> p" using k_in by auto
    have k_in01: "k \<in> {0..N+1}" using k_up p_hi jN by auto
    have k_lt_N2: "k < N + 2" using k_up p_hi jN by simp
    have k1q: "k + 1 \<le> q" using k_up pq by simp
    have gap: "h \<le> x - xs ! k"
      by (rule sat_gap_left[OF h_def xs_def hpos q_in k_in01 k1q x_ge])
    have sat_k: "\<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> \<le> 1 / real N"
      using sat k_lt_N2 gap by fastforce
    have k_hi': "k \<le> N - j + 1" using k_up p_hi by simp
    have coef: "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                  \<le> (2 * real j + 1) * Lj * h"
      unfolding Lj_def
      by (rule forward_diff_adjacent_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset
            j_pos k_lo k_hi' jN])
    show "\<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
      using coef sat_k C_nn by (intro mult_mono) auto
  qed
  have sum1: "(\<Sum>k=2..p. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                 * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
              \<le> real (card {2..p}) * ((2 * real j + 1) * Lj * h * (1 / real N))"
    using term1 by (rule sum_bounded_above)

  have zero_in01: "(0::nat) \<in> {0..N+1}" by simp
  have zero_lt: "(0::nat) < N + 2" by simp
  have zero1q: "(0::nat) + 1 \<le> q" using pq p_lo by simp
  have gap0: "h \<le> x - xs ! 0"
    by (rule sat_gap_left[OF h_def xs_def hpos q_in zero_in01 zero1q x_ge])
  have sat0: "\<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar> \<le> 1 / real N"
    using sat zero_lt gap0 by fastforce
  have df1: "\<bar>forward_diff f xs h j 1\<bar> \<le> real j * Lj * h + Mj"
    unfolding Lj_def Mj_def
    by (rule forward_diff_one_term_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset jN])
  have df1_nn: "0 \<le> real j * Lj * h + Mj" using Lj_nn Mj_nn hpos by simp
  have mid: "\<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
               \<le> (real j * Lj * h + Mj) * (1 / real N)"
    using df1 sat0 df1_nn by (intro mult_mono) auto

  have card_bound: "real (card {2..p}) \<le> real N"
  proof -
    have "card {2..p} \<le> N" using p_hi jN by simp
    then show ?thesis by simp
  qed
  have sums_bound: "real (card {2..p}) * ((2 * real j + 1) * Lj * h * (1 / real N))
                    \<le> (2 * real j + 1) * Lj * (b - a) / real N"
  proof -
    have Cinv_nn: "0 \<le> (2 * real j + 1) * Lj * h * (1 / real N)" using C_nn invN_nn by simp
    have "real (card {2..p}) * ((2 * real j + 1) * Lj * h * (1 / real N))
            \<le> real N * ((2 * real j + 1) * Lj * h * (1 / real N))"
      using card_bound Cinv_nn by (rule mult_right_mono)
    also have "\<dots> = (2 * real j + 1) * Lj * h" using N_pos by simp
    also have "\<dots> = (2 * real j + 1) * Lj * (b - a) / real N" unfolding h_def by simp
    finally show ?thesis .
  qed

  have decomp: "Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j p
             + (\<Sum>m=p+1..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                  * \<sigma> (w * (x - xs ! m))))
       = (\<Sum>k=2..p. (forward_diff f xs h j k - forward_diff f xs h j (k - 1))
              * (\<sigma> (w * (x - xs ! k)) - 1))
         + forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
    by (rule forward_diff_I1_tail_decomp_gen[OF p_lo p_hi])

  have t1: "\<bar>(\<Sum>k=2..p. (forward_diff f xs h j k - forward_diff f xs h j (k - 1))
                * (\<sigma> (w * (x - xs ! k)) - 1))\<bar>
              \<le> (\<Sum>k=2..p. \<bar>forward_diff f xs h j k - forward_diff f xs h j (k - 1)\<bar>
                     * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)"
    by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
  have t2: "\<bar>forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>
              = \<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
    by (simp add: abs_mult)
  have tri: "\<bar>(\<Sum>k=2..p. (forward_diff f xs h j k - forward_diff f xs h j (k - 1))
                 * (\<sigma> (w * (x - xs ! k)) - 1))
              + forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>
             \<le> \<bar>(\<Sum>k=2..p. (forward_diff f xs h j k - forward_diff f xs h j (k - 1))
                    * (\<sigma> (w * (x - xs ! k)) - 1))\<bar>
               + \<bar>forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>"
    by (rule abs_triangle_ineq)
  have final_eq: "(2 * real j + 1) * Lj * (b - a) / real N
                    + (real j * Lj * h + Mj) * (1 / real N)
                  = ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
    by (simp add: add_divide_distrib)
  show ?thesis
    unfolding decomp
    using tri t1 t2 sum1 mid sums_bound final_eq by linarith
qed

text \<open>
  Case 1.  Mirror image: no left sum, and the right sum starts at \<open>m = 4\<close>.  The anchor for the
  \<open>\<sigma>\<^sub>0\<close> term is \<open>x\<^sub>1\<close>, and for the right sum it is \<open>x\<^sub>3\<close>.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma forward_diff_I1_head_rate_gen:
  fixes a b :: real and N j :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes x_ge: "xs ! 1 \<le> x" and x_le: "x \<le> xs ! 3"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j 1
             + (forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))
             + (forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2)))\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have jN: "j \<le> N" using N_gt by simp
  have three_le: "3 \<le> N - j + 1" using N_gt by simp
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have Mj_nn: "0 \<le> Mj"
  proof -
    have ain: "a \<in> {a..b}" using a_lt_b by simp
    have "(0::real) \<le> \<bar>(deriv ^^ j) f a\<bar>" by simp
    also have "\<dots> \<le> Mj" unfolding Mj_def by (rule deriv_j_le_Sup[OF Ck ab_subset a_lt_b ain])
    finally show ?thesis .
  qed
  have C_nn: "0 \<le> (2 * real j + 1) * Lj * h" using Lj_nn hpos by simp
  have invN_nn: "0 \<le> 1 / real N" using N_pos by simp
  have three_in01: "(3::nat) \<in> {0..N+1}" using three_le jN by auto
  have one_in01: "(1::nat) \<in> {0..N+1}" by simp

  have term3: "\<And>m. m \<in> {4..N - j + 1}
      \<Longrightarrow> \<bar>forward_diff f xs h j m - forward_diff f xs h j (m - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! m))\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
  proof -
    fix m :: nat assume m_in: "m \<in> {4..N - j + 1}"
    have m_lo: "4 \<le> m" and m_up: "m \<le> N - j + 1" using m_in by auto
    have m_ge2: "m \<ge> 2" using m_lo by simp
    have m_in01: "m \<in> {0..N+1}" using m_up jN by auto
    have m_lt_N2: "m < N + 2" using m_up jN by simp
    text \<open>\<open>where i = 2\<close> is needed: \<open>rule\<close> cannot unify the numeral \<open>3\<close> against the pattern
      \<open>?i + 1\<close>.  Instantiating first lets the numerals normalise.\<close>
    have gap: "x - xs ! m \<le> - h"
      using sat_gap_right[OF h_def xs_def hpos, where i = 2 and k = m]
            three_in01 m_in01 m_lo x_le
      by auto
    have sat_m: "\<bar>\<sigma> (w * (x - xs ! m))\<bar> \<le> 1 / real N"
      using sat m_lt_N2 gap by fastforce
    have coef: "\<bar>forward_diff f xs h j m - forward_diff f xs h j (m - 1)\<bar>
                  \<le> (2 * real j + 1) * Lj * h"
      unfolding Lj_def
      by (rule forward_diff_adjacent_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset
            j_pos m_ge2 m_up jN])
    show "\<bar>forward_diff f xs h j m - forward_diff f xs h j (m - 1)\<bar>
            * \<bar>\<sigma> (w * (x - xs ! m))\<bar>
          \<le> (2 * real j + 1) * Lj * h * (1 / real N)"
      using coef sat_m C_nn by (intro mult_mono) auto
  qed
  have sum3: "(\<Sum>m=4..N - j + 1. \<bar>forward_diff f xs h j m - forward_diff f xs h j (m - 1)\<bar>
                 * \<bar>\<sigma> (w * (x - xs ! m))\<bar>)
              \<le> real (card {4..N - j + 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))"
    using term3 by (rule sum_bounded_above)

  have zero_in01: "(0::nat) \<in> {0..N+1}" by simp
  have zero_lt: "(0::nat) < N + 2" by simp
  have gap0: "h \<le> x - xs ! 0"
    by (rule sat_gap_left[OF h_def xs_def hpos one_in01 zero_in01 _ x_ge]) simp
  have sat0: "\<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar> \<le> 1 / real N"
    using sat zero_lt gap0 by fastforce
  have df1: "\<bar>forward_diff f xs h j 1\<bar> \<le> real j * Lj * h + Mj"
    unfolding Lj_def Mj_def
    by (rule forward_diff_one_term_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset jN])
  have df1_nn: "0 \<le> real j * Lj * h + Mj" using Lj_nn Mj_nn hpos by simp
  have mid: "\<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
               \<le> (real j * Lj * h + Mj) * (1 / real N)"
    using df1 sat0 df1_nn by (intro mult_mono) auto

  have card_bound: "real (card {4..N - j + 1}) \<le> real N"
  proof -
    have "card {4..N - j + 1} \<le> N" using jN by simp
    then show ?thesis by simp
  qed
  have sums_bound: "real (card {4..N - j + 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))
                    \<le> (2 * real j + 1) * Lj * (b - a) / real N"
  proof -
    have Cinv_nn: "0 \<le> (2 * real j + 1) * Lj * h * (1 / real N)" using C_nn invN_nn by simp
    have "real (card {4..N - j + 1}) * ((2 * real j + 1) * Lj * h * (1 / real N))
            \<le> real N * ((2 * real j + 1) * Lj * h * (1 / real N))"
      using card_bound Cinv_nn by (rule mult_right_mono)
    also have "\<dots> = (2 * real j + 1) * Lj * h" using N_pos by simp
    also have "\<dots> = (2 * real j + 1) * Lj * (b - a) / real N" unfolding h_def by simp
    finally show ?thesis .
  qed

  have decomp: "Gj_network \<sigma> f xs h N j w x
          - (forward_diff f xs h j 1
             + (forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))
             + (forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2)))
       = (\<Sum>m=4..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
              * \<sigma> (w * (x - xs ! m)))
         + forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
    by (rule forward_diff_I1_head_decomp_gen[OF three_le])

  have t3: "\<bar>(\<Sum>m=4..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                * \<sigma> (w * (x - xs ! m)))\<bar>
              \<le> (\<Sum>m=4..N-j+1. \<bar>forward_diff f xs h j m - forward_diff f xs h j (m - 1)\<bar>
                     * \<bar>\<sigma> (w * (x - xs ! m))\<bar>)"
    by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
  have t2: "\<bar>forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>
              = \<bar>forward_diff f xs h j 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
    by (simp add: abs_mult)
  have tri: "\<bar>(\<Sum>m=4..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                 * \<sigma> (w * (x - xs ! m)))
              + forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>
             \<le> \<bar>(\<Sum>m=4..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                    * \<sigma> (w * (x - xs ! m)))\<bar>
               + \<bar>forward_diff f xs h j 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>"
    by (rule abs_triangle_ineq)
  have final_eq: "(2 * real j + 1) * Lj * (b - a) / real N
                    + (real j * Lj * h + Mj) * (1 / real N)
                  = ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
    by (simp add: add_divide_distrib)
  show ?thesis
    unfolding decomp
    using tri t3 t2 sum3 mid sums_bound final_eq by linarith
qed

subsection \<open>The two halves joined, remaining three cases\<close>

text \<open>Case 1, the left boundary.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
theorem forward_diff_left_rate_gen:
  fixes a b :: real and N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes i_in12: "i \<in> {1, 2}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj
            + Lj * (b - a) * (2 * (2 * real j + 1) * S + real j + 2)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have jN: "j \<le> N" using N_gt by simp
  have one_in01: "(1::nat) \<in> {0..N+1}" by simp
  have three_in01: "(3::nat) \<in> {0..N+1}" using N_gt by auto
  have i_in01: "i \<in> {0..N+1}" and ip1_in01: "i + 1 \<in> {0..N+1}"
    using i_in12 N_gt by auto

  text \<open>\<open>x\<close> sits between \<open>x\<^sub>1\<close> and \<open>x\<^sub>3\<close>.\<close>
  have x_ge: "xs ! 1 \<le> x"
  proof -
    have "xs ! i - xs ! 1 = (real i - real 1) * h"
      by (rule node_gap_general[OF h_def xs_def one_in01 i_in01])
    then have "xs ! 1 \<le> xs ! i" using i_in12 hpos by auto
    then show ?thesis using x_in_cell by simp
  qed
  have x_le: "x \<le> xs ! 3"
  proof -
    have "xs ! 3 - xs ! (i + 1) = (real 3 - real (i + 1)) * h"
      by (rule node_gap_general[OF h_def xs_def ip1_in01 three_in01])
    then have "xs ! (i + 1) \<le> xs ! 3" using i_in12 hpos by auto
    then show ?thesis using x_in_cell by simp
  qed

  let ?L = "forward_diff f xs h j 1
              + (forward_diff f xs h j 3 - forward_diff f xs h j 2) * \<sigma> (w * (x - xs ! 3))
              + (forward_diff f xs h j 2 - forward_diff f xs h j 1) * \<sigma> (w * (x - xs ! 2))"
  have I1: "\<bar>Gj_network \<sigma> f xs h N j w x - ?L\<bar>
              \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
    unfolding Lj_def Mj_def
    by (rule forward_diff_I1_head_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset j_pos N_gt
          x_ge x_le sat])
  have J2: "\<bar>?L - (deriv ^^ j) f x\<bar> \<le> Lj * h * (2 * (2 * real j + 1) * S + real j + 2)"
    unfolding Lj_def S_def
    by (rule forward_diff_left_L_bound_gen[OF a_lt_b h_def xs_def Ck ab_subset
          bounded_sigmoidal j_pos N_gt i_in12 x_in_cell])
  have tri: "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
               \<le> \<bar>Gj_network \<sigma> f xs h N j w x - ?L\<bar> + \<bar>?L - (deriv ^^ j) f x\<bar>"
    using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N j w x - ?L" "?L - (deriv ^^ j) f x"]
    by simp
  have h_eq: "Lj * h * (2 * (2 * real j + 1) * S + real j + 2)
                = Lj * (b - a) * (2 * (2 * real j + 1) * S + real j + 2) / real N"
    unfolding h_def by simp
  show ?thesis
    using tri I1 J2 h_eq by (simp add: add_divide_distrib)
qed

text \<open>Case 3, the single cell \<open>i = N-j+1\<close>.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
theorem forward_diff_right_rate_gen:
  fixes a b :: real and N j :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes x_in_cell: "x \<in> {xs ! (N - j + 1) .. xs ! (N - j + 2)}"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj
            + Lj * (b - a) * ((2 * real j + 1) * S + real j + 2)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have jN: "j \<le> N" using N_gt by simp
  have p_lo: "N - j \<ge> 1" using N_gt by simp
  have p_hi: "N - j \<le> N - j + 1" by simp
  have q_in: "N - j + 1 \<in> {0..N+1}" using jN by auto
  have pq: "(N - j) + 1 \<le> N - j + 1" by simp
  have x_ge: "xs ! (N - j + 1) \<le> x" using x_in_cell by simp

  text \<open>The trailing sum is the single term \<open>m = N-j+1\<close>, i.e. exactly \<open>L\<^sub>i\<close>'s one \<open>\<sigma>\<close>-term.\<close>
  have single: "(\<Sum>m=(N - j)+1..N-j+1. (forward_diff f xs h j m - forward_diff f xs h j (m - 1))
                    * \<sigma> (w * (x - xs ! m)))
                = (forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
                    * \<sigma> (w * (x - xs ! (N - j + 1)))"
    by simp

  let ?L = "forward_diff f xs h j (N - j)
              + (forward_diff f xs h j (N - j + 1) - forward_diff f xs h j (N - j))
                  * \<sigma> (w * (x - xs ! (N - j + 1)))"
  have I1: "\<bar>Gj_network \<sigma> f xs h N j w x - ?L\<bar>
              \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
    unfolding Lj_def Mj_def single[symmetric]
    by (rule forward_diff_I1_tail_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset j_pos N_gt
          p_lo p_hi q_in pq x_ge sat])
  have J2: "\<bar>?L - (deriv ^^ j) f x\<bar> \<le> Lj * h * ((2 * real j + 1) * S + real j + 2)"
    unfolding Lj_def S_def
    by (rule forward_diff_right_L_bound_gen[OF a_lt_b h_def xs_def Ck ab_subset
          bounded_sigmoidal j_pos N_gt x_in_cell])
  have tri: "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
               \<le> \<bar>Gj_network \<sigma> f xs h N j w x - ?L\<bar> + \<bar>?L - (deriv ^^ j) f x\<bar>"
    using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N j w x - ?L" "?L - (deriv ^^ j) f x"]
    by simp
  have h_eq: "Lj * h * ((2 * real j + 1) * S + real j + 2)
                = Lj * (b - a) * ((2 * real j + 1) * S + real j + 2) / real N"
    unfolding h_def by simp
  show ?thesis
    using tri I1 J2 h_eq by (simp add: add_divide_distrib)
qed

text \<open>Case 4, the far-right plateau.  The trailing sum is empty and \<open>L\<^sub>i\<close> has no \<open>\<sigma>\<close>-term.\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
theorem forward_diff_plateau_rate_gen:
  fixes a b :: real and N j i :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes i_lo: "i \<ge> N - j + 2" and i_hi: "i \<le> N"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj
            + 2 * real j * Lj * (b - a)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have jN: "j \<le> N" using N_gt by simp
  have p_lo: "N - j + 1 \<ge> 1" by simp
  have p_hi: "N - j + 1 \<le> N - j + 1" by simp
  have i_in01: "i \<in> {0..N+1}" using i_hi by auto
  have pq: "(N - j + 1) + 1 \<le> i" using i_lo by simp
  have x_ge: "xs ! i \<le> x" using x_in_cell by simp

  text \<open>The trailing sum runs over the empty range \<open>{N-j+2..N-j+1}\<close>.\<close>
  have empty: "(\<Sum>m=(N - j + 1)+1..N-j+1. (forward_diff f xs h j m
                    - forward_diff f xs h j (m - 1)) * \<sigma> (w * (x - xs ! m))) = 0"
    by simp

  have I1: "\<bar>Gj_network \<sigma> f xs h N j w x - forward_diff f xs h j (N - j + 1)\<bar>
              \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
  proof -
    have "\<bar>Gj_network \<sigma> f xs h N j w x
            - (forward_diff f xs h j (N - j + 1)
               + (\<Sum>m=(N - j + 1)+1..N-j+1. (forward_diff f xs h j m
                      - forward_diff f xs h j (m - 1)) * \<sigma> (w * (x - xs ! m))))\<bar>
            \<le> ((2 * real j + 1) * Lj * (b - a) + (real j * Lj * h + Mj)) / real N"
      unfolding Lj_def Mj_def
      by (rule forward_diff_I1_tail_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset j_pos N_gt
            p_lo p_hi i_in01 pq x_ge sat])
    then show ?thesis unfolding empty by simp
  qed
  have J2: "\<bar>forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f x\<bar> \<le> 2 * real j * Lj * h"
    unfolding Lj_def
    by (rule forward_diff_plateau_L_bound_gen[OF a_lt_b N_pos h_def xs_def Ck ab_subset
          j_pos jN i_lo i_hi x_in_cell])
  have tri: "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
               \<le> \<bar>Gj_network \<sigma> f xs h N j w x - forward_diff f xs h j (N - j + 1)\<bar>
                 + \<bar>forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f x\<bar>"
    using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N j w x
                                 - forward_diff f xs h j (N - j + 1)"
                               "forward_diff f xs h j (N - j + 1) - (deriv ^^ j) f x"]
    by simp
  have h_eq: "2 * real j * Lj * h = 2 * real j * Lj * (b - a) / real N"
    unfolding h_def by simp
  show ?thesis
    using tri I1 J2 h_eq by (simp add: add_divide_distrib)
qed

subsection \<open>Theorem 4.1/4.2 for general \<open>j\<close>: the case dispatch\<close>

text \<open>
  The four cases exhaust \<open>{1..N}\<close> -- \<open>{1,2} \<union> {3..N-j} \<union> {N-j+1} \<union> {N-j+2..N}\<close>, using
  \<open>N > j+3\<close> (so \<open>N-j \<ge> 4\<close>) and \<open>j \<ge> 1\<close> -- so \<open>exists_containing_interval\<close> locating the active
  cell is enough to dispatch.

  Their four constants are not comparable pairwise: Case 4's \<open>2jL\<^sub>j(b-a)\<close> is \<^emph>\<open>not\<close> dominated by
  Case 1/2's \<open>L\<^sub>j(b-a)(2(2j+1)S+j+2)\<close> when \<open>\<sigma>\<close> is small and \<open>j\<close> large (at \<open>S = 0\<close> that would need
  \<open>j \<le> 2\<close>).  So the uniform statement uses \<open>2(2j+1)S + 2j + 2\<close>, which dominates all four:
  \<open>j+2 \<le> 2j+2\<close> for Cases 1 and 2, likewise for Case 3 after \<open>(2j+1)S \<le> 2(2j+1)S\<close>, and \<open>2j \<le> 2j+2\<close>
  for Case 4.
\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
theorem forward_diff_rate_gen:
  fixes a b :: real and N j :: nat and h w x :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  assumes x_in_ab: "x \<in> {a..b}"
  assumes sat: "\<forall>k < N + 2.
                  (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
       \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj
            + Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have jN: "j \<le> N" using N_gt by simp
  have Lj_nn: "0 \<le> Lj" unfolding Lj_def by (rule Lj_nonneg[OF Ck ab_subset a_lt_b])
  have S_nn: "0 \<le> S"
    unfolding S_def using sigma_abs_le_Sup[OF bounded_sigmoidal, of 0] by simp
  have base_nn: "0 \<le> Lj * (b - a)" using Lj_nn a_lt_b by simp
  have N_nn: "0 \<le> real N" using N_pos by simp

  have jS_nn: "0 \<le> (2 * real j + 1) * S" using S_nn by simp

  text \<open>\<open>let\<close>, not \<open>define\<close>: \<open>define\<close> folds the goal but leaves \<open>?thesis\<close> bound to the unfolded
    statement, so the branches' \<open>finally show ?thesis\<close> would no longer match.\<close>
  let ?A = "(2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj"
  let ?D = "2 * (2 * real j + 1) * S + 2 * real j + 2"

  text \<open>Every case constant is at most \<open>?D\<close>, so every case bound is at most the stated one.\<close>
  have step: "\<And>c. c \<le> ?D \<Longrightarrow>
        (?A + Lj * (b - a) * c) / real N \<le> (?A + Lj * (b - a) * ?D) / real N"
  proof -
    fix c :: real assume cD: "c \<le> ?D"
    have "Lj * (b - a) * c \<le> Lj * (b - a) * ?D"
      by (rule mult_left_mono[OF cD base_nn])
    then show "(?A + Lj * (b - a) * c) / real N \<le> (?A + Lj * (b - a) * ?D) / real N"
      using N_nn by (intro divide_right_mono) auto
  qed

  obtain i where i_range: "i \<in> {1..N}" and x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
    using exists_containing_interval[OF a_lt_b N_pos h_def xs_def x_in_ab] by blast
  have i_lo1: "1 \<le> i" and i_hiN: "i \<le> N" using i_range by auto

  have j_nn: "0 \<le> real j" by simp
  have expand: "2 * (2 * real j + 1) * S = 2 * ((2 * real j + 1) * S)" by simp

  show ?thesis
  proof (cases "i \<le> 2")
    case True
    have i_in12: "i \<in> {1, 2}" using True i_lo1 by auto
    have cle: "2 * (2 * real j + 1) * S + real j + 2 \<le> ?D" using j_nn by linarith
    have "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
            \<le> (?A + Lj * (b - a) * (2 * (2 * real j + 1) * S + real j + 2)) / real N"
      unfolding Lj_def Mj_def S_def
      using forward_diff_left_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset bounded_sigmoidal
              j_pos N_gt i_in12 x_in_cell sat]
      by (simp add: algebra_simps)
    also have "\<dots> \<le> (?A + Lj * (b - a) * ?D) / real N" by (rule step[OF cle])
    finally show ?thesis .
  next
    case False
    then have i_lo3: "3 \<le> i" by simp
    show ?thesis
    proof (cases "i \<le> N - j")
      case True
      have i_hi: "i + j \<le> N" using True jN by simp
      have cle: "2 * (2 * real j + 1) * S + real j + 2 \<le> ?D" using j_nn by linarith
      have "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
              \<le> (?A + Lj * (b - a) * (2 * (2 * real j + 1) * S + real j + 2)) / real N"
        unfolding Lj_def Mj_def S_def
        using forward_diff_generic_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset
                bounded_sigmoidal j_pos N_gt i_lo3 i_hi x_in_cell sat]
        by (simp add: algebra_simps)
      also have "\<dots> \<le> (?A + Lj * (b - a) * ?D) / real N" by (rule step[OF cle])
      finally show ?thesis .
    next
      case False
      then have i_gt: "N - j + 1 \<le> i" by simp
      show ?thesis
      proof (cases "i = N - j + 1")
        case True
        have cell: "x \<in> {xs ! (N - j + 1) .. xs ! (N - j + 2)}"
          using x_in_cell True by simp
        have cle: "(2 * real j + 1) * S + real j + 2 \<le> ?D"
          unfolding expand using jS_nn j_nn by linarith
        have "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
                \<le> (?A + Lj * (b - a) * ((2 * real j + 1) * S + real j + 2)) / real N"
          unfolding Lj_def Mj_def S_def
          using forward_diff_right_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset
                  bounded_sigmoidal j_pos N_gt cell sat]
          by (simp add: algebra_simps)
        also have "\<dots> \<le> (?A + Lj * (b - a) * ?D) / real N" by (rule step[OF cle])
        finally show ?thesis .
      next
        case False
        have i_lo4: "N - j + 2 \<le> i" using i_gt False by simp
        have cle: "2 * real j \<le> ?D"
          unfolding expand using jS_nn j_nn by linarith
        have "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
                \<le> (?A + Lj * (b - a) * (2 * real j)) / real N"
          unfolding Lj_def Mj_def
          using forward_diff_plateau_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset
                  j_pos N_gt i_lo4 i_hiN x_in_cell sat]
          by (simp add: algebra_simps)
        also have "\<dots> \<le> (?A + Lj * (b - a) * ?D) / real N" by (rule step[OF cle])
        finally show ?thesis .
      qed
    qed
  qed
qed

subsection \<open>Theorem 4.2 at general \<open>j\<close>\<close>

text \<open>
  Packaging the dispatch with \<open>sigma_saturation_for_N\<close> gives Theorem 4.2's own statement at
  general \<open>j\<close>: for every \<open>N > j+3\<close> there is \<open>w\<^sub>0>0\<close> such that the estimate holds for every
  \<open>w \<ge> w\<^sub>0\<close>, uniformly in \<open>x\<close> on \<open>[a,b]\<close>.  The \<open>j=1\<close> instance of this is
  \<open>forward_diff_one_rate\<close> (\<^file>\<open>Simultaneous_Approximation_Rate.thy\<close>), reached there by a
  different route.

  As at \<open>j=1\<close>, the constant is this development's own rather than the paper's printed
  \<open>L\<^sub>j(b-a)(2\<parallel>\<sigma>\<parallel>\<^sub>\<infinity>+1+max{2,j}) + Ctilde\<^sub>j(b-a)(4\<parallel>\<sigma>\<parallel>\<^sub>\<infinity>+3) + \<parallel>f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity>\<close>; both are \<open>O(1)\<close>, so the
  \<open>O(1/N)\<close> rate -- the theorem's content -- is the same.  Note also that \<open>Ctilde\<^sub>j = jL\<^sub>j\<close> here,
  by \<open>forward_diff_consistency\<close>, so the paper's \<open>max{2,j}\<close> growth in \<open>j\<close> is reproduced.
\<close>
(* Theorem 4.2: general-order rate, with the explicit constant derived here. *)
theorem forward_diff_rate:
  fixes a b :: real and N j :: nat and f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
    and U :: "real set"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on (Suc j) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes j_pos: "j \<ge> 1" and N_gt: "N > j + 3"
  defines "Lj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
  defines "Mj \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<exists>w0>0. \<forall>w \<ge> w0. \<forall>x \<in> {a..b}.
           \<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N j w x
              - (deriv ^^ j) f x\<bar>
             \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * ((b - a) / real N) + Mj
                  + Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N"
proof -
  have N_pos: "N > 0" using N_gt by simp
  define h where h_def: "h = (b - a) / real N"
  define xs where xs_def: "xs = unif_part a b N"
  obtain w0 where w0_pos: "w0 > 0"
    and sat: "\<forall>w \<ge> w0. \<forall>k < N + 2.
                (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
              \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
    using sigma_saturation_for_N[OF sigmoidal_function a_lt_b N_pos h_def]
    unfolding xs_def by blast
  show ?thesis
  proof (intro exI[where x = w0] conjI)
    show "w0 > 0" using w0_pos .
  next
    show "\<forall>w \<ge> w0. \<forall>x \<in> {a..b}.
            \<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N j w x
               - (deriv ^^ j) f x\<bar>
              \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * ((b - a) / real N) + Mj
                   + Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N"
    proof (intro allI impI ballI)
      fix w :: real and x :: real
      assume w_ge: "w0 \<le> w" and x_in_ab: "x \<in> {a..b}"
      have sat_w: "\<forall>k < N + 2.
              (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
            \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
        using sat w_ge by blast
      have "\<bar>Gj_network \<sigma> f xs h N j w x - (deriv ^^ j) f x\<bar>
              \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * h + Mj
                   + Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N"
        unfolding Lj_def Mj_def S_def
        by (rule forward_diff_rate_gen[OF a_lt_b h_def xs_def Ck ab_subset bounded_sigmoidal
              j_pos N_gt x_in_ab sat_w])
      then show "\<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N j w x
                    - (deriv ^^ j) f x\<bar>
                   \<le> ((2 * real j + 1) * Lj * (b - a) + real j * Lj * ((b - a) / real N) + Mj
                        + Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N"
        unfolding h_def xs_def .
    qed
  qed
qed

subsection \<open>Theorem 4.1 at general \<open>j\<close>: the simultaneity statement\<close>

text \<open>\<^const>\<open>C_k_on\<close> is antitone in its order (for nonzero orders).\<close>
(* Auxiliary for Theorems 4.1-4.2, general derivative order; not separately numbered. *)
lemma C_k_on_mono:
  assumes "C_k_on k f U" and "m \<le> k" and "m \<noteq> 0"
  shows "C_k_on m f U"
  using assms unfolding C_k_on_def by (auto split: if_splits)

text \<open>
  Theorem 4.1 (p.176): for every \<open>\<epsilon>>0\<close> there are \<open>N\<close> and \<open>w>0\<close> such that \<^emph>\<open>for every\<close>
  \<open>j = 1,\<dots>,n\<close> at once, \<open>\<parallel>G\<^sup>j\<^sub>N f - f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity> < \<epsilon>\<close>.

  The simultaneity is what makes this more than the conjunction of the per-\<open>j\<close> statements, and it
  turns on one fact: \<open>w\<^sub>0\<close> comes from \<open>sigma_saturation_for_N\<close>, which depends on \<open>N\<close> and \<open>h\<close> but
  \<^bold>\<open>not on \<open>j\<close>\<close>.  So a single \<open>w\<^sub>0\<close> serves every \<open>j\<close> once \<open>N\<close> is fixed, and only \<open>N\<close> faces
  \<open>j\<close>-dependent constraints -- finitely many, so a maximum settles them.  Assembling instead from
  \<open>n\<close> separate applications of \<open>forward_diff_rate\<close> would give unrelated \<open>N\<^sub>j\<close>, \<open>w\<^sub>j\<close> and would not
  prove this theorem.
\<close>
(* Theorem 4.1: simultaneous approximation of derivative orders 1 through n. *)
theorem forward_diff_simultaneous_approximation:
  fixes a b \<epsilon> :: real and n :: nat and f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
    and U :: "real set"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on (Suc n) f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes n_pos: "n \<ge> 1"
  assumes eps_pos: "\<epsilon> > 0"
  shows "\<exists>N w. n + 3 < N \<and> 0 < w \<and>
           (\<forall>j \<in> {1..n}. \<forall>x \<in> {a..b}.
              \<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N j w x
                 - (deriv ^^ j) f x\<bar> < \<epsilon>)"
proof -
  define S where S_def: "S = Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  define Kf where Kf_def: "Kf = (\<lambda>j::nat.
       (2 * real j + 1) * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * (b - a)
       + real j * Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * (b - a)
       + Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})
       + Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b}) * (b - a)
           * (2 * (2 * real j + 1) * S + 2 * real j + 2))"
  define K where K_def: "K = Max (Kf ` {1..n})"
  have K_ge: "\<And>j. j \<in> {1..n} \<Longrightarrow> Kf j \<le> K"
    unfolding K_def by (rule Max_ge) auto

  text \<open>One \<open>N\<close> large enough for every \<open>j \<le> n\<close> at once.\<close>
  obtain N :: nat where N_gt_n: "n + 3 < N" and N_big: "K / \<epsilon> < real N"
  proof -
    obtain N0 :: nat where N0: "K / \<epsilon> < real N0" using reals_Archimedean2 by blast
    have "n + 3 < max N0 (n + 4)" by simp
    moreover have "K / \<epsilon> < real (max N0 (n + 4))" using N0 by simp
    ultimately show ?thesis using that by blast
  qed
  have N_pos: "0 < N" using N_gt_n by simp
  have KN: "K / real N < \<epsilon>"
  proof -
    have "K < \<epsilon> * real N"
      using N_big eps_pos by (simp add: pos_divide_less_eq mult.commute)
    then show ?thesis using N_pos by (simp add: divide_less_eq)
  qed

  define h where h_def: "h = (b - a) / real N"
  define xs where xs_def: "xs = unif_part a b N"
  have hpos: "0 < h" using h_pos[OF a_lt_b N_pos h_def] .
  have h_le: "h \<le> b - a"
  proof -
    have "real N \<ge> 1" using N_pos by simp
    then show ?thesis unfolding h_def using a_lt_b by (simp add: divide_le_eq)
  qed

  text \<open>One \<open>w\<^sub>0\<close>, independent of \<open>j\<close>.\<close>
  obtain w0 where w0_pos: "0 < w0"
    and sat: "\<forall>w \<ge> w0. \<forall>k < N + 2.
                (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
              \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
    using sigma_saturation_for_N[OF sigmoidal_function a_lt_b N_pos h_def]
    unfolding xs_def by blast
  have sat_w0: "\<forall>k < N + 2.
                (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w0 * (y - xs ! k)) - 1\<bar> < 1 / real N)
              \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w0 * (y - xs ! k))\<bar> < 1 / real N)"
    using sat by blast

  text \<open>
    Proved as a standalone fact stated in terms of the local \<open>xs\<close> and \<open>h\<close>, then converted once
    with \<open>[unfolded \<dots>]\<close> on the fact.  Stating it directly as a \<open>show\<close> under the \<open>\<exists>\<close> does not work:
    \<open>define\<close> has already abstracted \<open>xs\<close> and \<open>h\<close> out of the surrounding context, so the goal and
    the cited bound end up on opposite sides of those definitions.
  \<close>
  have main: "\<forall>j \<in> {1..n}. \<forall>x \<in> {a..b}.
                \<bar>Gj_network \<sigma> f xs h N j w0 x - (deriv ^^ j) f x\<bar> < \<epsilon>"
  text \<open>\<open>intro ballI\<close> strips \<^emph>\<open>both\<close> \<open>\<forall>j\<close> and the inner \<open>\<forall>x\<close>, so both must be taken at once --
    the same trap already recorded for Theorem 5.2's \<open>intro exI \<dots> allI impI\<close>.\<close>
  proof (intro ballI)
    fix j :: nat and x :: real
    assume j_in: "j \<in> {1..n}" and x_in_ab: "x \<in> {a..b}"
    have j_pos: "1 \<le> j" and j_le: "j \<le> n" using j_in by auto
    have N_gt: "j + 3 < N" using N_gt_n j_le by simp
    have Ckj: "C_k_on (Suc j) f U"
      using C_k_on_mono[OF Ck] j_le by simp
    let ?Lj = "Sup ((\<lambda>t. \<bar>(deriv ^^ Suc j) f t\<bar>) ` {a..b})"
    let ?Mj = "Sup ((\<lambda>t. \<bar>(deriv ^^ j) f t\<bar>) ` {a..b})"
    have Lj_nn: "0 \<le> ?Lj" by (rule Lj_nonneg[OF Ckj ab_subset a_lt_b])
    have step1: "\<bar>Gj_network \<sigma> f xs h N j w0 x - (deriv ^^ j) f x\<bar>
            \<le> ((2 * real j + 1) * ?Lj * (b - a) + real j * ?Lj * h + ?Mj
                 + ?Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N"
      unfolding S_def
      by (rule forward_diff_rate_gen[OF a_lt_b h_def xs_def Ckj ab_subset
            bounded_sigmoidal j_pos N_gt x_in_ab sat_w0])
    have num_le: "(2 * real j + 1) * ?Lj * (b - a) + real j * ?Lj * h + ?Mj
                    + ?Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)
                  \<le> Kf j"
    proof -
      have "real j * ?Lj * h \<le> real j * ?Lj * (b - a)"
        using h_le Lj_nn by (intro mult_left_mono) auto
      then show ?thesis unfolding Kf_def by simp
    qed
    have div_le: "((2 * real j + 1) * ?Lj * (b - a) + real j * ?Lj * h + ?Mj
                    + ?Lj * (b - a) * (2 * (2 * real j + 1) * S + 2 * real j + 2)) / real N
                  \<le> Kf j / real N"
      using num_le N_pos by (intro divide_right_mono) auto
    have bound1: "\<bar>Gj_network \<sigma> f xs h N j w0 x - (deriv ^^ j) f x\<bar> \<le> Kf j / real N"
      using step1 div_le by (rule order_trans)
    have bound2: "Kf j / real N \<le> K / real N"
      using K_ge[OF j_in] N_pos by (intro divide_right_mono) auto
    show "\<bar>Gj_network \<sigma> f xs h N j w0 x - (deriv ^^ j) f x\<bar> < \<epsilon>"
      using bound1 bound2 KN by linarith
  qed
  show ?thesis
    using N_gt_n w0_pos main[unfolded h_def xs_def] by blast
qed


subsection \<open>Theorems 4.1 and 4.2 in their printed forms\<close>

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
