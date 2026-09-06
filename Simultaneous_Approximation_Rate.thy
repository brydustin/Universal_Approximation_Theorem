section \<open>Theorem 4.2: the convergence rate for simultaneous approximation (\<open>j=1\<close>)\<close>

theory Simultaneous_Approximation_Rate
  imports Simultaneous_Approximation Forward_Difference_Consistency
begin

text \<open>
  Theorem 4.2 of Costarelli and Spigler~\cite{CostarelliSpigler} (p.180): for \<open>\<sigma>\<close> a bounded
  sigmoidal function, \<open>f \<in> C\<^sup>n\<^sup>+\<^sup>1[a,b]\<close> and \<open>j\<close> fixed, for every \<open>N > j+3\<close> there is \<open>w\<^sub>0>0\<close> such
  that for all \<open>w \<ge> w\<^sub>0\<close>,
  \<open>\<parallel>G\<^sup>j\<^sub>N f - f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity> < (1/N)[L\<^sub>j(b-a)(2\<parallel>\<sigma>\<parallel>\<^sub>\<infinity>+1+max{2,j}) + Ctilde\<^sub>j(b-a)(4\<parallel>\<sigma>\<parallel>\<^sub>\<infinity>+3) + \<parallel>f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity>]\<close>,
  where \<open>Ctilde\<^sub>j\<close> is the constant of (4.4) and \<open>L\<^sub>j\<close> a Lipschitz constant for \<open>f\<^sup>(\<^sup>j\<^sup>)\<close>.

  This theory does the \<open>j=1\<close> case, where \<open>max{2,j}=2\<close>.  It stands to
  \<open>forward_diff_one_approximation\<close> (Theorem 4.1, \<open>j=1\<close>) exactly as Theorem 5.2
  (\<^file>\<open>Multivariate_Holder_Rate.thy\<close>) stands to Theorem 5.1: the same case split, but every
  \<open>\<eta>\<close> replaced by an explicit constant.  The existing \<open>j=1\<close> development is \<^emph>\<open>already\<close> quantitative
  one layer down -- \<open>forward_diff_one_J1_sum_bound\<close> produces honest numeric bounds -- and only
  collapses to \<open>\<eta>\<close> at the \<open>*_eta_bound\<close> layer.  So the refinement re-derives that layer keeping
  \<open>1/N\<close> and \<open>C\<^sub>1 h\<close> explicit, and leaves every lemma below it untouched.

  Constants, in this theory's notation, both taken from what the existing development already
  produces rather than introduced as new definitions:
  \<^item> \<open>C\<^sub>1 = Sup {\<bar>f''(t)\<bar> | t\<in>[a,b]}\<close>.  This is simultaneously a Lipschitz constant for \<open>f'\<close>
    (\<open>deriv_lipschitz_bound\<close>, \<^file>\<open>Derivative_Approximation.thy\<close>), so \<open>L\<^sub>1 = C\<^sub>1\<close>; and by
    \<open>forward_diff_one_error_bound\<close> the constant of (4.4) is \<open>Ctilde\<^sub>1 = C\<^sub>1/2\<close>.
  \<^item> \<open>M\<^sub>1 = Sup {\<bar>f'(t)\<bar> | t\<in>[a,b]} = \<parallel>f'\<parallel>\<^sub>\<infinity>\<close>.
  With \<open>L\<^sub>1 = C\<^sub>1\<close> and \<open>Ctilde\<^sub>1 = C\<^sub>1/2\<close> the paper's \<open>J\<^sub>1\<close> constant \<open>2Ctilde\<^sub>1(b-a) + L\<^sub>1(b-a) + \<parallel>f'\<parallel>\<^sub>\<infinity>\<close>
  becomes \<open>2C\<^sub>1(b-a) + M\<^sub>1\<close>, which is what the first lemma below establishes.
\<close>

subsection \<open>The \<open>J\<^sub>1\<close> sum at an explicit \<open>1/N\<close> rate\<close>

text \<open>
  The quantitative counterpart of \<open>forward_diff_one_J1_eta_bound\<close>: the same five-term total,
  scaled by the outer \<open>1/N\<close>, but bounded by an explicit constant over \<open>N\<close> instead of by
  \<open>\<eta>\<sqdot>(5/2+M\<^sub>1)\<close>.

  The paper absorbs its fourth term \<open>(1/N)\<bar>\<Delta>\<^sup>1\<^sub>0f - f'(x\<^sub>0)\<bar>\<close> (an \<open>O(1/N\<^sup>2)\<close> quantity) silently into
  the slack of its strict inequality.  That absorption is legitimate and is carried out
  explicitly here: the three \<open>M\<close>-indexed sums run over \<open>M < N\<close> terms, not \<open>N\<close>, and the resulting
  slack \<open>2(N-M)C\<^sub>1h \<ge> 2C\<^sub>1h\<close> comfortably covers the leftover \<open>(C\<^sub>1/2)h\<close>.  So the constant here is
  exactly the paper's, with no extra term.
\<close>
(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma forward_diff_one_J1_rate_bound:
  fixes a b :: real and N M :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes M_le_N: "M < N" and M_pos: "M \<ge> 1"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "(1 / real N) *
         ((\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
          + (\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>)
          + (\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
          + \<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar>
          + \<bar>deriv f (xs ! 1)\<bar>)
       \<le> (1 / real N) * (2 * C1 * (b - a) + M1)"
proof -
  have hpos: "h > 0"
    using h_pos[OF a_lt_b N_pos h_def] .
  have C1h_nonneg: "0 \<le> C1 * h"
    using order_trans[OF abs_ge_zero forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def
      Ck ab_subset, of 1]] N_pos
    unfolding C1_def by simp
  have C1_nonneg: "C1 \<ge> 0"
    using C1h_nonneg hpos by (simp add: zero_le_mult_iff)

  have sum_bound: "(\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
       + (\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>)
       + (\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
       + \<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar>
       + \<bar>deriv f (xs ! 1)\<bar>
       \<le> real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h)
       + (C1 / 2) * h + M1"
    unfolding C1_def M1_def
    using forward_diff_one_J1_sum_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset M_le_N M_pos]
    by simp

  text \<open>\<open>b-a = N h\<close>, so the whole \<open>C\<^sub>1\<close>-part of the bound is a multiple of \<open>C\<^sub>1 h\<close>.\<close>
  have ba: "b - a = real N * h"
    unfolding h_def using N_pos by simp

  have collapse: "real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h)
                    + (C1 / 2) * h + M1
                  \<le> 2 * C1 * (b - a) + M1"
  proof -
    have lhs_eq: "real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h)
                    + (C1 / 2) * h
                  = (C1 * h) * (2 * real M + 1 / 2)"
      by (simp add: field_simps)
    have rhs_eq: "2 * C1 * (b - a) = (C1 * h) * (2 * real N)"
      unfolding ba by (simp add: field_simps)
    have counts: "2 * real M + 1 / 2 \<le> 2 * real N"
    proof -
      have "real M + 1 \<le> real N" using M_le_N by simp
      then show ?thesis by simp
    qed
    have "(C1 * h) * (2 * real M + 1 / 2) \<le> (C1 * h) * (2 * real N)"
      using counts C1h_nonneg by (rule mult_left_mono)
    then show ?thesis
      unfolding lhs_eq rhs_eq by simp
  qed

  have "(1 / real N) *
         ((\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
          + (\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>)
          + (\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
          + \<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar>
          + \<bar>deriv f (xs ! 1)\<bar>)
      \<le> (1 / real N) *
         (real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h)
          + (C1 / 2) * h + M1)"
    using sum_bound N_pos by (intro mult_left_mono) auto
  also have "\<dots> \<le> (1 / real N) * (2 * C1 * (b - a) + M1)"
    using collapse N_pos by (intro mult_left_mono) auto
  finally show ?thesis .
qed

subsection \<open>Two small reusable facts\<close>

text \<open>\<open>C\<^sub>1\<close> is a supremum of absolute values, hence nonnegative; extracted here because the
  \<open>\<eta>\<close>-instantiations below all need it.\<close>
(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma C1_sup_nonneg:
  fixes a b :: real and f :: "real \<Rightarrow> real" and U :: "real set"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  shows "0 \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
proof -
  have ain: "a \<in> {a..b}" and bin: "b \<in> {a..b}" using a_lt_b by simp_all
  have "(0::real) \<le> \<bar>deriv f a - deriv f b\<bar>" by simp
  also have "\<dots> \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * \<bar>a - b\<bar>"
    using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b ain bin] .
  finally have "0 \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * \<bar>a - b\<bar>" .
  then show ?thesis using a_lt_b by (simp add: zero_le_mult_iff)
qed

text \<open>
  The \<open>\<sigma>\<close>-saturation clause for a \<^emph>\<open>given\<close> \<open>N\<close>.  Theorem 4.2 quantifies as ``for every \<open>N>j+3\<close>
  there is \<open>w\<^sub>0>0\<close> such that for all \<open>w \<ge> w\<^sub>0\<close>'', the opposite order from Theorem 4.1, which picks
  \<open>N\<close> from \<open>\<epsilon>\<close>.  This is exactly the part of \<open>forward_diff_one_approximation_preamble\<close> that does
  not depend on \<open>\<epsilon>\<close> or \<open>\<eta>\<close> at all, so it can be split off unchanged.
\<close>
(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma sigma_saturation_for_N:
  fixes a b h :: real and N :: nat and \<sigma> :: "real \<Rightarrow> real"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N"
  shows "\<exists>w0>0. \<forall>w \<ge> w0. \<forall>k < N + 2.
           (\<forall>x. x - unif_part a b N ! k \<ge> h
                 \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / real N)
           \<and> (\<forall>x. x - unif_part a b N ! k \<le> - h
                 \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / real N)"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have length_xs: "length (unif_part a b N) = N + 2"
    unfolding unif_part_def by simp
  from sigmoidal_function N_pos hpos have
    "\<exists>\<omega> > 0. \<forall>w \<ge> \<omega>. \<forall>k < length (unif_part a b N).
             (\<forall>x. x - unif_part a b N ! k \<ge> h
                   \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / N)
           \<and> (\<forall>x. x - unif_part a b N ! k \<le> - h
                   \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / N)"
    by (subst sigmoidal_uniform_approximation, simp_all)
  then show ?thesis
    unfolding length_xs by blast
qed

subsection \<open>Replacing uniform continuity of \<open>f'\<close> by its Lipschitz constant\<close>

text \<open>
  The three \<open>L\<close>-bound lemmas of \<^file>\<open>Simultaneous_Approximation.thy\<close> are stated against an
  abstract modulus-of-continuity pair \<open>(\<delta>,\<eta>)\<close> for \<open>f'\<close>, and each already carries its \<open>C\<^sub>1 h\<close> part
  explicitly; only the \<open>\<eta>\<close> part is qualitative.  Since \<open>f' \<in> C\<^sup>0\<^sup>,\<^sup>1[a,b]\<close> here -- with Lipschitz
  constant \<open>C\<^sub>1 = Sup\<bar>f''\<bar>\<close>, by \<open>deriv_lipschitz_bound\<close> -- that pair can be instantiated at the
  mesh scale, turning every \<open>\<eta>\<close> into an explicit multiple of \<open>h\<close>.

  \<open>\<delta> := 3h\<close> (which satisfies the lemmas' own \<open>2h<\<delta>\<close> requirement) and \<open>\<eta> := 3(C\<^sub>1+1)h\<close>.  The
  \<open>+1\<close> is what makes the inequality \<^emph>\<open>strict\<close>, as \<open>\<delta>_prop\<close> demands, in the degenerate case
  \<open>C\<^sub>1 = 0\<close> (\<open>f'\<close> constant); it costs only an additive \<open>3h\<close> in the final constant and keeps the
  rate exactly \<open>O(1/N)\<close>.
\<close>
(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma deriv_lipschitz_delta_prop:
  fixes a b h :: real and f :: "real \<Rightarrow> real" and U :: "real set"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  assumes h_pos: "0 < h"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h
           \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < 3 * (C1 + 1) * h"
proof -
  have ain: "a \<in> {a..b}" and bin: "b \<in> {a..b}" using a_lt_b by simp_all
  have C1_nonneg: "0 \<le> C1"
  proof -
    have "(0::real) \<le> \<bar>deriv f a - deriv f b\<bar>" by simp
    also have "\<dots> \<le> C1 * \<bar>a - b\<bar>"
      unfolding C1_def using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b ain bin] .
    finally have "0 \<le> C1 * \<bar>a - b\<bar>" .
    then show ?thesis using a_lt_b by (simp add: zero_le_mult_iff)
  qed
  show ?thesis
  proof (intro ballI impI)
    fix x y assume x_in: "x \<in> {a..b}" and y_in: "y \<in> {a..b}" and d: "\<bar>x - y\<bar> < 3 * h"
    have "\<bar>deriv f x - deriv f y\<bar> \<le> C1 * \<bar>x - y\<bar>"
      unfolding C1_def using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b x_in y_in] .
    also have "\<dots> \<le> C1 * (3 * h)"
      using d C1_nonneg by (intro mult_left_mono) auto
    also have "\<dots> < 3 * (C1 + 1) * h"
      using h_pos by (simp add: algebra_simps)
    finally show "\<bar>deriv f x - deriv f y\<bar> < 3 * (C1 + 1) * h" .
  qed
qed

text \<open>The three \<open>L\<close>-bounds at the mesh scale.  Generic interior case first.\<close>
(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma forward_diff_one_generic_L_rate_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes i_range: "i \<in> {2..N - 1}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))
          - deriv f x\<bar>
       \<le> 3 * (C1 + 1) * h * (1 + 2 * S) + C1 * h * (1 / 2 + 2 * S)"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have C1_nonneg: "0 \<le> C1"
  proof -
    have ain: "a \<in> {a..b}" and bin: "b \<in> {a..b}" using a_lt_b by simp_all
    have "(0::real) \<le> \<bar>deriv f a - deriv f b\<bar>" by simp
    also have "\<dots> \<le> C1 * \<bar>a - b\<bar>"
      unfolding C1_def using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b ain bin] .
    finally have "0 \<le> C1 * \<bar>a - b\<bar>" .
    then show ?thesis using a_lt_b by (simp add: zero_le_mult_iff)
  qed
  have \<eta>_pos: "3 * (C1 + 1) * h > 0" using C1_nonneg hpos by simp
  have \<delta>_pos: "(3 :: real) * h > 0" using hpos by simp
  have h_lt: "2 * h < 3 * h" using hpos by simp
  have dp: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h
              \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < 3 * (C1 + 1) * h"
    unfolding C1_def by (rule deriv_lipschitz_delta_prop[OF Ck ab_subset a_lt_b hpos])
  show ?thesis
    unfolding C1_def S_def
    using forward_diff_one_generic_L_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset
      bounded_sigmoidal \<eta>_pos \<delta>_pos dp h_lt i_range x_in_cell]
    unfolding C1_def by simp
qed

(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma forward_diff_one_left_boundary_L_rate_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes i_range: "i \<in> {1, 2}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h 1 1
           + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
           + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2)))
          - deriv f x\<bar>
       \<le> 3 * (C1 + 1) * h * (1 + 2 * S) + C1 * h * (1 / 2 + 2 * S)"
proof -
  have N_pos: "N > 0" using N_gt3 by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have C1_nonneg: "0 \<le> C1"
  proof -
    have ain: "a \<in> {a..b}" and bin: "b \<in> {a..b}" using a_lt_b by simp_all
    have "(0::real) \<le> \<bar>deriv f a - deriv f b\<bar>" by simp
    also have "\<dots> \<le> C1 * \<bar>a - b\<bar>"
      unfolding C1_def using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b ain bin] .
    finally have "0 \<le> C1 * \<bar>a - b\<bar>" .
    then show ?thesis using a_lt_b by (simp add: zero_le_mult_iff)
  qed
  have \<eta>_pos: "3 * (C1 + 1) * h > 0" using C1_nonneg hpos by simp
  have \<delta>_pos: "(3 :: real) * h > 0" using hpos by simp
  have h_lt: "2 * h < 3 * h" using hpos by simp
  have dp: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h
              \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < 3 * (C1 + 1) * h"
    unfolding C1_def by (rule deriv_lipschitz_delta_prop[OF Ck ab_subset a_lt_b hpos])
  show ?thesis
    unfolding C1_def S_def
    using forward_diff_one_left_boundary_L_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
      bounded_sigmoidal \<eta>_pos \<delta>_pos dp h_lt i_range x_in_cell]
    unfolding C1_def by simp
qed

(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma forward_diff_one_right_boundary_L_rate_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes x_in_cell: "x \<in> {xs ! N .. xs ! (N + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h 1 (N - 1)
           + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N)))
          - deriv f x\<bar>
       \<le> 3 * (C1 + 1) * h * (1 + S) + C1 * h * (1 / 2 + S)"
proof -
  have N_pos: "N > 0" using N_gt3 by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have C1_nonneg: "0 \<le> C1"
  proof -
    have ain: "a \<in> {a..b}" and bin: "b \<in> {a..b}" using a_lt_b by simp_all
    have "(0::real) \<le> \<bar>deriv f a - deriv f b\<bar>" by simp
    also have "\<dots> \<le> C1 * \<bar>a - b\<bar>"
      unfolding C1_def using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b ain bin] .
    finally have "0 \<le> C1 * \<bar>a - b\<bar>" .
    then show ?thesis using a_lt_b by (simp add: zero_le_mult_iff)
  qed
  have \<eta>_pos: "3 * (C1 + 1) * h > 0" using C1_nonneg hpos by simp
  have \<delta>_pos: "(3 :: real) * h > 0" using hpos by simp
  have h_lt: "2 * h < 3 * h" using hpos by simp
  have dp: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h
              \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < 3 * (C1 + 1) * h"
    unfolding C1_def by (rule deriv_lipschitz_delta_prop[OF Ck ab_subset a_lt_b hpos])
  show ?thesis
    unfolding C1_def S_def
    using forward_diff_one_right_boundary_L_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
      bounded_sigmoidal \<eta>_pos \<delta>_pos dp h_lt x_in_cell]
    unfolding C1_def by simp
qed

subsection \<open>The \<open>I\<^sub>1\<close> bounds at an explicit \<open>1/N\<close> rate\<close>

text \<open>
  The three \<open>I\<^sub>1\<close> lemmas of \<^file>\<open>Simultaneous_Approximation.thy\<close> all conclude \<open>< \<eta>\<sqdot>(5/2+M\<^sub>1)\<close>, and
  their \<open>\<eta>\<close> is constrained only by three inequalities: \<open>h C\<^sub>1 < \<eta>\<close>, \<open>1/N < \<eta>\<close>, and \<open>\<eta>\<close> being a
  modulus of continuity for \<open>f'\<close> at scale \<open>\<delta> > 2h\<close>.  A single choice satisfies all three at once
  and is itself \<open>O(1/N)\<close>:
  \<open>\<delta> := 3h\<close> and \<open>\<eta>\<^sub>N := (3C\<^sub>1(b-a)+2)/N\<close>.
  So no part of those (large) proofs has to be re-derived -- the rate versions are pure
  instantiations.  The \<open>3C\<^sub>1(b-a)\<close> is what the Lipschitz bound needs across a \<open>3h\<close> gap
  (\<open>C\<^sub>1\<sqdot>3h = 3C\<^sub>1(b-a)/N\<close>); the \<open>+2\<close> dominates the \<open>1/N\<close> requirement and makes every inequality
  strict.
\<close>
(* Auxiliary for Theorem 4.2, first-derivative case; not separately numbered. *)
lemma eta_N_facts:
  fixes a b h :: real and N :: nat and f :: "real \<Rightarrow> real" and U :: "real set"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "\<eta>N \<equiv> (3 * C1 * (b - a) + 2) / real N"
  shows "0 < \<eta>N"
    and "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>N"
    and "h * C1 < \<eta>N"
    and "1 / real N < \<eta>N"
proof -
  have C1_nonneg: "0 \<le> C1"
    unfolding C1_def by (rule C1_sup_nonneg[OF Ck ab_subset a_lt_b])
  have ba_pos: "0 < b - a" using a_lt_b by simp
  have Npos: "0 < real N" using N_pos by simp
  text \<open>The one product-positivity fact every branch below needs; \<open>simp\<close> does not get it
    from \<open>0 \<le> C\<^sub>1\<close> and \<open>a < b\<close> on its own.\<close>
  have prod_nonneg: "0 \<le> C1 * (b - a)"
    using C1_nonneg ba_pos by (intro mult_nonneg_nonneg) auto
  have num_pos: "0 < 3 * C1 * (b - a) + 2"
    using prod_nonneg by simp
  show eta_pos: "0 < \<eta>N"
    unfolding \<eta>N_def using num_pos Npos by simp

  show "h * C1 < \<eta>N"
  proof -
    have "h * C1 = C1 * (b - a) / real N"
      unfolding h_def by simp
    also have "\<dots> < (3 * C1 * (b - a) + 2) / real N"
      using prod_nonneg Npos by (simp add: divide_strict_right_mono)
    finally show ?thesis unfolding \<eta>N_def .
  qed

  show "1 / real N < \<eta>N"
  proof -
    have "(1::real) < 3 * C1 * (b - a) + 2"
      using prod_nonneg by simp
    then show ?thesis
      unfolding \<eta>N_def using Npos by (simp add: divide_strict_right_mono)
  qed

  show "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>N"
  proof (intro ballI impI)
    fix x y assume x_in: "x \<in> {a..b}" and y_in: "y \<in> {a..b}" and d: "\<bar>x - y\<bar> < 3 * h"
    have "\<bar>deriv f x - deriv f y\<bar> \<le> C1 * \<bar>x - y\<bar>"
      unfolding C1_def using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b x_in y_in] .
    also have "\<dots> \<le> C1 * (3 * h)"
      using d C1_nonneg by (intro mult_left_mono) auto
    also have "\<dots> = 3 * C1 * (b - a) / real N"
      unfolding h_def by simp
    also have "\<dots> < \<eta>N"
      unfolding \<eta>N_def using Npos by (simp add: divide_strict_right_mono)
    finally show "\<bar>deriv f x - deriv f y\<bar> < \<eta>N" using prod_nonneg by simp
  qed
qed

subsection \<open>Theorem 4.2 for \<open>j = 1\<close>\<close>

text \<open>
  The assembly.  Because \<open>\<eta>\<^sub>N\<close> satisfies every constraint the \<open>j=1\<close> development already places on
  its abstract \<open>\<eta>\<close> (\<open>eta_N_facts\<close>), the case dispatch of \<open>forward_diff_one_approximation\<close>
  (Theorem 4.1) goes through verbatim with \<open>\<eta> := \<eta>\<^sub>N\<close> and \<open>\<delta> := 3h\<close>, and its final collapse
  \<open>I\<^sub>1+J\<^sub>2 < \<eta>(4+M\<^sub>1+4S)\<close> becomes an explicit \<open>O(1/N)\<close> bound.  Nothing below the \<open>*_eta_bound\<close>
  layer is re-derived.

  Note the quantifier order, which is Theorem 4.2's and \<^emph>\<open>not\<close> Theorem 4.1's: \<open>N\<close> is given first
  and \<open>w\<^sub>0\<close> depends on it, with the estimate holding for every \<open>w \<ge> w\<^sub>0\<close>.

  Two deliberate divergences from the paper's printed statement, both in the safe direction:
  \<^item> the paper requires \<open>N > j+3 = 4\<close>; this development needs only \<open>N > 3\<close>, inherited from
    Theorem 4.1's own hypothesis.
  \<^item> the constant is \<open>(3C\<^sub>1(b-a)+2)(4+M\<^sub>1+4S)\<close> rather than the paper's
    \<open>L\<^sub>1(b-a)(2S+3) + Ctilde\<^sub>1(b-a)(4S+3) + M\<^sub>1\<close>.  Both are \<open>O(1)\<close>, so the \<open>O(1/N)\<close> rate --
    the actual content of the theorem -- is identical.  The divergence is the same phenomenon
    already recorded for Theorem 5.2: this project's route reaches the bound through its own
    \<open>\<eta>\<close>-parametrised lemmas rather than by transcribing the paper's per-term grouping.
    \<open>forward_diff_one_J1_rate_bound\<close> and the three \<open>*_L_rate_bound\<close> lemmas above record the
    paper's own per-piece constants (its \<open>J\<^sub>1\<close> bound is matched exactly), for comparison.
\<close>
(* Theorem 4.2: first-derivative rate, with the explicit constant derived here. *)
theorem forward_diff_one_rate:
  fixes a b :: real and N :: nat and f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and U :: "real set"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes N_gt3: "N > 3"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  shows "\<exists>w0>0. \<forall>w \<ge> w0. \<forall>x \<in> {a..b}.
           \<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N 1 w x - deriv f x\<bar>
             < ((3 * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * (b - a) + 2)
                * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)))
               / real N"
proof -
  have N_pos: "N > 0" using N_gt3 by simp
  define h where h_def: "h = (b - a) / real N"
  define xs where xs_def: "xs = unif_part a b N"
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  define C1 where C1_def: "C1 = Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  define M1 where M1_def: "M1 = Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  define S where S_def: "S = Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  define \<eta>N where \<eta>N_def: "\<eta>N = (3 * C1 * (b - a) + 2) / real N"

  have S_nonneg: "S \<ge> 0"
    using bounded_sigmoidal unfolding bounded_function_def S_def
    by (meson UNIV_I abs_ge_zero cSUP_upper2)

  text \<open>The four \<open>\<eta>\<close>-constraints, all met by \<open>\<eta>\<^sub>N\<close> at \<open>\<delta> = 3h\<close>.\<close>
  have \<eta>_pos: "\<eta>N > 0"
    unfolding \<eta>N_def C1_def by (rule eta_N_facts(1)[OF a_lt_b N_pos h_def Ck ab_subset])
  have \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < 3 * h
                  \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>N"
    unfolding \<eta>N_def C1_def by (rule eta_N_facts(2)[OF a_lt_b N_pos h_def Ck ab_subset])
  have hC1_lt_\<eta>: "h * C1 < \<eta>N"
    unfolding \<eta>N_def C1_def by (rule eta_N_facts(3)[OF a_lt_b N_pos h_def Ck ab_subset])
  have N_inv_lt_\<eta>: "1 / real N < \<eta>N"
    unfolding \<eta>N_def C1_def by (rule eta_N_facts(4)[OF a_lt_b N_pos h_def Ck ab_subset])
  have \<delta>_pos: "(3::real) * h > 0" using hpos by simp
  have h_lt: "2 * h < 3 * h" using hpos by simp
  have hC1_lt_\<eta>': "h * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>N"
    using hC1_lt_\<eta> unfolding C1_def .

  text \<open>The \<open>\<sigma>\<close>-saturation threshold for this \<open>N\<close>.\<close>
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
            \<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N 1 w x - deriv f x\<bar>
              < ((3 * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * (b - a) + 2)
                 * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)))
                / real N"
    proof (intro allI impI ballI)
      fix w :: real and x :: real
      assume w_ge: "w0 \<le> w" and x_in_ab: "x \<in> {a..b}"
      have sat_clause': "\<forall>k < N + 2.
              (\<forall>y. y - xs ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
            \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
        using sat w_ge by blast

      obtain i where i_range: "i \<in> {1..N}" and x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
        using exists_containing_interval[OF a_lt_b N_pos h_def xs_def x_in_ab] by blast

      have goal: "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar> < \<eta>N * (4 + M1 + 4 * S)"
      proof (cases "i < 3")
        case True
        then have i_in: "i \<in> {1, 2}" using i_range by auto
        define Li where "Li = forward_diff f xs h 1 1
            + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
            + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2))"
        have J2: "\<bar>Li - deriv f x\<bar>
                    \<le> \<eta>N * (1 + 2 * S)
                      + Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + 2 * S)"
          unfolding Li_def S_def
          using forward_diff_one_left_boundary_L_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
            bounded_sigmoidal \<eta>_pos \<delta>_pos \<delta>_prop h_lt i_in x_in_cell] .
        have I1: "\<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> < \<eta>N * (5 / 2 + M1)"
          unfolding Li_def M1_def
          using forward_diff_one_I1_left_boundary_eta_bound[OF a_lt_b N_gt3 h_def xs_def Ck
            ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt hC1_lt_\<eta>' N_inv_lt_\<eta> sat_clause' i_in x_in_cell] .
        have C1h_bound: "Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + 2 * S)
                           < \<eta>N * (1 / 2 + 2 * S)"
        proof -
          have "0 < 1 / 2 + 2 * S" using S_nonneg by simp
          then show ?thesis
            using mult_strict_right_mono[OF hC1_lt_\<eta>'] by (simp add: mult.commute)
        qed
        have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
            \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>"
          using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N 1 w x - Li" "Li - deriv f x"]
          by simp
        also have "\<dots> < \<eta>N * (5 / 2 + M1) + (\<eta>N * (1 + 2 * S) + \<eta>N * (1 / 2 + 2 * S))"
          using I1 J2 C1h_bound by linarith
        also have "\<dots> = \<eta>N * (4 + M1 + 4 * S)"
          by (simp add: algebra_simps)
        finally show ?thesis .
      next
        case False
        then show ?thesis
        proof (cases "i = N")
          case True
          define Li where "Li = forward_diff f xs h 1 (N - 1)
              + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N))"
          have x_in_cellN: "x \<in> {xs ! N .. xs ! (N + 1)}" using x_in_cell True by simp
          have J2: "\<bar>Li - deriv f x\<bar>
                      \<le> \<eta>N * (1 + S)
                        + Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + S)"
            unfolding Li_def S_def
            using forward_diff_one_right_boundary_L_bound[OF a_lt_b N_gt3 h_def xs_def Ck
              ab_subset bounded_sigmoidal \<eta>_pos \<delta>_pos \<delta>_prop h_lt x_in_cellN] .
          have I1: "\<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> < \<eta>N * (5 / 2 + M1)"
            unfolding Li_def M1_def
            using forward_diff_one_I1_right_boundary_eta_bound[OF a_lt_b N_gt3 h_def xs_def Ck
              ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt hC1_lt_\<eta>' N_inv_lt_\<eta> sat_clause' x_in_cellN] .
          have C1h_bound: "Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + S)
                             < \<eta>N * (1 / 2 + S)"
          proof -
            have "0 < 1 / 2 + S" using S_nonneg by simp
            then show ?thesis
              using mult_strict_right_mono[OF hC1_lt_\<eta>'] by (simp add: mult.commute)
          qed
          have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
              \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>"
            using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N 1 w x - Li" "Li - deriv f x"]
            by simp
          also have "\<dots> < \<eta>N * (5 / 2 + M1) + (\<eta>N * (1 + S) + \<eta>N * (1 / 2 + S))"
            using I1 J2 C1h_bound by linarith
          also have "\<dots> \<le> \<eta>N * (4 + M1 + 4 * S)"
            using S_nonneg \<eta>_pos by (simp add: algebra_simps)
          finally show ?thesis .
        next
          case False
          then have i_in: "i \<in> {3..N - 1}" using i_range \<open>\<not> i < 3\<close> by auto
          have i_in2: "i \<in> {2..N - 1}" using i_in by auto
          define Li where "Li = forward_diff f xs h 1 (i - 1)
              + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
              + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i)
                  * \<sigma> (w * (x - xs ! (i + 1)))"
          have J2: "\<bar>Li - deriv f x\<bar>
                      \<le> \<eta>N * (1 + 2 * S)
                        + Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + 2 * S)"
            unfolding Li_def S_def
            using forward_diff_one_generic_L_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset
              bounded_sigmoidal \<eta>_pos \<delta>_pos \<delta>_prop h_lt i_in2 x_in_cell] .
          have I1: "\<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> < \<eta>N * (5 / 2 + M1)"
            unfolding Li_def M1_def
            using forward_diff_one_I1_generic_eta_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
              \<eta>_pos \<delta>_pos \<delta>_prop h_lt hC1_lt_\<eta>' N_inv_lt_\<eta> sat_clause' i_in x_in_cell] .
          have C1h_bound: "Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + 2 * S)
                             < \<eta>N * (1 / 2 + 2 * S)"
          proof -
            have "0 < 1 / 2 + 2 * S" using S_nonneg by simp
            then show ?thesis
              using mult_strict_right_mono[OF hC1_lt_\<eta>'] by (simp add: mult.commute)
          qed
          have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
              \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>"
            using abs_triangle_ineq[of "Gj_network \<sigma> f xs h N 1 w x - Li" "Li - deriv f x"]
            by simp
          also have "\<dots> < \<eta>N * (5 / 2 + M1) + (\<eta>N * (1 + 2 * S) + \<eta>N * (1 / 2 + 2 * S))"
            using I1 J2 C1h_bound by linarith
          also have "\<dots> = \<eta>N * (4 + M1 + 4 * S)"
            by (simp add: algebra_simps)
          finally show ?thesis .
        qed
      qed

      text \<open>\<open>unfolding\<close> rewrites the goal, not the cited fact, so the two must be brought
        together on the fact side: first replace \<open>\<eta>\<^sub>N\<close> by its closed form, then expand the
        local abbreviations inside the fact itself with an explicit \<open>[unfolded]\<close> attribute.\<close>
      have final_eq: "\<eta>N * (4 + M1 + 4 * S)
                        = ((3 * C1 * (b - a) + 2) * (4 + M1 + 4 * S)) / real N"
        unfolding \<eta>N_def by simp
      have goal2: "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
                     < ((3 * C1 * (b - a) + 2) * (4 + M1 + 4 * S)) / real N"
        using goal final_eq by linarith
      show "\<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N 1 w x - deriv f x\<bar>
              < ((3 * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * (b - a) + 2)
                 * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)))
                / real N"
        using goal2[unfolded h_def xs_def C1_def M1_def S_def] .
    qed
  qed
qed

end
