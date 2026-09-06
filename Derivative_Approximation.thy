section \<open>Simultaneous Approximation of a Function and its Derivatives\<close>

theory Derivative_Approximation
  imports Universal_Approximation_1d Partition_Facts
begin

text \<open>
  This theory formalizes Section 4 of Costarelli and Spigler~\cite{CostarelliSpigler}: the
  same construction that builds the network \<open>G_Nf\<close> approximating \<open>f\<close> uniformly (Theorem 2.1
  in theory Universal\_Approximation\_1d), still with the very same \<open>\<sigma>\<close>, approximates the
  \<open>j\<close>-th derivative of \<open>f\<close> with the \<open>same\<close> order of accuracy once the raw differences of
  \<open>f\<close>-values in its coefficients are replaced by differences of \<open>\<Delta>\<^sup>j f\<close>-values (Theorem 4.1,
  then quantified in Theorem 4.2).  (\<open>\<sigma>'\<close> only appears in the paper's discarded Remark 4.1
  approach of differentiating \<open>G_Nf\<close> itself, which the authors show does \<open>not\<close> achieve the
  right accuracy -- Theorem 4.1's actual network \<open>G_N\<^sup>j f\<close>, eq. (4.3), still uses \<open>\<sigma>\<close>.)

  The key ingredient is the forward finite-difference operator of (4.2): for a partition
  \<open>x\<^sub>-\<^sub>1,x\<^sub>0,\<dots>,x\<^sub>N\<close> with mesh width \<open>h\<close>,
  \<open>\<Delta>\<^sup>j\<^sub>k f := (1/h\<^sup>j) \<Sum>\<^sub>v\<^sub>=\<^sub>0\<^sup>j (j choose v)(-1)\<^sup>v f(x\<^sub>k\<^sub>+\<^sub>j\<^sub>-\<^sub>v)\<close>, which approximates the \<open>j\<close>-th
  derivative of \<open>f\<close> at \<open>x\<^sub>k\<close> to order \<open>h\<close>.  We build up its basic algebraic properties here
  before attempting Theorem 4.1 itself, in a later theory, so that each addition to this
  development compiles cleanly on its own.
\<close>

text \<open>
  The general derivative-chain fact that \<open>C1_cont_diff\<close> and \<open>C2_cont_diff\<close> (theory
  Real\_and\_Complex\_Analytic.Limits\_Higher\_Order\_Derivatives) each specialize for \<open>k=1,2\<close>:
  on \<open>C_k_on k f U\<close>, every derivative below order \<open>k\<close> is genuinely a derivative of the one
  before it, at every point of \<open>U\<close>.  This is exactly the hypothesis form used by the library's
  Lagrange-remainder theorem \<open>Taylor\<close> (theory \<open>HOL.MacLaurin\<close>).
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma Ck_on_derivative_chain:
  assumes ck: "C_k_on k f U" and mk: "m < k" and yU: "y \<in> U"
  shows "((deriv ^^ m) f has_real_derivative (deriv ^^ (Suc m)) f y) (at y)"
proof -
  have k_pos: "k \<noteq> 0"
    using mk by auto
  have openU: "open U"
    using ck k_pos unfolding C_k_on_def by (auto split: if_splits)
  have diff_on: "((deriv ^^ m) f) differentiable_on U"
    using ck k_pos mk unfolding C_k_on_def by (auto split: if_splits)
  have "((deriv ^^ m) f) differentiable (at y)"
    using diff_on yU openU by (simp add: differentiable_on_eq_differentiable_at)
  then have "DERIV ((deriv ^^ m) f) y :> deriv ((deriv ^^ m) f) y"
    using DERIV_deriv_iff_real_differentiable by blast
  then show ?thesis
    by simp
qed

text \<open>
  A standalone name for a fact used repeatedly (so far always inline) when adapting Theorem
  2.1's argument to \<open>f'\<close>: \<open>C_k_on 2 f U\<close> already bundles continuity of \<open>deriv f\<close>
  directly (it is exactly the \<open>n=0\<close> case of \<open>C_k_on\<close>'s own definition), so no derivative-chain
  argument like \<open>Ck_on_derivative_chain\<close> is even needed here.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma Ck_on_continuous_first_derivative:
  assumes "C_k_on 2 f U"
  shows "continuous_on U (deriv f)"
  using C2_cont_diff[OF assms] by (simp add: first_derivative_alt_def)

text \<open>
  The Lipschitz bound Theorem 4.2's proof needs for \<open>f'\<close> (paper: "as \<open>f^{(j)} \<in> C^{0,1}[a,b]\<close>,
  say \<open>L_j>0\<close> is the Lipschitz constant for \<open>f^{(j)}\<close>", p.181, used right after the \<open>J_1\<close>
  estimate). Unlike the paper, which takes the Lipschitz constant \<open>L_j\<close> as separately given, we
  do not need a new hypothesis for \<open>j=1\<close>: \<open>f'\<close> is automatically Lipschitz on \<open>[a,b]\<close> with
  constant \<open>C\<^sub>1\<close>, the supremum of \<open>|f''|\<close>, whenever \<open>C_k_on 2 f U\<close>, by the Mean Value Theorem (\<open>MVT2\<close>) applied
  to \<open>f'\<close> using \<open>Ck_on_derivative_chain\<close> for \<open>f'\<close>'s own derivative \<open>f''\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma deriv_lipschitz_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U" and a_lt_b: "a < b"
  assumes x_in: "x \<in> {a..b}" and y_in: "y \<in> {a..b}"
  shows "\<bar>deriv f x - deriv f y\<bar> \<le> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * \<bar>x - y\<bar>"
proof -
  obtain C1 where C1_def: "C1 = Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
    by blast
  have cont2: "continuous_on U ((deriv ^^ 2) f)"
  proof -
    have all_n: "\<forall>n<(2::nat). (deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
      using Ck unfolding C_k_on_def by simp
    have "(1::nat) < 2" by simp
    with all_n have "continuous_on U ((deriv ^^ (Suc 1)) f)" by blast
    then show ?thesis by (simp add: second_derivative_alt_def)
  qed
  have bdd: "bdd_above ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
    using a_lt_b cont2 ab_subset continuous_on_subset continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have key: "\<And>u v. u \<in> {a..b} \<Longrightarrow> v \<in> {a..b} \<Longrightarrow> u < v \<Longrightarrow> \<bar>deriv f u - deriv f v\<bar> \<le> C1 * (v - u)"
  proof -
    fix u v :: real
    assume u_in: "u \<in> {a..b}" and v_in: "v \<in> {a..b}" and u_lt_v: "u < v"
    have der: "\<And>t. u \<le> t \<Longrightarrow> t \<le> v \<Longrightarrow> DERIV (deriv f) t :> (deriv ^^ 2) f t"
    proof -
      fix t assume "u \<le> t" "t \<le> v"
      then have t_in_U: "t \<in> U"
        using u_in v_in ab_subset by auto
      have m_lt: "(1::nat) < 2" by simp
      have "((deriv ^^ 1) f has_real_derivative (deriv ^^ 2) f t) (at t)"
        using Ck_on_derivative_chain[OF Ck m_lt t_in_U] by (simp add: second_derivative_alt_def)
      then show "DERIV (deriv f) t :> (deriv ^^ 2) f t"
        by simp
    qed
    obtain z where z_bound: "u < z" "z < v" and mvt_eq: "deriv f v - deriv f u = (v - u) * (deriv ^^ 2) f z"
      using MVT2[OF u_lt_v der] by blast
    have z_in_ab: "z \<in> {a..b}"
      using u_in v_in z_bound by auto
    have "\<bar>deriv f u - deriv f v\<bar> = \<bar>(v - u) * (deriv ^^ 2) f z\<bar>"
      using mvt_eq by linarith
    also have "\<dots> = (v - u) * \<bar>(deriv ^^ 2) f z\<bar>"
      using u_lt_v by (simp add: abs_mult)
    also have "\<dots> \<le> (v - u) * C1"
      unfolding C1_def using u_lt_v cSUP_upper[OF z_in_ab bdd] by (intro mult_left_mono) auto
    finally show "\<bar>deriv f u - deriv f v\<bar> \<le> C1 * (v - u)"
      by (simp add: mult.commute)
  qed
  show ?thesis
    unfolding C1_def[symmetric]
  proof (cases x y rule: linorder_cases)
    case less
    then show "\<bar>deriv f x - deriv f y\<bar> \<le> C1 * \<bar>x - y\<bar>"
      using key[OF x_in y_in less] by simp
  next
    case equal
    then show "\<bar>deriv f x - deriv f y\<bar> \<le> C1 * \<bar>x - y\<bar>"
      by simp
  next
    case greater
    then show "\<bar>deriv f x - deriv f y\<bar> \<le> C1 * \<bar>x - y\<bar>"
      using key[OF y_in x_in greater] by simp
  qed
qed

text \<open>
  The forward difference \<open>\<Delta>\<^sup>j\<^sub>k f\<close> of (4.2), parametrized directly by the partition list
  \<open>xs\<close> (as produced by \<open>unif_part\<close>) and mesh width \<open>h\<close>, rather than by \<open>a\<close>, \<open>b\<close>, \<open>N\<close>
  separately: this is the only quantity from Section 4 with no counterpart in Section 2, so
  it earns a definition, matching how \<open>unif_part\<close> and \<open>bounded_function\<close> were introduced
  for Section 2.
\<close>
(* Equation (4.2): forward differences. *)
definition forward_diff :: "(real \<Rightarrow> real) \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "forward_diff f xs h j k =
     (1 / h^j) * (\<Sum>v\<in>{0..j}. (real (j choose v)) * (-1)^v * f (xs ! (k + j - v)))"

text \<open>The \<open>j=0\<close> case of (4.2) is just \<open>f\<close> evaluated at the node, as it must be.\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_zero: "forward_diff f xs h 0 k = f (xs ! k)"
  unfolding forward_diff_def by simp

text \<open>
  The \<open>j=1\<close> case is the usual forward difference quotient
  \<open>(f(x\<^sub>k\<^sub>+\<^sub>1) - f(x\<^sub>k))/h\<close>, matching e.g. the \<open>G\<^sup>1\<^sub>Nf\<close> example on p.179 of the paper.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_one: "forward_diff f xs h 1 k = (f (xs ! (k + 1)) - f (xs ! k)) / h"
proof -
  have "(\<Sum>v\<in>{0..1::nat}. (real (1 choose v)) * (-1)^v * f (xs ! (k + 1 - v)))
      = f (xs ! (k + 1)) - f (xs ! k)"
    by (simp add: sum.atLeast0_atMost_Suc)
  then show ?thesis
    unfolding forward_diff_def by simp
qed

text \<open>
  The \<open>j=2\<close> case, needed below to extend (4.4) one step past \<open>j=1\<close>: the usual centred
  second difference \<open>(f(x\<^sub>k\<^sub>+\<^sub>2)-2f(x\<^sub>k\<^sub>+\<^sub>1)+f(x\<^sub>k))/h\<^sup>2\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_two: "forward_diff f xs h 2 k = (f (xs ! (k + 2)) - 2 * f (xs ! (k + 1)) + f (xs ! k)) / h\<^sup>2"
proof -
  have "(\<Sum>v\<in>{0..2::nat}. (real (2 choose v)) * (-1)^v * f (xs ! (k + 2 - v)))
      = f (xs ! (k + 2)) - 2 * f (xs ! (k + 1)) + f (xs ! k)"
    by (simp add: sum.atLeast0_atMost_Suc eval_nat_numeral)
  then show ?thesis
    unfolding forward_diff_def by (simp add: power2_eq_square)
qed

text \<open>
  The \<open>j=3\<close> case, extending (4.4) one more step: \<open>(f(x\<^sub>k\<^sub>+\<^sub>3)-3f(x\<^sub>k\<^sub>+\<^sub>2)+3f(x\<^sub>k\<^sub>+\<^sub>1)-f(x\<^sub>k))/h\<^sup>3\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_three:
  "forward_diff f xs h 3 k
     = (f (xs ! (k + 3)) - 3 * f (xs ! (k + 2)) + 3 * f (xs ! (k + 1)) - f (xs ! k)) / h ^ 3"
proof -
  have "(\<Sum>v\<in>{0..3::nat}. (real (3 choose v)) * (-1)^v * f (xs ! (k + 3 - v)))
      = f (xs ! (k + 3)) - 3 * f (xs ! (k + 2)) + 3 * f (xs ! (k + 1)) - f (xs ! k)"
    by (simp add: sum.atLeast0_atMost_Suc eval_nat_numeral)
  then show ?thesis
    unfolding forward_diff_def by simp
qed

text \<open>
  \<open>\<Delta>\<close> is linear in \<open>f\<close>: this is used repeatedly in Theorem 4.1's proof, where the network
  coefficients themselves are differences \<open>\<Delta>\<^sup>j\<^sub>k f - \<Delta>\<^sup>j\<^sub>k\<^sub>-\<^sub>1 f\<close> of (4.3).
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_add:
  "forward_diff (\<lambda>x. f x + g x) xs h j k = forward_diff f xs h j k + forward_diff g xs h j k"
  unfolding forward_diff_def by (simp add: sum.distrib ring_distribs mult.assoc)

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_scale:
  "forward_diff (\<lambda>x. c * f x) xs h j k = c * forward_diff f xs h j k"
  unfolding forward_diff_def by (simp add: sum_distrib_left mult.commute mult.left_commute)

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_diff:
  "forward_diff (\<lambda>x. f x - g x) xs h j k = forward_diff f xs h j k - forward_diff g xs h j k"
  using forward_diff_add[of f "\<lambda>x. - g x" xs h j k] forward_diff_scale[of "-1" g xs h j k]
  by simp

text \<open>
  The classical forward-difference recursion \<open>\<Delta>\<^sup>j\<^sup>+\<^sup>1_k f = (\<Delta>\<^sup>j_k\<^sub>+\<^sub>1 f - \<Delta>\<^sup>j_k f)/h\<close>: the
  \<open>(j+1)\<close>-th order difference is the first difference of the \<open>j\<close>-th order ones.  Not needed
  for the \<open>j=1\<close> case of (4.4) already proved below, but standard finite-difference calculus,
  and the natural route to (4.4) for general \<open>j\<close> by induction on \<open>j\<close> in a later theory.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_recursive:
  assumes h_nonzero: "h \<noteq> 0"
  shows "forward_diff f xs h (Suc j) k = (forward_diff f xs h j (Suc k) - forward_diff f xs h j k) / h"
proof -
  define D :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "D = (\<lambda>j k. \<Sum>v\<in>{0..j}. real (j choose v) * (-1)^v * f (xs ! (k + j - v)))"
  have D_eq: "\<And>j k. forward_diff f xs h j k = D j k / h^j"
    unfolding forward_diff_def D_def by simp

  have key: "D (Suc j) k = D j (Suc k) - D j k" for j k
  proof -
    have set0: "{0..Suc j} = insert 0 {1..Suc j}"
      by auto
    have peel0: "D (Suc j) k =
        f (xs ! (k + Suc j)) + (\<Sum>v\<in>{1..Suc j}. real (Suc j choose v) * (-1)^v * f (xs ! (k + Suc j - v)))"
      unfolding D_def set0 by (subst sum.insert) simp_all

    have image_eq: "Suc ` {0..j} = {1..Suc j}"
      by auto
    have bij: "bij_betw Suc {0..j} {1..Suc j}"
      unfolding bij_betw_def using image_eq by (simp add: inj_on_def)
    have reindex: "(\<Sum>v\<in>{1..Suc j}. real (Suc j choose v) * (-1)^v * f (xs ! (k + Suc j - v)))
                 = (\<Sum>w\<in>{0..j}. real (Suc j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + Suc j - Suc w)))"
      using sum.reindex_bij_betw[OF bij,
              of "\<lambda>v. real (Suc j choose v) * (-1)^v * f (xs ! (k + Suc j - v))"]
      by simp

    have pascal: "\<And>w. w \<in> {0..j} \<Longrightarrow>
        real (Suc j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + Suc j - Suc w))
      = real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))
      + real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))"
    proof -
      fix w :: nat assume "w \<in> {0..j}"
      have shift: "(Suc j choose Suc w) = (j choose w) + (j choose Suc w)"
        by simp
      have idx: "k + Suc j - Suc w = k + 1 + j - Suc w"
        by simp
      show "real (Suc j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + Suc j - Suc w))
          = real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))
          + real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))"
        unfolding idx shift by (simp add: ring_distribs)
    qed
    have split_step: "(\<Sum>w\<in>{0..j}. real (Suc j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + Suc j - Suc w)))
        = (\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))
                       + real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))"
      by (rule sum.cong) (use pascal in auto)
    have split_pascal: "(\<Sum>w\<in>{0..j}. real (Suc j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + Suc j - Suc w)))
        = (\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))
        + (\<Sum>w\<in>{0..j}. real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))"
      unfolding split_step by (rule sum.distrib)

    text \<open>The first piece is \<open>-D j k\<close>: it is (up to the sign from \<open>(-1)^(Suc w)\<close>) exactly the
      sum defining \<open>D j k\<close>, term by term.\<close>
    have piece1: "(\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))
                = - D j k"
    proof -
      have step: "(\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))
                = (\<Sum>w\<in>{0..j}. - (real (j choose w) * (-1)^w * f (xs ! (k + j - w))))"
      proof (rule sum.cong, simp)
        fix w :: nat assume "w \<in> {0..j}"
        have idx: "k + 1 + j - Suc w = k + j - w"
          by simp
        show "real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))
            = - (real (j choose w) * (-1)^w * f (xs ! (k + j - w)))"
          unfolding idx by simp
      qed
      also have "(\<Sum>w\<in>{0..j}. - (real (j choose w) * (-1)^w * f (xs ! (k + j - w))))
               = - (\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^w * f (xs ! (k + j - w)))"
        by (simp add: sum_negf)
      also have "(\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^w * f (xs ! (k + j - w))) = D j k"
        unfolding D_def ..
      finally show ?thesis
        unfolding step .
    qed

    text \<open>The second piece is \<open>D j (Suc k) - f(xs!(k+1+j))\<close>: reindex \<open>u := Suc w\<close> to land in
      the defining sum for \<open>D j (Suc k)\<close>, whose \<open>w=0\<close> term is exactly \<open>f(xs!(k+1+j))\<close>, and drop
      the vanishing \<open>u = Suc j\<close> term (since \<open>j choose Suc j = 0\<close>).\<close>
    have piece2: "(\<Sum>w\<in>{0..j}. real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))
                = D j (Suc k) - f (xs ! (k + 1 + j))"
    proof -
      have reindex2: "(\<Sum>w\<in>{0..j}. real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))
                    = (\<Sum>u\<in>{1..Suc j}. real (j choose u) * (-1)^u * f (xs ! (k + 1 + j - u)))"
        using sum.reindex_bij_betw[OF bij, of "\<lambda>u. real (j choose u) * (-1)^u * f (xs ! (k + 1 + j - u))"]
        by simp
      have extend: "(\<Sum>u\<in>{1..Suc j}. real (j choose u) * (-1)^u * f (xs ! (k + 1 + j - u)))
                  = (\<Sum>u\<in>{1..j}. real (j choose u) * (-1)^u * f (xs ! (k + 1 + j - u)))"
      proof (cases "j = 0")
        case True
        then show ?thesis by simp
      next
        case False
        then have set_eq: "{1..Suc j} = insert (Suc j) {1..j}"
          by auto
        show ?thesis
          unfolding set_eq by (subst sum.insert) simp_all
      qed
      have Dsk_split: "D j (Suc k)
          = f (xs ! (k + 1 + j)) + (\<Sum>u\<in>{1..j}. real (j choose u) * (-1)^u * f (xs ! (k + 1 + j - u)))"
      proof (cases "j = 0")
        case True
        then show ?thesis unfolding D_def by simp
      next
        case False
        then have set0j: "{0..j} = insert 0 {1..j}"
          by auto
        show ?thesis
          unfolding D_def set0j by (subst sum.insert) simp_all
      qed
      from reindex2 extend Dsk_split show ?thesis
        by simp
    qed

    have "D (Suc j) k = f (xs ! (k + Suc j))
        + ((\<Sum>w\<in>{0..j}. real (j choose w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w)))
           + (\<Sum>w\<in>{0..j}. real (j choose Suc w) * (-1)^(Suc w) * f (xs ! (k + 1 + j - Suc w))))"
      using peel0 reindex split_pascal by simp
    also have "\<dots> = f (xs ! (k + Suc j)) + (- D j k) + (D j (Suc k) - f (xs ! (k + 1 + j)))"
      using piece1 piece2 by simp
    also have "k + Suc j = k + 1 + j"
      by simp
    finally show ?thesis
      by simp
  qed

  have "forward_diff f xs h (Suc j) k = D (Suc j) k / h ^ (Suc j)"
    using D_eq by simp
  also have "\<dots> = (D j (Suc k) - D j k) / h ^ (Suc j)"
    using key by simp
  also have "\<dots> = (D j (Suc k) / h ^ j - D j k / h ^ j) / h"
    using h_nonzero by (simp add: diff_divide_distrib mult.commute)
  also have "\<dots> = (forward_diff f xs h j (Suc k) - forward_diff f xs h j k) / h"
    using D_eq by simp
  finally show ?thesis .
qed

text \<open>
  Equation (4.4) of the paper claims a constant \<open>C\<^sub>j\<close>, depending only on the \<open>(j+1)\<close>-th
  derivative of \<open>f\<close>, such that the forward difference approximates the \<open>j\<close>-th derivative to
  order \<open>h\<close>.  We prove this first for \<open>j=1\<close>, the base case needed for the induction to come.

  Rather than tracking \<open>f'\<close>, \<open>f''\<close> as separate hypotheses, we phrase this directly in terms
  of \<open>C_k_on\<close> and \<open>(deriv ^^ n) f\<close> from theory \<open>Limits_Higher_Order_Derivatives\<close> -- the same
  higher-differentiability infrastructure already used for \<open>\<sigma>\<close> throughout this development
  (and shared with the author's separate \<open>Higher_Diffs\<close> line of work, where the analogous
  \<open>Taylor\<close> theorem is likewise stated via iterated derivatives rather than named primes).
  This matches the paper's own hypothesis \<open>f \<in> \<^bold>C\<^sup>n\<^sup>+\<^sup>1[a,b]\<close> ("\<open>f \<in> C\<^sup>n\<^sup>+\<^sup>1(a',b')\<close> for some open
  \<open>(a',b') \<supseteq> [a,b]\<close>") directly: take \<open>U := (a',b')\<close>.  We still close the analytic core with the
  library's Lagrange-remainder theorem \<open>Taylor\<close> (theory \<open>HOL.MacLaurin\<close>) rather than reproving
  Taylor's theorem ourselves.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_one_taylor:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 2 f U"
  assumes seg: "{x0..x0 + h} \<subseteq> U"
  shows "\<exists>t. x0 < t \<and> t < x0 + h \<and>
             (f (x0 + h) - f x0) / h - deriv f x0 = (deriv ^^ 2) f t * h / 2"
proof -
  have INIT: "(2::nat) > 0" "(deriv ^^ 0) f = f"
    by simp_all
  have DERIV_hyp: "\<forall>m t. m < 2 \<and> x0 \<le> t \<and> t \<le> x0 + h
                     \<longrightarrow> DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
  proof (rule allI, rule allI, rule impI)
    fix m :: nat and t :: real
    assume "m < 2 \<and> x0 \<le> t \<and> t \<le> x0 + h"
    then show "DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
      using seg by (intro Ck_on_derivative_chain[OF Ck]) auto
  qed
  have INTERV: "x0 \<le> x0" "x0 \<le> x0 + h" "x0 \<le> x0 + h" "x0 + h \<le> x0 + h" "x0 + h \<noteq> x0"
    using h_pos by simp_all
  have Taylor_result: "\<exists>t. (if x0 + h < x0 then x0 + h < t \<and> t < x0 else x0 < t \<and> t < x0 + h) \<and>
        f (x0 + h) =
        (\<Sum>m<2. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 2) f t / fact 2) * ((x0 + h) - x0)^2"
    by (rule Taylor[OF INIT DERIV_hyp INTERV])
  obtain t where t_bound: "x0 < t \<and> t < x0 + h"
    and taylor_eq: "f (x0 + h) =
        (\<Sum>m<2. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 2) f t / fact 2) * ((x0 + h) - x0)^2"
    using Taylor_result h_pos by auto
  have sum_eq: "(\<Sum>m<2. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
              = f x0 + deriv f x0 * h"
    by (simp add: numeral_2_eq_2)
  have remainder_eq: "((deriv ^^ 2) f t / fact 2) * ((x0 + h) - x0)^2 = (deriv ^^ 2) f t * h\<^sup>2 / 2"
    by (simp add: numeral_2_eq_2)
  have "f (x0 + h) = f x0 + deriv f x0 * h + (deriv ^^ 2) f t * h\<^sup>2 / 2"
    using taylor_eq sum_eq remainder_eq by simp
  then have "(f (x0 + h) - f x0) / h = deriv f x0 + (deriv ^^ 2) f t * h / 2"
    using h_pos by (simp add: power2_eq_square field_simps)
  then show ?thesis
    using t_bound by auto
qed

text \<open>
  Corollary: if \<open>(deriv ^^ 2) f\<close> is additionally bounded by \<open>M\<close> on \<open>[x0,x0+h]\<close>, the
  forward difference quotient \<open>\<Delta>\<^sup>1_k f\<close> (\<^const>\<open>forward_diff\<close> with \<open>j=1\<close>) approximates
  \<open>f'(x0)\<close> to order \<open>h\<close> with constant \<open>M/2\<close>, matching (4.4) for \<open>j=1\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
corollary forward_diff_one_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 2 f U"
  assumes seg: "{x0..x0 + h} \<subseteq> U"
  assumes bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + h \<Longrightarrow> \<bar>(deriv ^^ 2) f t\<bar> \<le> M"
  shows "\<bar>(f (x0 + h) - f x0) / h - deriv f x0\<bar> \<le> (M / 2) * h"
proof -
  from forward_diff_one_taylor[OF h_pos Ck seg]
  obtain t where t_bound: "x0 < t" "t < x0 + h"
    and eq: "(f (x0 + h) - f x0) / h - deriv f x0 = (deriv ^^ 2) f t * h / 2"
    by blast
  have "\<bar>(f (x0 + h) - f x0) / h - deriv f x0\<bar> = \<bar>(deriv ^^ 2) f t\<bar> * h / 2"
    unfolding eq using h_pos by (simp add: abs_mult)
  also have "\<dots> \<le> M * h / 2"
    using bound[of t] t_bound h_pos by (simp add: mult_right_mono)
  finally show ?thesis
    by simp
qed

text \<open>
  Equation (4.4) for \<open>j=2\<close>: the general-\<open>j\<close> case is genuinely harder than a naive induction
  on \<open>j\<close> would suggest (see the note at \<open>forward_diff_recursive\<close>), but for a \<open>fixed\<close> small
  \<open>j\<close> the finitely many terms of \<open>\<Delta>\<^sup>j_k f\<close> can just be Taylor-expanded directly, exactly as
  \<open>forward_diff_one_taylor\<close> did for \<open>j=1\<close>: here, \<open>f(x\<^sub>0\<^sub>+\<^sub>h)\<close> and \<open>f(x\<^sub>0\<^sub>+\<^sub>2\<^sub>h)\<close> are each
  expanded to order \<open>3\<close> about \<open>x\<^sub>0\<close>, and the \<open>f(x\<^sub>0\<^sub>)\<close>, \<open>f'(x\<^sub>0\<^sub>)\<close> and \<open>f''(x\<^sub>0\<^sub>)\<close> terms cancel
  by direct arithmetic (no combinatorial identity needed, since there are only three terms to
  track for \<open>j=2\<close>), leaving a remainder of order \<open>h\<close> built from the two Lagrange points.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_two_taylor:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 3 f U"
  assumes seg: "{x0..x0 + 2 * h} \<subseteq> U"
  shows "\<exists>t1 t2. x0 < t1 \<and> t1 < x0 + h \<and> x0 < t2 \<and> t2 < x0 + 2 * h \<and>
             (f (x0 + 2 * h) - 2 * f (x0 + h) + f x0) / h\<^sup>2 - (deriv ^^ 2) f x0
               = (8 * (deriv ^^ 3) f t2 - 2 * (deriv ^^ 3) f t1) * h / 6"
proof -
  have INIT: "(3::nat) > 0" "(deriv ^^ 0) f = f"
    by simp_all
  have DERIV_hyp: "\<forall>m t. m < 3 \<and> x0 \<le> t \<and> t \<le> x0 + 2 * h
                     \<longrightarrow> DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
  proof (rule allI, rule allI, rule impI)
    fix m :: nat and t :: real
    assume "m < 3 \<and> x0 \<le> t \<and> t \<le> x0 + 2 * h"
    then show "DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
      using seg by (intro Ck_on_derivative_chain[OF Ck]) auto
  qed

  have INTERV1: "x0 \<le> x0" "x0 \<le> x0 + 2 * h" "x0 \<le> x0 + h" "x0 + h \<le> x0 + 2 * h" "x0 + h \<noteq> x0"
    using h_pos by simp_all
  have Taylor1: "\<exists>t. (if x0 + h < x0 then x0 + h < t \<and> t < x0 else x0 < t \<and> t < x0 + h) \<and>
        f (x0 + h) =
        (\<Sum>m<3. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 3) f t / fact 3) * ((x0 + h) - x0)^3"
    by (rule Taylor[OF INIT DERIV_hyp INTERV1])
  obtain t1 where t1_bound: "x0 < t1 \<and> t1 < x0 + h"
    and taylor1_eq: "f (x0 + h) =
        (\<Sum>m<3. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 3) f t1 / fact 3) * ((x0 + h) - x0)^3"
    using Taylor1 h_pos by auto

  have INTERV2: "x0 \<le> x0" "x0 \<le> x0 + 2 * h" "x0 \<le> x0 + 2 * h" "x0 + 2 * h \<le> x0 + 2 * h" "x0 + 2 * h \<noteq> x0"
    using h_pos by simp_all
  have Taylor2: "\<exists>t. (if x0 + 2 * h < x0 then x0 + 2 * h < t \<and> t < x0 else x0 < t \<and> t < x0 + 2 * h) \<and>
        f (x0 + 2 * h) =
        (\<Sum>m<3. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
          + ((deriv ^^ 3) f t / fact 3) * ((x0 + 2 * h) - x0)^3"
    by (rule Taylor[OF INIT DERIV_hyp INTERV2])
  obtain t2 where t2_bound: "x0 < t2 \<and> t2 < x0 + 2 * h"
    and taylor2_eq: "f (x0 + 2 * h) =
        (\<Sum>m<3. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
          + ((deriv ^^ 3) f t2 / fact 3) * ((x0 + 2 * h) - x0)^3"
    using Taylor2 h_pos by auto

  have sum1_eq: "(\<Sum>m<3. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
              = f x0 + deriv f x0 * h + (deriv ^^ 2) f x0 * h\<^sup>2 / 2"
    by (simp add: eval_nat_numeral)
  have sum2_eq: "(\<Sum>m<3. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
              = f x0 + deriv f x0 * (2 * h) + (deriv ^^ 2) f x0 * (2 * h)\<^sup>2 / 2"
    by (simp add: eval_nat_numeral)

  have e1: "f (x0 + h) = f x0 + deriv f x0 * h + (deriv ^^ 2) f x0 * h\<^sup>2 / 2
                        + (deriv ^^ 3) f t1 * h ^ 3 / 6"
    using taylor1_eq sum1_eq by (simp add: eval_nat_numeral)
  have e2: "f (x0 + 2 * h) = f x0 + deriv f x0 * (2 * h) + (deriv ^^ 2) f x0 * (2 * h)\<^sup>2 / 2
                        + (deriv ^^ 3) f t2 * (2 * h) ^ 3 / 6"
    using taylor2_eq sum2_eq by (simp add: eval_nat_numeral)

  have combine: "f (x0 + 2 * h) - 2 * f (x0 + h) + f x0
      = (deriv ^^ 2) f x0 * h\<^sup>2 + (8 * (deriv ^^ 3) f t2 - 2 * (deriv ^^ 3) f t1) * h ^ 3 / 6"
    using e1 e2 by (simp add: power2_eq_square field_simps)

  have "(f (x0 + 2 * h) - 2 * f (x0 + h) + f x0) / h\<^sup>2
      = (deriv ^^ 2) f x0 + (8 * (deriv ^^ 3) f t2 - 2 * (deriv ^^ 3) f t1) * h / 6"
    unfolding combine using h_pos by (simp add: add_divide_distrib power2_eq_square power3_eq_cube)
  then show ?thesis
    using t1_bound t2_bound by auto
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
corollary forward_diff_two_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 3 f U"
  assumes seg: "{x0..x0 + 2 * h} \<subseteq> U"
  assumes bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + 2 * h \<Longrightarrow> \<bar>(deriv ^^ 3) f t\<bar> \<le> M"
  shows "\<bar>(f (x0 + 2 * h) - 2 * f (x0 + h) + f x0) / h\<^sup>2 - (deriv ^^ 2) f x0\<bar> \<le> (5 * M / 3) * h"
proof -
  from forward_diff_two_taylor[OF h_pos Ck seg]
  obtain t1 t2 where bounds: "x0 < t1" "t1 < x0 + h" "x0 < t2" "t2 < x0 + 2 * h"
    and eq: "(f (x0 + 2 * h) - 2 * f (x0 + h) + f x0) / h\<^sup>2 - (deriv ^^ 2) f x0
               = (8 * (deriv ^^ 3) f t2 - 2 * (deriv ^^ 3) f t1) * h / 6"
    by blast
  have b1: "\<bar>(deriv ^^ 3) f t1\<bar> \<le> M"
    using bound[of t1] bounds h_pos by simp
  have b2: "\<bar>(deriv ^^ 3) f t2\<bar> \<le> M"
    using bound[of t2] bounds h_pos by simp
  have "\<bar>(f (x0 + 2 * h) - 2 * f (x0 + h) + f x0) / h\<^sup>2 - (deriv ^^ 2) f x0\<bar>
      = \<bar>8 * (deriv ^^ 3) f t2 - 2 * (deriv ^^ 3) f t1\<bar> * h / 6"
    unfolding eq using h_pos by (simp add: abs_mult)
  also have "\<dots> \<le> (8 * \<bar>(deriv ^^ 3) f t2\<bar> + 2 * \<bar>(deriv ^^ 3) f t1\<bar>) * h / 6"
    using h_pos by (simp add: mult_right_mono)
  also have "\<dots> \<le> (8 * M + 2 * M) * h / 6"
    using b1 b2 h_pos by (simp add: mult_left_mono mult_right_mono)
  also have "\<dots> = (5 * M / 3) * h"
    by simp
  finally show ?thesis .
qed

text \<open>
  The telescoping identity used repeatedly in Theorem 4.1's proof (e.g. the step
  "\<open>\<Sum>\<^sub>k\<^sub>=\<^sub>1\<^sup>i\<^sup>-\<^sup>2 (\<Delta>\<^sup>j\<^sub>k f - \<Delta>\<^sup>j\<^sub>k\<^sub>-\<^sub>1 f) + \<Delta>\<^sup>j\<^sub>0 f = \<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>2 f\<close>" on p.177): a sum of consecutive
  differences of \<open>\<Delta>\<^sup>j f\<close> telescopes back down to the two endpoint values.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_telescope:
  "(\<Sum>k=1..m. (forward_diff f xs h j k - forward_diff f xs h j (k - 1))) + forward_diff f xs h j 0
     = forward_diff f xs h j m"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have insert_eq: "{1..Suc m} = insert (Suc m) {1..m}"
    by auto
  have "(\<Sum>k=1..Suc m. (forward_diff f xs h j k - forward_diff f xs h j (k - 1)))
      = (forward_diff f xs h j (Suc m) - forward_diff f xs h j m)
        + (\<Sum>k=1..m. (forward_diff f xs h j k - forward_diff f xs h j (k - 1)))"
    unfolding insert_eq by (subst sum.insert) simp_all
  then show ?case
    using Suc.IH by simp
qed

text \<open>
  Uniform form of (4.4) for \<open>j=1\<close>: a single constant \<open>C\<^sub>1\<close>, depending only on \<open>(deriv ^^ 2) f\<close>
  via its supremum over the whole interval \<open>[a,b]\<close>, bounds the truncation error for every
  subinterval \<open>[x0,x0+h] \<subseteq> [a,b]\<close> -- matching the paper's own \<open>C\<^sub>j = C\<^sub>j(f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>),a,b)\<close>, "a fixed
  constant that will be determined later" (p.177), rather than one constant per subinterval.
  Note that \<open>C_k_on\<close> already bundles the needed continuity of \<open>(deriv ^^ 2) f\<close> on \<open>U\<close>, so
  unlike the \<open>f',f''\<close>-based formulation this needs no separate continuity hypothesis.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_one_uniform_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes h_pos: "0 < h"
  assumes x0_in: "x0 \<in> {a..b}" "x0 + h \<in> {a..b}"
  shows "\<bar>(f (x0 + h) - f x0) / h - deriv f x0\<bar>
           \<le> (Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) / 2) * h"
proof -
  have all_n: "\<forall>n<(2::nat). (deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
    using Ck unfolding C_k_on_def by simp
  have cont_on_U: "continuous_on U ((deriv ^^ 2) f)"
  proof -
    have "(1::nat) < 2" by simp
    with all_n have "continuous_on U ((deriv ^^ (Suc 1)) f)" by blast
    then show ?thesis by (simp add: second_derivative_alt_def)
  qed
  have cont: "continuous_on {a..b} ((deriv ^^ 2) f)"
    using cont_on_U ab_subset continuous_on_subset by blast
  (* (deriv ^^ 2) f is continuous on the compact [a,b], hence bounded there: the same
     pattern used throughout Universal_Approximation_1d.thy for bounding \<sigma> and f. *)
  have bdd: "bdd_above ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b})"
    using a_lt_b cont continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + h \<Longrightarrow> \<bar>(deriv ^^ 2) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b})"
  proof -
    fix t assume t_bounds: "x0 \<le> t" "t \<le> x0 + h"
    have t_in_ab: "t \<in> {a..b}"
      using t_bounds x0_in by auto
    show "\<bar>(deriv ^^ 2) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b})"
      by (rule cSUP_upper[OF t_in_ab bdd])
  qed
  have seg: "{x0..x0 + h} \<subseteq> U"
    using x0_in ab_subset by auto
  show ?thesis
    by (rule forward_diff_one_error_bound[OF h_pos Ck seg bound])
qed

text \<open>
  Uniform form of (4.4) for \<open>j=2\<close>, the exact analogue of
  \<open>forward_diff_one_uniform_error_bound\<close>: a single constant, depending only on the supremum of
  \<open>(deriv ^^ 3) f\<close> over \<open>[a,b]\<close>, bounds the second-difference truncation error on every
  subinterval \<open>[x0,x0+2h] \<subseteq> [a,b]\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_two_uniform_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 3 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes h_pos: "0 < h"
  assumes x0_in: "x0 \<in> {a..b}" "x0 + 2 * h \<in> {a..b}"
  shows "\<bar>(f (x0 + 2 * h) - 2 * f (x0 + h) + f x0) / h\<^sup>2 - (deriv ^^ 2) f x0\<bar>
           \<le> (5 * Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b}) / 3) * h"
proof -
  have all_n: "\<forall>n<(3::nat). (deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
    using Ck unfolding C_k_on_def by simp
  have cont_on_U: "continuous_on U ((deriv ^^ 3) f)"
  proof -
    have "(2::nat) < 3" by simp
    with all_n have "continuous_on U ((deriv ^^ (Suc 2)) f)" by blast
    then show ?thesis by simp
  qed
  have cont: "continuous_on {a..b} ((deriv ^^ 3) f)"
    using cont_on_U ab_subset continuous_on_subset by blast
  have bdd: "bdd_above ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b})"
    using a_lt_b cont continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + 2 * h \<Longrightarrow> \<bar>(deriv ^^ 3) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b})"
  proof -
    fix t assume t_bounds: "x0 \<le> t" "t \<le> x0 + 2 * h"
    have t_in_ab: "t \<in> {a..b}"
      using t_bounds x0_in by auto
    show "\<bar>(deriv ^^ 3) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b})"
      by (rule cSUP_upper[OF t_in_ab bdd])
  qed
  have seg: "{x0..x0 + 2 * h} \<subseteq> U"
    using x0_in ab_subset by auto
  show ?thesis
    by (rule forward_diff_two_error_bound[OF h_pos Ck seg bound])
qed

text \<open>
  Equation (4.4) for \<open>j=3\<close>, by the same brute-force per-term Taylor expansion as \<open>j=2\<close> (three
  applications of \<open>Taylor\<close>, to order \<open>4\<close>, at \<open>h\<close>, \<open>2h\<close>, \<open>3h\<close>): the \<open>f\<close>, \<open>f'\<close>, \<open>f''\<close> terms
  cancel (coefficients \<open>1-3+3-1=0\<close>, \<open>3-12+9=0\<close> after the \<open>h\<close>/\<open>h\<^sup>2\<close> factors, etc.), the \<open>f'''\<close>
  term survives with coefficient exactly \<open>h\<^sup>3\<close> (\<open>27-24+3=6=3!\<close>), and the remainder is a
  combination of three Lagrange points at order \<open>h\<^sup>4\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_three_taylor:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 4 f U"
  assumes seg: "{x0..x0 + 3 * h} \<subseteq> U"
  shows "\<exists>t1 t2 t3. x0 < t1 \<and> t1 < x0 + h \<and> x0 < t2 \<and> t2 < x0 + 2 * h \<and>
                     x0 < t3 \<and> t3 < x0 + 3 * h \<and>
             (f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0) / h ^ 3
               - (deriv ^^ 3) f x0
               = (81 * (deriv ^^ 4) f t3 - 48 * (deriv ^^ 4) f t2
                    + 3 * (deriv ^^ 4) f t1) * h / 24"
proof -
  have INIT: "(4::nat) > 0" "(deriv ^^ 0) f = f"
    by simp_all
  have DERIV_hyp: "\<forall>m t. m < 4 \<and> x0 \<le> t \<and> t \<le> x0 + 3 * h
                     \<longrightarrow> DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
  proof (rule allI, rule allI, rule impI)
    fix m :: nat and t :: real
    assume "m < 4 \<and> x0 \<le> t \<and> t \<le> x0 + 3 * h"
    then show "DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
      using seg by (intro Ck_on_derivative_chain[OF Ck]) auto
  qed

  have INTERV1: "x0 \<le> x0" "x0 \<le> x0 + 3 * h" "x0 \<le> x0 + h" "x0 + h \<le> x0 + 3 * h" "x0 + h \<noteq> x0"
    using h_pos by simp_all
  have Taylor1: "\<exists>t. (if x0 + h < x0 then x0 + h < t \<and> t < x0 else x0 < t \<and> t < x0 + h) \<and>
        f (x0 + h) =
        (\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 4) f t / fact 4) * ((x0 + h) - x0)^4"
    by (rule Taylor[OF INIT DERIV_hyp INTERV1])
  obtain t1 where t1_bound: "x0 < t1 \<and> t1 < x0 + h"
    and taylor1_eq: "f (x0 + h) =
        (\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 4) f t1 / fact 4) * ((x0 + h) - x0)^4"
    using Taylor1 h_pos by auto

  have INTERV2: "x0 \<le> x0" "x0 \<le> x0 + 3 * h" "x0 \<le> x0 + 2 * h" "x0 + 2 * h \<le> x0 + 3 * h" "x0 + 2 * h \<noteq> x0"
    using h_pos by simp_all
  have Taylor2: "\<exists>t. (if x0 + 2 * h < x0 then x0 + 2 * h < t \<and> t < x0 else x0 < t \<and> t < x0 + 2 * h) \<and>
        f (x0 + 2 * h) =
        (\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
          + ((deriv ^^ 4) f t / fact 4) * ((x0 + 2 * h) - x0)^4"
    by (rule Taylor[OF INIT DERIV_hyp INTERV2])
  obtain t2 where t2_bound: "x0 < t2 \<and> t2 < x0 + 2 * h"
    and taylor2_eq: "f (x0 + 2 * h) =
        (\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
          + ((deriv ^^ 4) f t2 / fact 4) * ((x0 + 2 * h) - x0)^4"
    using Taylor2 h_pos by auto

  have INTERV3: "x0 \<le> x0" "x0 \<le> x0 + 3 * h" "x0 \<le> x0 + 3 * h" "x0 + 3 * h \<le> x0 + 3 * h" "x0 + 3 * h \<noteq> x0"
    using h_pos by simp_all
  have Taylor3: "\<exists>t. (if x0 + 3 * h < x0 then x0 + 3 * h < t \<and> t < x0 else x0 < t \<and> t < x0 + 3 * h) \<and>
        f (x0 + 3 * h) =
        (\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + 3 * h) - x0)^m)
          + ((deriv ^^ 4) f t / fact 4) * ((x0 + 3 * h) - x0)^4"
    by (rule Taylor[OF INIT DERIV_hyp INTERV3])
  obtain t3 where t3_bound: "x0 < t3 \<and> t3 < x0 + 3 * h"
    and taylor3_eq: "f (x0 + 3 * h) =
        (\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + 3 * h) - x0)^m)
          + ((deriv ^^ 4) f t3 / fact 4) * ((x0 + 3 * h) - x0)^4"
    using Taylor3 h_pos by auto

  have sum1_eq: "(\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
              = f x0 + deriv f x0 * h + (deriv ^^ 2) f x0 * h\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * h ^ 3 / 6"
    by (simp add: eval_nat_numeral)
  have sum2_eq: "(\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
              = f x0 + deriv f x0 * (2 * h) + (deriv ^^ 2) f x0 * (2 * h)\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * (2 * h) ^ 3 / 6"
    by (simp add: eval_nat_numeral)
  have sum3_eq: "(\<Sum>m<4. ((deriv ^^ m) f x0 / fact m) * ((x0 + 3 * h) - x0)^m)
              = f x0 + deriv f x0 * (3 * h) + (deriv ^^ 2) f x0 * (3 * h)\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * (3 * h) ^ 3 / 6"
    by (simp add: eval_nat_numeral)

  have e1: "f (x0 + h) = f x0 + deriv f x0 * h + (deriv ^^ 2) f x0 * h\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * h ^ 3 / 6 + (deriv ^^ 4) f t1 * h ^ 4 / 24"
    using taylor1_eq sum1_eq by (simp add: eval_nat_numeral)
  have e2: "f (x0 + 2 * h) = f x0 + deriv f x0 * (2 * h) + (deriv ^^ 2) f x0 * (2 * h)\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * (2 * h) ^ 3 / 6 + (deriv ^^ 4) f t2 * (2 * h) ^ 4 / 24"
    using taylor2_eq sum2_eq by (simp add: eval_nat_numeral)
  have e3: "f (x0 + 3 * h) = f x0 + deriv f x0 * (3 * h) + (deriv ^^ 2) f x0 * (3 * h)\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * (3 * h) ^ 3 / 6 + (deriv ^^ 4) f t3 * (3 * h) ^ 4 / 24"
    using taylor3_eq sum3_eq by (simp add: eval_nat_numeral)

  have h4_eq: "h ^ 4 = h * h ^ 3"
    by (simp add: eval_nat_numeral)

  have combine: "f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0
      = (deriv ^^ 3) f x0 * h ^ 3
        + (81 * (deriv ^^ 4) f t3 - 48 * (deriv ^^ 4) f t2 + 3 * (deriv ^^ 4) f t1)
            * h ^ 4 / 24"
    using e1 e2 e3 by (simp add: field_simps)

  have "(f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0) / h ^ 3
      = (deriv ^^ 3) f x0
        + (81 * (deriv ^^ 4) f t3 - 48 * (deriv ^^ 4) f t2 + 3 * (deriv ^^ 4) f t1)
            * h / 24"
    unfolding combine h4_eq using h_pos
    by (simp add: add_divide_distrib field_simps)
  then show ?thesis
    using t1_bound t2_bound t3_bound by auto
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
corollary forward_diff_three_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 4 f U"
  assumes seg: "{x0..x0 + 3 * h} \<subseteq> U"
  assumes bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + 3 * h \<Longrightarrow> \<bar>(deriv ^^ 4) f t\<bar> \<le> M"
  shows "\<bar>(f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0) / h ^ 3
            - (deriv ^^ 3) f x0\<bar> \<le> (11 * M / 2) * h"
proof -
  from forward_diff_three_taylor[OF h_pos Ck seg]
  obtain t1 t2 t3 where bounds: "x0 < t1" "t1 < x0 + h" "x0 < t2" "t2 < x0 + 2 * h"
                                 "x0 < t3" "t3 < x0 + 3 * h"
    and eq: "(f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0) / h ^ 3
               - (deriv ^^ 3) f x0
             = (81 * (deriv ^^ 4) f t3 - 48 * (deriv ^^ 4) f t2 + 3 * (deriv ^^ 4) f t1)
                 * h / 24"
    by blast
  have b1: "\<bar>(deriv ^^ 4) f t1\<bar> \<le> M"
    using bound[of t1] bounds h_pos by simp
  have b2: "\<bar>(deriv ^^ 4) f t2\<bar> \<le> M"
    using bound[of t2] bounds h_pos by simp
  have b3: "\<bar>(deriv ^^ 4) f t3\<bar> \<le> M"
    using bound[of t3] bounds h_pos by simp
  have "\<bar>(f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0) / h ^ 3
            - (deriv ^^ 3) f x0\<bar>
      = \<bar>81 * (deriv ^^ 4) f t3 - 48 * (deriv ^^ 4) f t2 + 3 * (deriv ^^ 4) f t1\<bar> * h / 24"
    unfolding eq using h_pos by (simp add: abs_mult)
  also have "\<dots> \<le> (81 * \<bar>(deriv ^^ 4) f t3\<bar> + 48 * \<bar>(deriv ^^ 4) f t2\<bar>
                     + 3 * \<bar>(deriv ^^ 4) f t1\<bar>) * h / 24"
    using h_pos by (simp add: mult_right_mono)
  also have "\<dots> \<le> (81 * M + 48 * M + 3 * M) * h / 24"
    using b1 b2 b3 h_pos by (simp add: mult_left_mono mult_right_mono)
  also have "\<dots> = (11 * M / 2) * h"
    by simp
  finally show ?thesis .
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_three_uniform_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 4 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes h_pos: "0 < h"
  assumes x0_in: "x0 \<in> {a..b}" "x0 + 3 * h \<in> {a..b}"
  shows "\<bar>(f (x0 + 3 * h) - 3 * f (x0 + 2 * h) + 3 * f (x0 + h) - f x0) / h ^ 3
            - (deriv ^^ 3) f x0\<bar>
           \<le> (11 * Sup ((\<lambda>x. \<bar>(deriv ^^ 4) f x\<bar>) ` {a..b}) / 2) * h"
proof -
  have all_n: "\<forall>n<(4::nat). (deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
    using Ck unfolding C_k_on_def by simp
  have cont_on_U: "continuous_on U ((deriv ^^ 4) f)"
  proof -
    have "(3::nat) < 4" by simp
    with all_n have "continuous_on U ((deriv ^^ (Suc 3)) f)" by blast
    then show ?thesis by simp
  qed
  have cont: "continuous_on {a..b} ((deriv ^^ 4) f)"
    using cont_on_U ab_subset continuous_on_subset by blast
  have bdd: "bdd_above ((\<lambda>x. \<bar>(deriv ^^ 4) f x\<bar>) ` {a..b})"
    using a_lt_b cont continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + 3 * h \<Longrightarrow> \<bar>(deriv ^^ 4) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 4) f x\<bar>) ` {a..b})"
  proof -
    fix t assume t_bounds: "x0 \<le> t" "t \<le> x0 + 3 * h"
    have t_in_ab: "t \<in> {a..b}"
      using t_bounds x0_in by auto
    show "\<bar>(deriv ^^ 4) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 4) f x\<bar>) ` {a..b})"
      by (rule cSUP_upper[OF t_in_ab bdd])
  qed
  have seg: "{x0..x0 + 3 * h} \<subseteq> U"
    using x0_in ab_subset by auto
  show ?thesis
    by (rule forward_diff_three_error_bound[OF h_pos Ck seg bound])
qed

text \<open>
  Equation (4.4) for \<open>j=4\<close>, the last instance of the per-\<open>j\<close> Taylor-expansion recipe recorded
  here (the pattern from \<open>j=1,2,3\<close> clearly continues to scale; further \<open>j\<close> add no new proof
  technique, only more Taylor applications and larger binomial arithmetic, so this is the last
  one formalized explicitly -- see the note on the general-\<open>j\<close> combinatorial identity earlier
  in this theory for what a fully general statement would still need). Four applications of
  \<open>Taylor\<close> to order \<open>5\<close>, at \<open>h,2h,3h,4h\<close>; coefficients \<open>1,-4,6,-4,1\<close> on \<open>f,f',f'',f'''\<close> cancel
  (e.g. \<open>1-4+6-4+1=0\<close>), the \<open>f''''\<close> term survives with coefficient exactly \<open>h\<^sup>4\<close>
  (\<open>0-4+96-324+256=24=4!\<close>), and the remainder is a combination of four Lagrange points.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_four:
  "forward_diff f xs h 4 k
     = (f (xs ! (k + 4)) - 4 * f (xs ! (k + 3)) + 6 * f (xs ! (k + 2))
          - 4 * f (xs ! (k + 1)) + f (xs ! k)) / h ^ 4"
proof -
  have "(\<Sum>v\<in>{0..4::nat}. (real (4 choose v)) * (-1)^v * f (xs ! (k + 4 - v)))
      = f (xs ! (k + 4)) - 4 * f (xs ! (k + 3)) + 6 * f (xs ! (k + 2))
          - 4 * f (xs ! (k + 1)) + f (xs ! k)"
    by (simp add: sum.atLeast0_atMost_Suc eval_nat_numeral)
  then show ?thesis
    unfolding forward_diff_def by simp
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_four_taylor:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 5 f U"
  assumes seg: "{x0..x0 + 4 * h} \<subseteq> U"
  shows "\<exists>t1 t2 t3 t4. x0 < t1 \<and> t1 < x0 + h \<and> x0 < t2 \<and> t2 < x0 + 2 * h \<and>
                        x0 < t3 \<and> t3 < x0 + 3 * h \<and> x0 < t4 \<and> t4 < x0 + 4 * h \<and>
             (f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0)
                / h ^ 4 - (deriv ^^ 4) f x0
               = (1024 * (deriv ^^ 5) f t4 - 972 * (deriv ^^ 5) f t3
                    + 192 * (deriv ^^ 5) f t2 - 4 * (deriv ^^ 5) f t1) * h / 120"
proof -
  have INIT: "(5::nat) > 0" "(deriv ^^ 0) f = f"
    by simp_all
  have DERIV_hyp: "\<forall>m t. m < 5 \<and> x0 \<le> t \<and> t \<le> x0 + 4 * h
                     \<longrightarrow> DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
  proof (rule allI, rule allI, rule impI)
    fix m :: nat and t :: real
    assume "m < 5 \<and> x0 \<le> t \<and> t \<le> x0 + 4 * h"
    then show "DERIV ((deriv ^^ m) f) t :> (deriv ^^ (Suc m)) f t"
      using seg by (intro Ck_on_derivative_chain[OF Ck]) auto
  qed

  have INTERV1: "x0 \<le> x0" "x0 \<le> x0 + 4 * h" "x0 \<le> x0 + h" "x0 + h \<le> x0 + 4 * h" "x0 + h \<noteq> x0"
    using h_pos by simp_all
  have Taylor1: "\<exists>t. (if x0 + h < x0 then x0 + h < t \<and> t < x0 else x0 < t \<and> t < x0 + h) \<and>
        f (x0 + h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 5) f t / fact 5) * ((x0 + h) - x0)^5"
    by (rule Taylor[OF INIT DERIV_hyp INTERV1])
  obtain t1 where t1_bound: "x0 < t1 \<and> t1 < x0 + h"
    and taylor1_eq: "f (x0 + h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
          + ((deriv ^^ 5) f t1 / fact 5) * ((x0 + h) - x0)^5"
    using Taylor1 h_pos by auto

  have INTERV2: "x0 \<le> x0" "x0 \<le> x0 + 4 * h" "x0 \<le> x0 + 2 * h" "x0 + 2 * h \<le> x0 + 4 * h" "x0 + 2 * h \<noteq> x0"
    using h_pos by simp_all
  have Taylor2: "\<exists>t. (if x0 + 2 * h < x0 then x0 + 2 * h < t \<and> t < x0 else x0 < t \<and> t < x0 + 2 * h) \<and>
        f (x0 + 2 * h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
          + ((deriv ^^ 5) f t / fact 5) * ((x0 + 2 * h) - x0)^5"
    by (rule Taylor[OF INIT DERIV_hyp INTERV2])
  obtain t2 where t2_bound: "x0 < t2 \<and> t2 < x0 + 2 * h"
    and taylor2_eq: "f (x0 + 2 * h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
          + ((deriv ^^ 5) f t2 / fact 5) * ((x0 + 2 * h) - x0)^5"
    using Taylor2 h_pos by auto

  have INTERV3: "x0 \<le> x0" "x0 \<le> x0 + 4 * h" "x0 \<le> x0 + 3 * h" "x0 + 3 * h \<le> x0 + 4 * h" "x0 + 3 * h \<noteq> x0"
    using h_pos by simp_all
  have Taylor3: "\<exists>t. (if x0 + 3 * h < x0 then x0 + 3 * h < t \<and> t < x0 else x0 < t \<and> t < x0 + 3 * h) \<and>
        f (x0 + 3 * h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 3 * h) - x0)^m)
          + ((deriv ^^ 5) f t / fact 5) * ((x0 + 3 * h) - x0)^5"
    by (rule Taylor[OF INIT DERIV_hyp INTERV3])
  obtain t3 where t3_bound: "x0 < t3 \<and> t3 < x0 + 3 * h"
    and taylor3_eq: "f (x0 + 3 * h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 3 * h) - x0)^m)
          + ((deriv ^^ 5) f t3 / fact 5) * ((x0 + 3 * h) - x0)^5"
    using Taylor3 h_pos by auto

  have INTERV4: "x0 \<le> x0" "x0 \<le> x0 + 4 * h" "x0 \<le> x0 + 4 * h" "x0 + 4 * h \<le> x0 + 4 * h" "x0 + 4 * h \<noteq> x0"
    using h_pos by simp_all
  have Taylor4: "\<exists>t. (if x0 + 4 * h < x0 then x0 + 4 * h < t \<and> t < x0 else x0 < t \<and> t < x0 + 4 * h) \<and>
        f (x0 + 4 * h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 4 * h) - x0)^m)
          + ((deriv ^^ 5) f t / fact 5) * ((x0 + 4 * h) - x0)^5"
    by (rule Taylor[OF INIT DERIV_hyp INTERV4])
  obtain t4 where t4_bound: "x0 < t4 \<and> t4 < x0 + 4 * h"
    and taylor4_eq: "f (x0 + 4 * h) =
        (\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 4 * h) - x0)^m)
          + ((deriv ^^ 5) f t4 / fact 5) * ((x0 + 4 * h) - x0)^5"
    using Taylor4 h_pos by auto

  have sum1_eq: "(\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + h) - x0)^m)
              = f x0 + deriv f x0 * h + (deriv ^^ 2) f x0 * h\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * h ^ 3 / 6 + (deriv ^^ 4) f x0 * h ^ 4 / 24"
    by (simp add: eval_nat_numeral)
  have sum2_eq: "(\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 2 * h) - x0)^m)
              = f x0 + deriv f x0 * (2 * h) + (deriv ^^ 2) f x0 * (2 * h)\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * (2 * h) ^ 3 / 6 + (deriv ^^ 4) f x0 * (2 * h) ^ 4 / 24"
    by (simp add: eval_nat_numeral)
  have sum3_eq: "(\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 3 * h) - x0)^m)
              = f x0 + deriv f x0 * (3 * h) + (deriv ^^ 2) f x0 * (3 * h)\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * (3 * h) ^ 3 / 6 + (deriv ^^ 4) f x0 * (3 * h) ^ 4 / 24"
    by (simp add: eval_nat_numeral)
  have sum4_eq: "(\<Sum>m<5. ((deriv ^^ m) f x0 / fact m) * ((x0 + 4 * h) - x0)^m)
              = f x0 + deriv f x0 * (4 * h) + (deriv ^^ 2) f x0 * (4 * h)\<^sup>2 / 2
                     + (deriv ^^ 3) f x0 * (4 * h) ^ 3 / 6 + (deriv ^^ 4) f x0 * (4 * h) ^ 4 / 24"
    by (simp add: eval_nat_numeral)

  have e1: "f (x0 + h) = f x0 + deriv f x0 * h + (deriv ^^ 2) f x0 * h\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * h ^ 3 / 6 + (deriv ^^ 4) f x0 * h ^ 4 / 24
                        + (deriv ^^ 5) f t1 * h ^ 5 / 120"
    using taylor1_eq sum1_eq by (simp add: eval_nat_numeral)
  have e2: "f (x0 + 2 * h) = f x0 + deriv f x0 * (2 * h) + (deriv ^^ 2) f x0 * (2 * h)\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * (2 * h) ^ 3 / 6 + (deriv ^^ 4) f x0 * (2 * h) ^ 4 / 24
                        + (deriv ^^ 5) f t2 * (2 * h) ^ 5 / 120"
    using taylor2_eq sum2_eq by (simp add: eval_nat_numeral)
  have e3: "f (x0 + 3 * h) = f x0 + deriv f x0 * (3 * h) + (deriv ^^ 2) f x0 * (3 * h)\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * (3 * h) ^ 3 / 6 + (deriv ^^ 4) f x0 * (3 * h) ^ 4 / 24
                        + (deriv ^^ 5) f t3 * (3 * h) ^ 5 / 120"
    using taylor3_eq sum3_eq by (simp add: eval_nat_numeral)
  have e4: "f (x0 + 4 * h) = f x0 + deriv f x0 * (4 * h) + (deriv ^^ 2) f x0 * (4 * h)\<^sup>2 / 2
                        + (deriv ^^ 3) f x0 * (4 * h) ^ 3 / 6 + (deriv ^^ 4) f x0 * (4 * h) ^ 4 / 24
                        + (deriv ^^ 5) f t4 * (4 * h) ^ 5 / 120"
    using taylor4_eq sum4_eq by (simp add: eval_nat_numeral)

  have h5_eq: "h ^ 5 = h * h ^ 4"
    by (simp add: eval_nat_numeral)

  have combine: "f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0
      = (deriv ^^ 4) f x0 * h ^ 4
        + (1024 * (deriv ^^ 5) f t4 - 972 * (deriv ^^ 5) f t3
             + 192 * (deriv ^^ 5) f t2 - 4 * (deriv ^^ 5) f t1) * h ^ 5 / 120"
    unfolding e1 e2 e3 e4 by (simp add: eval_nat_numeral field_simps)

  have "(f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0) / h ^ 4
      = (deriv ^^ 4) f x0
        + (1024 * (deriv ^^ 5) f t4 - 972 * (deriv ^^ 5) f t3
             + 192 * (deriv ^^ 5) f t2 - 4 * (deriv ^^ 5) f t1) * h / 120"
    unfolding combine h5_eq using h_pos
    by (simp add: add_divide_distrib field_simps)
  then show ?thesis
    using t1_bound t2_bound t3_bound t4_bound by auto
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
corollary forward_diff_four_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck: "C_k_on 5 f U"
  assumes seg: "{x0..x0 + 4 * h} \<subseteq> U"
  assumes bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + 4 * h \<Longrightarrow> \<bar>(deriv ^^ 5) f t\<bar> \<le> M"
  shows "\<bar>(f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0) / h ^ 4
            - (deriv ^^ 4) f x0\<bar> \<le> (274 * M / 15) * h"
proof -
  from forward_diff_four_taylor[OF h_pos Ck seg]
  obtain t1 t2 t3 t4 where bounds: "x0 < t1" "t1 < x0 + h" "x0 < t2" "t2 < x0 + 2 * h"
                                    "x0 < t3" "t3 < x0 + 3 * h" "x0 < t4" "t4 < x0 + 4 * h"
    and eq: "(f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0) / h ^ 4
               - (deriv ^^ 4) f x0
             = (1024 * (deriv ^^ 5) f t4 - 972 * (deriv ^^ 5) f t3
                  + 192 * (deriv ^^ 5) f t2 - 4 * (deriv ^^ 5) f t1) * h / 120"
    by blast
  have b1: "\<bar>(deriv ^^ 5) f t1\<bar> \<le> M"
    using bound[of t1] bounds h_pos by simp
  have b2: "\<bar>(deriv ^^ 5) f t2\<bar> \<le> M"
    using bound[of t2] bounds h_pos by simp
  have b3: "\<bar>(deriv ^^ 5) f t3\<bar> \<le> M"
    using bound[of t3] bounds h_pos by simp
  have b4: "\<bar>(deriv ^^ 5) f t4\<bar> \<le> M"
    using bound[of t4] bounds h_pos by simp
  have "\<bar>(f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0) / h ^ 4
            - (deriv ^^ 4) f x0\<bar>
      = \<bar>1024 * (deriv ^^ 5) f t4 - 972 * (deriv ^^ 5) f t3
           + 192 * (deriv ^^ 5) f t2 - 4 * (deriv ^^ 5) f t1\<bar> * h / 120"
    unfolding eq using h_pos by (simp add: abs_mult)
  also have "\<dots> \<le> (1024 * \<bar>(deriv ^^ 5) f t4\<bar> + 972 * \<bar>(deriv ^^ 5) f t3\<bar>
                     + 192 * \<bar>(deriv ^^ 5) f t2\<bar> + 4 * \<bar>(deriv ^^ 5) f t1\<bar>) * h / 120"
    using h_pos by (simp add: mult_right_mono)
  also have "\<dots> \<le> (1024 * M + 972 * M + 192 * M + 4 * M) * h / 120"
    using b1 b2 b3 b4 h_pos by (simp add: mult_left_mono mult_right_mono)
  also have "\<dots> = (274 * M / 15) * h"
    by simp
  finally show ?thesis .
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_four_uniform_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 5 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes h_pos: "0 < h"
  assumes x0_in: "x0 \<in> {a..b}" "x0 + 4 * h \<in> {a..b}"
  shows "\<bar>(f (x0 + 4 * h) - 4 * f (x0 + 3 * h) + 6 * f (x0 + 2 * h) - 4 * f (x0 + h) + f x0) / h ^ 4
            - (deriv ^^ 4) f x0\<bar>
           \<le> (274 * Sup ((\<lambda>x. \<bar>(deriv ^^ 5) f x\<bar>) ` {a..b}) / 15) * h"
proof -
  have all_n: "\<forall>n<(5::nat). (deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ (Suc n)) f)"
    using Ck unfolding C_k_on_def by simp
  have cont_on_U: "continuous_on U ((deriv ^^ 5) f)"
  proof -
    have "(4::nat) < 5" by simp
    with all_n have "continuous_on U ((deriv ^^ (Suc 4)) f)" by blast
    then show ?thesis by simp
  qed
  have cont: "continuous_on {a..b} ((deriv ^^ 5) f)"
    using cont_on_U ab_subset continuous_on_subset by blast
  have bdd: "bdd_above ((\<lambda>x. \<bar>(deriv ^^ 5) f x\<bar>) ` {a..b})"
    using a_lt_b cont continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have bound: "\<And>t. x0 \<le> t \<Longrightarrow> t \<le> x0 + 4 * h \<Longrightarrow> \<bar>(deriv ^^ 5) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 5) f x\<bar>) ` {a..b})"
  proof -
    fix t assume t_bounds: "x0 \<le> t" "t \<le> x0 + 4 * h"
    have t_in_ab: "t \<in> {a..b}"
      using t_bounds x0_in by auto
    show "\<bar>(deriv ^^ 5) f t\<bar> \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 5) f x\<bar>) ` {a..b})"
      by (rule cSUP_upper[OF t_in_ab bdd])
  qed
  have seg: "{x0..x0 + 4 * h} \<subseteq> U"
    using x0_in ab_subset by auto
  show ?thesis
    by (rule forward_diff_four_error_bound[OF h_pos Ck seg bound])
qed

text \<open>
  The network \<open>G_N\<^sup>j f\<close> of (4.3): structurally identical to \<open>G_Nf\<close> from (2.2) (theory
  Universal\_Approximation\_1d) and built with the very same \<open>\<sigma>\<close>, except that its
  coefficients are differences of \<open>\<Delta>\<^sup>j f\<close>-values, rather than of \<open>f\<close>-values themselves.
  As in \<open>Universal_Approximation_1d.thy\<close>, \<open>xs\<close> is indexed with an
  offset of one from the paper's own \<open>x\<^sub>-\<^sub>1,x\<^sub>0,\<dots>,x\<^sub>N\<close>: \<open>xs!0 = x\<^sub>-\<^sub>1\<close> and \<open>xs!(k+1) = x\<^sub>k\<close>, so
  a paper index \<open>k\<close> becomes \<open>k+1\<close> here, and \<open>\<Delta>\<^sup>j\<^sub>k f\<close> becomes \<open>forward_diff f xs h j (k+1)\<close>.
\<close>
(* Equation (4.3): derivative-approximation network. *)
definition Gj_network :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Gj_network \<sigma> f xs h N j w x =
     (\<Sum>k\<in>{1..N-j}. (forward_diff f xs h j (k + 1) - forward_diff f xs h j k) * \<sigma> (w * (x - xs ! (k + 1))))
     + forward_diff f xs h j 1 * \<sigma> (w * (x - xs ! 0))"

text \<open>
  \<open>G_N\<^sup>j f\<close> is continuous whenever \<open>\<sigma>\<close> is, exactly as \<open>G_Nf\<close> is in
  \<open>Lp_Approximation.thy\<close>'s \<open>G_Nf_continuous\<close> -- both are finite sums of scalar multiples of
  \<open>\<sigma>\<close> composed with an affine map of \<open>x\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma Gj_network_continuous:
  assumes cont_sigma: "continuous_on UNIV \<sigma>"
  shows "continuous_on S (Gj_network \<sigma> f xs h N j w)"
  unfolding Gj_network_def
  by (intro continuous_intros continuous_on_compose2[OF cont_sigma]
            continuous_on_subset[OF continuous_on_id, of S UNIV]) auto

text \<open>
  Theorem 4.1's argument approximates \<open>f'\<close> by comparing \<open>G_N\<^sup>1 f\<close> to the network
  \<open>sigmoidal_approximation_theorem\<close> already builds out of the \<open>true\<close> values of \<open>f'\<close> at the
  partition nodes: the two networks have exactly the same shape, and differ only in that
  \<open>G_N\<^sup>1 f\<close>'s coefficients use \<open>\<Delta>\<^sup>1_k f\<close> (a finite difference of \<open>f\<close>) where the other uses
  \<open>f'(x_k)\<close> directly. The bridge is that \<open>\<Delta>\<^sup>1_k f\<close> approximates \<open>f'(x_k)\<close> to order \<open>h\<close>
  (\<open>forward_diff_one_uniform_error_bound\<close>) at \<open>every\<close> node \<open>x_k\<close> of the partition, not
  just at one point -- exactly what is needed to bound the coefficient-by-coefficient error
  that accumulates into \<open>G_N\<^sup>1 f - G_N\<^sup>1(f')\<close>. We record this node-by-node fact here, before
  assembling Theorem 4.1 itself in a later theory. \<open>a\<close>, \<open>b\<close>, \<open>N\<close>, \<open>h\<close>, \<open>xs\<close> are all taken as
  explicit parameters with explicit hypotheses (matching \<open>Partition_Facts.thy\<close>), not via a
  \<open>locale\<close>.
\<close>

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_one_node_error:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes m_range: "m \<in> {1..N}"
  shows "\<bar>forward_diff f xs h 1 m - deriv f (xs ! m)\<bar>
       \<le> (Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) / 2) * h"
proof -
  have h_pos': "h > 0"
    by (rule h_pos[OF a_lt_b N_pos h_def])
  have x0_in: "xs ! m \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] m_range by auto
  have m1_range: "m + 1 \<in> {1..N+1}"
    using m_range by auto
  have step: "xs ! (m + 1) - xs ! m = h"
    using difference_of_adj_terms[OF h_def xs_def, of "m + 1"] m1_range by auto
  have x0h_eq: "xs ! m + h = xs ! (m + 1)"
    using step by simp
  have x0h_in: "xs ! m + h \<in> {a..b}"
    unfolding x0h_eq using els_in_ab[OF a_lt_b N_pos h_def xs_def] m1_range by auto
  have fd_eq: "forward_diff f xs h 1 m = (f (xs ! m + h) - f (xs ! m)) / h"
    unfolding x0h_eq using forward_diff_one by simp
  show ?thesis
    unfolding fd_eq
    by (rule forward_diff_one_uniform_error_bound[OF a_lt_b Ck ab_subset h_pos' x0_in x0h_in])
qed

text \<open>
  The coefficient-error bound Theorem 4.1's proof actually needs: at any \<open>interior\<close> pair of
  adjacent nodes, the difference of two consecutive \<open>\<Delta>\<^sup>1 f\<close>-values (a \<open>G_N\<^sup>1 f\<close> coefficient)
  differs from the difference of the corresponding \<open>f'\<close>-values (the analogous
  \<open>sigmoidal_approximation_theorem\<close> coefficient, for the function \<open>f'\<close>) by at most \<open>C\<^sub>1 h\<close> --
  twice the single-node bound above, one factor of \<open>h\<close> from each node, via the triangle
  inequality.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_one_coefficient_error:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes k_range: "k \<in> {1..N-1}"
  shows "\<bar>(forward_diff f xs h 1 (k + 1) - forward_diff f xs h 1 k)
        - (deriv f (xs ! (k + 1)) - deriv f (xs ! k))\<bar>
       \<le> Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) * h"
proof -
  have k_in: "k \<in> {1..N}" and k1_in: "k + 1 \<in> {1..N}"
    using k_range N_pos by auto
  have e1: "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>
       \<le> (Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) / 2) * h"
    by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_in])
  have e2: "\<bar>forward_diff f xs h 1 (k + 1) - deriv f (xs ! (k + 1))\<bar>
       \<le> (Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) / 2) * h"
    by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k1_in])
  have rearrange: "(forward_diff f xs h 1 (k + 1) - forward_diff f xs h 1 k)
        - (deriv f (xs ! (k + 1)) - deriv f (xs ! k))
      = (forward_diff f xs h 1 (k + 1) - deriv f (xs ! (k + 1)))
        - (forward_diff f xs h 1 k - deriv f (xs ! k))"
    by simp
  show ?thesis
    unfolding rearrange using e1 e2 by linarith
qed

text \<open>
  Theorem 4.1's proof, when written to reuse Theorem 2.1's own \<open>I_1\<close> argument (see the
  discussion recorded alongside this development), needs one further fact about \<open>\<Delta>\<^sup>1 f\<close> that
  \<open>forward_diff_one_coefficient_error\<close> alone does not give: Theorem 2.1's \<open>I_1\<close> bound relies on
  \<open>f\<close>'s own \<open>uniform\<close> continuity to keep \<open>\<Sum>\<^sub>k |f(x_k)-f(x_{k-1})|\<close>-type sums under control
  \<^emph>\<open>independently of\<close> \<open>N\<close> (every pair of nodes closer than \<open>\<delta>\<close> apart has \<open>f\<close>-values closer than
  \<open>\<eta>\<close> apart, for a \<open>\<delta>\<close> depending only on \<open>\<eta>\<close>, not on which pair of nodes). Reusing that argument
  for \<open>G_N\<^sup>1 f\<close>'s own coefficients \<open>\<Delta>\<^sup>1_k f\<close> in place of \<open>f(x_k)\<close> needs the analogous fact for
  \<open>\<Delta>\<^sup>1 f\<close>: any \<^emph>\<open>two\<close> nodes \<open>x_j\<close>, \<open>x_k\<close> (not just adjacent ones, unlike
  \<open>forward_diff_one_coefficient_error\<close>) have \<open>\<Delta>\<^sup>1 f\<close>-values within \<open>|f'(x_j)-f'(x_k)| + C_1 h\<close> of
  each other -- so once \<open>x_j\<close>, \<open>x_k\<close> are within \<open>\<delta>\<close> of each other, \<open>f'\<close>'s own uniform continuity
  (which holds here since \<open>C_k_on 2 f U\<close> already bundles continuity of \<open>deriv f\<close>) makes
  the first term small, and choosing \<open>N\<close> large enough (so \<open>h\<close> is small) makes the second term
  small, matching \<open>\<Delta>\<^sup>1 f\<close> to the same \<open>\<delta>\<close>/\<open>\<eta>\<close> pattern Theorem 2.1's proof uses for \<open>f\<close> itself.
  This is the two-node generalization of \<open>forward_diff_one_node_error\<close>, proved the same way
  (two applications of \<open>forward_diff_one_uniform_error_bound\<close> and the triangle inequality).
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_one_two_node_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes j_range: "j \<in> {1..N}" and k_range: "k \<in> {1..N}"
  shows "\<bar>forward_diff f xs h 1 j - forward_diff f xs h 1 k\<bar>
       \<le> \<bar>deriv f (xs ! j) - deriv f (xs ! k)\<bar>
           + Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) * h"
proof -
  have ej: "\<bar>forward_diff f xs h 1 j - deriv f (xs ! j)\<bar>
       \<le> (Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) / 2) * h"
    by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset j_range])
  have ek: "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>
       \<le> (Sup ((\<lambda>x. \<bar>(deriv ^^ 2) f x\<bar>) ` {a..b}) / 2) * h"
    by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_range])
  have rearrange: "forward_diff f xs h 1 j - forward_diff f xs h 1 k
      = (deriv f (xs ! j) - deriv f (xs ! k))
        + ((forward_diff f xs h 1 j - deriv f (xs ! j))
           - (forward_diff f xs h 1 k - deriv f (xs ! k)))"
    by simp
  show ?thesis
    unfolding rearrange using ej ek by linarith
qed

text \<open>
  The same two bridge facts one order up, for \<open>j=2\<close>: needed for the \<open>j=2\<close> analogue of
  Theorem 4.1 (approximating \<open>f''\<close>), by the identical argument with
  \<open>forward_diff_two_uniform_error_bound\<close> in place of \<open>forward_diff_one_uniform_error_bound\<close>.
\<close>
(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_two_node_error:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 3 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes m_range: "m \<in> {1..N-1}"
  shows "\<bar>forward_diff f xs h 2 m - (deriv ^^ 2) f (xs ! m)\<bar>
       \<le> (5 * Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b}) / 3) * h"
proof -
  have h_pos': "h > 0"
    by (rule h_pos[OF a_lt_b N_pos h_def])
  have x0_in: "xs ! m \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] m_range by auto
  have m1_range: "m + 1 \<in> {1..N+1}" and m2_range: "m + 2 \<in> {1..N+1}"
    using m_range by auto
  have step1: "xs ! (m + 1) - xs ! m = h"
    using difference_of_adj_terms[OF h_def xs_def, of "m + 1"] m1_range by auto
  have step2: "xs ! (m + 2) - xs ! (m + 1) = h"
    using difference_of_adj_terms[OF h_def xs_def, of "m + 2"] m2_range by auto
  have m1_eq: "xs ! (m + 1) = xs ! m + h"
    using step1 by simp
  have x0_2h_eq: "xs ! m + 2 * h = xs ! (m + 2)"
    using step1 step2 by simp
  have x0_2h_in: "xs ! m + 2 * h \<in> {a..b}"
    unfolding x0_2h_eq using els_in_ab[OF a_lt_b N_pos h_def xs_def] m2_range by auto
  have fd_eq: "forward_diff f xs h 2 m = (f (xs ! m + 2 * h) - 2 * f (xs ! m + h) + f (xs ! m)) / h\<^sup>2"
    unfolding forward_diff_two[of f xs h m] x0_2h_eq[symmetric] m1_eq[symmetric] ..
  show ?thesis
    unfolding fd_eq
    by (rule forward_diff_two_uniform_error_bound[OF a_lt_b Ck ab_subset h_pos' x0_in x0_2h_in])
qed

(* Auxiliary for Theorem 4.1 and estimate (4.4); not separately numbered. *)
lemma forward_diff_two_coefficient_error:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 3 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes k_range: "k \<in> {1..N-2}"
  shows "\<bar>(forward_diff f xs h 2 (k + 1) - forward_diff f xs h 2 k)
        - ((deriv ^^ 2) f (xs ! (k + 1)) - (deriv ^^ 2) f (xs ! k))\<bar>
       \<le> 10 * Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b}) / 3 * h"
proof -
  have k_in: "k \<in> {1..N-1}" and k1_in: "k + 1 \<in> {1..N-1}"
    using k_range N_pos by auto
  have e1: "\<bar>forward_diff f xs h 2 k - (deriv ^^ 2) f (xs ! k)\<bar>
       \<le> (5 * Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b}) / 3) * h"
    by (rule forward_diff_two_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_in])
  have e2: "\<bar>forward_diff f xs h 2 (k + 1) - (deriv ^^ 2) f (xs ! (k + 1))\<bar>
       \<le> (5 * Sup ((\<lambda>x. \<bar>(deriv ^^ 3) f x\<bar>) ` {a..b}) / 3) * h"
    by (rule forward_diff_two_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k1_in])
  have rearrange: "(forward_diff f xs h 2 (k + 1) - forward_diff f xs h 2 k)
        - ((deriv ^^ 2) f (xs ! (k + 1)) - (deriv ^^ 2) f (xs ! k))
      = (forward_diff f xs h 2 (k + 1) - (deriv ^^ 2) f (xs ! (k + 1)))
        - (forward_diff f xs h 2 k - (deriv ^^ 2) f (xs ! k))"
    by simp
  show ?thesis
    unfolding rearrange using e1 e2 by linarith
qed

end
