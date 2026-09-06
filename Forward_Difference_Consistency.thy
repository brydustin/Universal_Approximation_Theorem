section \<open>Consistency of the forward difference operator: equation (4.4) for general \<open>j\<close>\<close>

theory Forward_Difference_Consistency
  imports Derivative_Approximation
begin

text \<open>
  Equation (4.4) of Costarelli and Spigler~\cite{CostarelliSpigler} (p.178) asserts that the
  forward difference \<open>\<Delta>\<^sup>j\<^sub>k f\<close> of (4.2) approximates \<open>f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k)\<close> to first order in the mesh width:
  there is a constant \<open>Ctilde\<^sub>j>0\<close>, depending only on \<open>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<close>, with
  \<open>\<bar>\<Delta>\<^sup>j\<^sub>k f - f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k)\<bar> \<le> Ctilde\<^sub>j h\<close> for every \<open>k=0,\<dots>,N-j\<close>.  The paper introduces this with the words
  ``it is well known that'', and gives no proof; it is nevertheless the load-bearing estimate for
  both Theorem 4.1 and Theorem 4.2, so it has to be supplied here.

  \<^file>\<open>Derivative_Approximation.thy\<close> already has the cases \<open>j=1,2,3,4\<close>
  (\<open>forward_diff_one_error_bound\<close> and friends), each obtained from its own hand-rolled Taylor
  expansion, with constants \<open>M/2\<close>, \<open>5M/3\<close>, \<open>11M/2\<close>, \<open>274M/15\<close>.  That route does not scale.  Here
  we prove the general-\<open>j\<close> statement once, by a route that needs only the mean value theorem:

  \<^item> \<open>\<Delta>\<^sup>j\<^sub>k f\<close> is the \<open>j\<close>-fold iterate of the one-step difference quotient
    \<open>D\<^sub>h g x = (g(x+h)-g(x))/h\<close> (\<open>Dh\<close> below), by a Pascal-rule induction;
  \<^item> \<open>D\<^sub>h\<close> commutes with \<^const>\<open>deriv\<close>;
  \<^item> \<open>D\<^sub>h g x = g'(\<eta>)\<close> for some \<open>\<eta>\<in>(x,x+h)\<close>, by the mean value theorem;
  \<^item> whence, by induction on \<open>j\<close>, \<open>\<bar>(D\<^sub>h\<^sup>j f)(x) - f\<^sup>(\<^sup>j\<^sup>)(x)\<bar> \<le> j\<sqdot>M\<sqdot>h\<close> whenever \<open>M\<close> bounds \<open>\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar>\<close>,
    giving the paper's \<open>Ctilde\<^sub>j = j\<sqdot>\<parallel>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<parallel>\<^sub>\<infinity>\<close>.
\<close>

subsection \<open>The one-step difference quotient\<close>

text \<open>
  \<open>D\<^sub>h\<close> earns a definition (rather than being inlined) because the induction below has to apply
  its own induction hypothesis to the \<^emph>\<open>function\<close> \<open>D\<^sub>h f\<close>, which \<^const>\<open>forward_diff\<close> -- tied as it
  is to a partition list -- cannot express.
\<close>
definition Dh :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "Dh h g x = (g (x + h) - g x) / h"

subsection \<open>The Pascal step\<close>

text \<open>
  The pure binomial identity behind (4.2)'s recurrence, isolated from all analysis: summing
  \<open>P\<close> against row \<open>j\<close> of Pascal's triangle, once in place and once shifted by one, gives row
  \<open>j+1\<close>.  Stated for an arbitrary real-valued \<open>P\<close> so that the analytic content can be substituted
  in afterwards.
\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma binom_pascal_sum:
  fixes P :: "nat \<Rightarrow> real" and j :: nat
  shows "(\<Sum>v\<in>{0..j}. real (j choose v) * P v) + (\<Sum>v\<in>{0..j}. real (j choose v) * P (Suc v))
           = (\<Sum>v\<in>{0..Suc j}. real (Suc j choose v) * P v)"
proof -
  text \<open>The shifted row-\<open>j\<close> sum, re-expressed on \<open>{0..j}\<close>: the top term drops because
    \<open>j choose (j+1) = 0\<close>.\<close>
  have key: "(\<Sum>u\<in>{0..j}. real (j choose Suc u) * P (Suc u))
               = (\<Sum>v\<in>{0..j}. real (j choose v) * P v) - P 0"
  proof -
    text \<open>\<open>subst\<close>, not \<open>simp add:\<close>: both split rules apply here and plain \<open>simp\<close> picks the
      top split, leaving the bottom one unused.\<close>
    have top_zero: "real (j choose Suc j) * P (Suc j) = 0"
      by simp
    have split_bot: "(\<Sum>v\<in>{0..Suc j}. real (j choose v) * P v)
                       = real (j choose 0) * P 0
                         + (\<Sum>u\<in>{0..j}. real (j choose Suc u) * P (Suc u))"
      by (subst sum.atLeast0_atMost_Suc_shift) (simp add: o_def)
    have split_top: "(\<Sum>v\<in>{0..Suc j}. real (j choose v) * P v)
                       = (\<Sum>v\<in>{0..j}. real (j choose v) * P v)"
      by (subst sum.atLeast0_atMost_Suc) (simp add: top_zero)
    from split_bot split_top show ?thesis by simp
  qed
  have "(\<Sum>v\<in>{0..Suc j}. real (Suc j choose v) * P v)
          = real (Suc j choose 0) * P 0
            + (\<Sum>u\<in>{0..j}. real (Suc j choose Suc u) * P (Suc u))"
    by (subst sum.atLeast0_atMost_Suc_shift) (simp add: o_def)
  also have "\<dots> = P 0
                  + (\<Sum>u\<in>{0..j}. (real (j choose u) + real (j choose Suc u)) * P (Suc u))"
    by simp
  also have "\<dots> = P 0 + ((\<Sum>u\<in>{0..j}. real (j choose u) * P (Suc u))
                          + (\<Sum>u\<in>{0..j}. real (j choose Suc u) * P (Suc u)))"
    by (simp add: distrib_right sum.distrib)
  also have "\<dots> = P 0 + ((\<Sum>u\<in>{0..j}. real (j choose u) * P (Suc u))
                          + ((\<Sum>v\<in>{0..j}. real (j choose v) * P v) - P 0))"
    using key by simp
  also have "\<dots> = (\<Sum>v\<in>{0..j}. real (j choose v) * P v)
                    + (\<Sum>v\<in>{0..j}. real (j choose v) * P (Suc v))"
    by simp
  finally show ?thesis by (rule sym)
qed

subsection \<open>The forward difference is an iterated difference quotient\<close>

text \<open>
  The bridge between (4.2)'s binomial sum and the iterate of \<^const>\<open>Dh\<close>.  Stated with an explicit
  \<open>\<forall>x\<close> rather than relying on \<open>induction j arbitrary: x\<close>, which in this project has been observed
  to desynchronise the generalised variable from the goal text.
\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Dh_iterate_sum:
  fixes h :: real and g :: "real \<Rightarrow> real" and j :: nat
  assumes h_pos: "0 < h"
  shows "\<forall>x. (Dh h ^^ j) g x
               = (1 / h ^ j)
                 * (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v * g (x + (real j - real v) * h))"
proof (induction j)
  case 0
  show ?case by simp
next
  case (Suc j)
  show ?case
  proof (rule allI)
    fix x :: real
    define P where "P = (\<lambda>v::nat. (- 1) ^ v * g (x + (real (Suc j) - real v) * h))"
    have h_nz: "h \<noteq> 0" using h_pos by simp

    have decomp: "(Dh h ^^ Suc j) g x = ((Dh h ^^ j) g (x + h) - (Dh h ^^ j) g x) / h"
      by (simp add: Dh_def)

    have upper: "(Dh h ^^ j) g (x + h)
                   = (1 / h ^ j) * (\<Sum>v\<in>{0..j}. real (j choose v) * P v)"
    proof -
      have ih: "(Dh h ^^ j) g (x + h)
                  = (1 / h ^ j)
                    * (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v
                                     * g (x + h + (real j - real v) * h))"
        using Suc.IH by blast
      have "(\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v * g (x + h + (real j - real v) * h))
              = (\<Sum>v\<in>{0..j}. real (j choose v) * P v)"
        by (rule sum.cong[OF refl]) (simp add: P_def algebra_simps)
      with ih show ?thesis by simp
    qed

    have lower: "(Dh h ^^ j) g x
                   = - ((1 / h ^ j) * (\<Sum>v\<in>{0..j}. real (j choose v) * P (Suc v)))"
    proof -
      have ih: "(Dh h ^^ j) g x
                  = (1 / h ^ j)
                    * (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v
                                     * g (x + (real j - real v) * h))"
        using Suc.IH by blast
      have "(\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v * g (x + (real j - real v) * h))
              = (\<Sum>v\<in>{0..j}. - (real (j choose v) * P (Suc v)))"
        by (rule sum.cong[OF refl]) (simp add: P_def algebra_simps)
      also have "\<dots> = - (\<Sum>v\<in>{0..j}. real (j choose v) * P (Suc v))"
        by (simp add: sum_negf)
      finally show ?thesis using ih by simp
    qed

    have "(Dh h ^^ Suc j) g x
            = ((1 / h ^ j) * ((\<Sum>v\<in>{0..j}. real (j choose v) * P v)
                              + (\<Sum>v\<in>{0..j}. real (j choose v) * P (Suc v)))) / h"
      unfolding decomp upper lower by (simp add: algebra_simps)
    also have "\<dots> = (1 / h ^ Suc j) * (\<Sum>v\<in>{0..Suc j}. real (Suc j choose v) * P v)"
      using binom_pascal_sum[of j P] h_nz by (simp add: field_simps)
    finally show "(Dh h ^^ Suc j) g x
                    = (1 / h ^ Suc j)
                      * (\<Sum>v\<in>{0..Suc j}. real (Suc j choose v) * (- 1) ^ v
                                           * g (x + (real (Suc j) - real v) * h))"
      by (simp add: P_def mult.assoc)
  qed
qed

subsection \<open>\<open>D\<^sub>h\<close> commutes with differentiation\<close>

text \<open>
  \<open>D\<^sub>h g\<close> is differentiable exactly where \<open>g\<close> is differentiable at both \<open>t\<close> and \<open>t+h\<close>, so the
  natural domain for \<open>D\<^sub>h g\<close> is not \<open>U\<close> but the \<^emph>\<open>shifted intersection\<close> \<open>U \<inter> (U-h)\<close>, which is again
  open.  Only one \<open>D\<^sub>h\<close> is ever applied below, so this shrinking happens once and does not
  compound with the order of differentiation.
\<close>
definition Ush :: "real \<Rightarrow> real set \<Rightarrow> real set" where
  "Ush h U = U \<inter> {t. t + h \<in> U}"

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Ush_subset: "Ush h U \<subseteq> U"
  unfolding Ush_def by blast

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Ush_mem: "t \<in> Ush h U \<Longrightarrow> t \<in> U"
  unfolding Ush_def by blast

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Ush_shift: "t \<in> Ush h U \<Longrightarrow> t + h \<in> U"
  unfolding Ush_def by blast

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Ush_open:
  assumes U_open: "open U"
  shows "open (Ush h U)"
proof -
  have "{t. t + h \<in> U} = (\<lambda>x. x - h) ` U"
    by force
  then have "open {t. t + h \<in> U}"
    using U_open open_translation_subtract by metis
  then show ?thesis
    unfolding Ush_def using U_open by blast
qed

text \<open>The one-step commutation, in derivative form: \<open>(D\<^sub>h g)' = D\<^sub>h (g')\<close>.\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Dh_has_derivative:
  fixes g g' :: "real \<Rightarrow> real" and h t :: real
  assumes h_nz: "h \<noteq> 0"
  assumes dt:  "(g has_real_derivative g' t) (at t)"
  assumes dth: "(g has_real_derivative g' (t + h)) (at (t + h))"
  shows "(Dh h g has_real_derivative Dh h g' t) (at t)"
proof -
  have shift: "((\<lambda>s. g (s + h)) has_real_derivative g' (t + h)) (at t)"
    using dth by (simp add: DERIV_shift)
  have diff: "((\<lambda>s. g (s + h) - g s) has_real_derivative (g' (t + h) - g' t)) (at t)"
    using shift dt by (rule DERIV_diff)
  have quot: "((\<lambda>s. (g (s + h) - g s) / h) has_real_derivative ((g' (t + h) - g' t) / h)) (at t)"
    using diff by (rule DERIV_cdivide)
  have fun_eq: "Dh h g = (\<lambda>s. (g (s + h) - g s) / h)"
    by (rule ext) (simp add: Dh_def)
  from quot show ?thesis
    unfolding fun_eq Dh_def by simp
qed

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma deriv_Dh:
  fixes g :: "real \<Rightarrow> real" and h t :: real
  assumes h_nz: "h \<noteq> 0"
  assumes dt:  "(g has_real_derivative deriv g t) (at t)"
  assumes dth: "(g has_real_derivative deriv g (t + h)) (at (t + h))"
  shows "deriv (Dh h g) t = Dh h (deriv g) t"
  by (rule DERIV_imp_deriv[OF Dh_has_derivative[OF h_nz dt dth]])

text \<open>
  The iterated form.  The induction step rewrites \<open>deriv\<close> along the induction hypothesis using
  \<open>deriv_cong_ev\<close>, which is legitimate precisely because \<^const>\<open>Ush\<close> is open: two functions
  agreeing on an open neighbourhood of \<open>t\<close> have the same derivative at \<open>t\<close>.

  The regularity hypothesis is the unpacked derivative chain rather than \<^const>\<open>C_k_on\<close>, because
  that form is \<^emph>\<open>self-propagating\<close>: the chain for \<open>D\<^sub>h f\<close> on \<^const>\<open>Ush\<close> follows from the chain
  for \<open>f\<close> on \<open>U\<close> (see \<open>Dh_iterate_error_all\<close> below), whereas re-establishing \<^const>\<open>C_k_on\<close> for
  \<open>D\<^sub>h f\<close> would additionally require transporting every continuity obligation, none of which the
  argument ever uses.  \<^const>\<open>C_k_on\<close> users reach this via \<open>Ck_on_derivative_chain\<close>.
\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma higher_deriv_Dh:
  fixes g :: "real \<Rightarrow> real" and h :: real and k m :: nat
  assumes h_nz: "h \<noteq> 0"
  assumes U_open: "open U"
  assumes chain: "\<And>i t. i < k \<Longrightarrow> t \<in> U
                    \<Longrightarrow> ((deriv ^^ i) g has_real_derivative (deriv ^^ Suc i) g t) (at t)"
  assumes mk: "m \<le> k"
  shows "\<forall>t \<in> Ush h U. (deriv ^^ m) (Dh h g) t = Dh h ((deriv ^^ m) g) t"
  using mk
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have m_lt: "m < k" using Suc.prems by simp
  have IH: "\<forall>t \<in> Ush h U. (deriv ^^ m) (Dh h g) t = Dh h ((deriv ^^ m) g) t"
    using Suc.IH m_lt by simp
  show ?case
  proof
    fix t assume t_in: "t \<in> Ush h U"
    have ev: "eventually (\<lambda>s. (deriv ^^ m) (Dh h g) s = Dh h ((deriv ^^ m) g) s) (nhds t)"
      using eventually_nhds_in_open[OF Ush_open[OF U_open] t_in] IH
      by (elim eventually_mono) blast
    have dt: "((deriv ^^ m) g has_real_derivative deriv ((deriv ^^ m) g) t) (at t)"
      using chain[OF m_lt Ush_mem[OF t_in]] by simp
    have dth: "((deriv ^^ m) g has_real_derivative deriv ((deriv ^^ m) g) (t + h)) (at (t + h))"
      using chain[OF m_lt Ush_shift[OF t_in]] by simp
    have "(deriv ^^ Suc m) (Dh h g) t = deriv ((deriv ^^ m) (Dh h g)) t"
      by simp
    also have "\<dots> = deriv (Dh h ((deriv ^^ m) g)) t"
      by (rule deriv_cong_ev[OF ev refl])
    also have "\<dots> = Dh h (deriv ((deriv ^^ m) g)) t"
      by (rule deriv_Dh[OF h_nz dt dth])
    finally show "(deriv ^^ Suc m) (Dh h g) t = Dh h ((deriv ^^ Suc m) g) t"
      by simp
  qed
qed

subsection \<open>The mean value theorem for the one-step quotient\<close>

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Dh_mvt:
  fixes g g' :: "real \<Rightarrow> real" and h x :: real
  assumes h_pos: "0 < h"
  assumes der: "\<And>s. \<lbrakk>x \<le> s; s \<le> x + h\<rbrakk> \<Longrightarrow> (g has_real_derivative g' s) (at s)"
  shows "\<exists>\<eta>. x < \<eta> \<and> \<eta> < x + h \<and> Dh h g x = g' \<eta>"
proof -
  have x_lt: "x < x + h" using h_pos by simp
  obtain z where z_lo: "x < z" and z_hi: "z < x + h"
    and eq: "g (x + h) - g x = (x + h - x) * g' z"
    using MVT2[OF x_lt der] by blast
  have "Dh h g x = (g (x + h) - g x) / h"
    by (simp add: Dh_def)
  also have "\<dots> = ((x + h - x) * g' z) / h"
    using eq by simp
  also have "\<dots> = g' z"
    using h_pos by simp
  finally show ?thesis using z_lo z_hi by blast
qed

(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Dh_abs_bound:
  fixes g g' :: "real \<Rightarrow> real" and h x M :: real
  assumes h_pos: "0 < h"
  assumes der: "\<And>s. \<lbrakk>x \<le> s; s \<le> x + h\<rbrakk> \<Longrightarrow> (g has_real_derivative g' s) (at s)"
  assumes bnd: "\<And>s. \<lbrakk>x \<le> s; s \<le> x + h\<rbrakk> \<Longrightarrow> \<bar>g' s\<bar> \<le> M"
  shows "\<bar>Dh h g x\<bar> \<le> M"
proof -
  obtain \<eta> where \<eta>_lo: "x < \<eta>" and \<eta>_hi: "\<eta> < x + h" and \<eta>_eq: "Dh h g x = g' \<eta>"
    using Dh_mvt[OF h_pos der] by blast
  show ?thesis
    using \<eta>_eq bnd[of \<eta>] \<eta>_lo \<eta>_hi by simp
qed

subsection \<open>Equation (4.4) for general \<open>j\<close>\<close>

text \<open>
  The induction that carries the whole estimate.  The hypothesis is applied not to \<open>f\<close> but to
  \<open>D\<^sub>h f\<close> -- on the shrunken domain \<^const>\<open>Ush\<close> -- so \<open>f\<close>, \<open>U\<close>, \<open>x\<close> and \<open>M\<close> must all be generalised
  over.  They are carried by an explicit \<open>\<forall>\<close> rather than by \<open>induction j arbitrary: f U x M\<close>,
  which in this project has been observed to desynchronise generalised variables from the goal
  text.

  Applying the hypothesis to \<open>D\<^sub>h f\<close> rather than to \<open>f\<close> is exactly what makes the induction work:
  the naive version, comparing \<open>E\<^sub>j\<^sub>+\<^sub>1\<close> to \<open>E\<^sub>j\<close> directly, produces the term
  \<open>(E\<^sub>j(x+h) - E\<^sub>j(x))/h\<close>, whose bound does not shrink with \<open>h\<close>.
\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma Dh_iterate_error_all:
  fixes h :: real and j :: nat
  assumes h_pos: "0 < h"
  shows "\<forall>(f :: real \<Rightarrow> real) U x M.
           open U
           \<and> (\<forall>i t. i \<le> j \<longrightarrow> t \<in> U
                \<longrightarrow> ((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f t) (at t))
           \<and> {x..x + real j * h} \<subseteq> U
           \<and> (\<forall>t. x \<le> t \<and> t \<le> x + real j * h \<longrightarrow> \<bar>(deriv ^^ Suc j) f t\<bar> \<le> M)
           \<longrightarrow> \<bar>(Dh h ^^ j) f x - (deriv ^^ j) f x\<bar> \<le> real j * M * h"
proof (induction j)
  case 0
  show ?case by simp
next
  case (Suc j)
  show ?case
  proof (intro allI impI)
    fix f :: "real \<Rightarrow> real" and U :: "real set" and x M :: real
    assume H: "open U
               \<and> (\<forall>i t. i \<le> Suc j \<longrightarrow> t \<in> U
                    \<longrightarrow> ((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f t) (at t))
               \<and> {x..x + real (Suc j) * h} \<subseteq> U
               \<and> (\<forall>t. x \<le> t \<and> t \<le> x + real (Suc j) * h
                     \<longrightarrow> \<bar>(deriv ^^ Suc (Suc j)) f t\<bar> \<le> M)"
    have U_open: "open U" using H by blast
    have chain: "\<And>i t. i \<le> Suc j \<Longrightarrow> t \<in> U
                   \<Longrightarrow> ((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f t) (at t)"
      using H by blast
    have seg: "{x..x + real (Suc j) * h} \<subseteq> U" using H by blast
    have bnd: "\<And>t. \<lbrakk>x \<le> t; t \<le> x + real (Suc j) * h\<rbrakk>
                 \<Longrightarrow> \<bar>(deriv ^^ Suc (Suc j)) f t\<bar> \<le> M"
      using H by blast
    have h_nz: "h \<noteq> 0" using h_pos by simp
    have Sj: "real (Suc j) * h = real j * h + h" by (simp add: algebra_simps)
    have jh_nonneg: "0 \<le> real j * h" using h_pos by simp

    define V where "V = Ush h U"
    have V_open: "open V" unfolding V_def by (rule Ush_open[OF U_open])

    text \<open>Every point of the inner segment, and its \<open>+h\<close> shift, lies in \<open>U\<close>.\<close>
    have inU: "\<And>t. \<lbrakk>x \<le> t; t \<le> x + real j * h\<rbrakk> \<Longrightarrow> t \<in> U \<and> t + h \<in> U"
    proof -
      fix t :: real
      assume t1: "x \<le> t" and t2: "t \<le> x + real j * h"
      have "t \<le> x + real (Suc j) * h" using t2 h_pos Sj by simp
      then have tU: "t \<in> U" using t1 seg by auto
      have "x \<le> t + h" using t1 h_pos by simp
      moreover have "t + h \<le> x + real (Suc j) * h" using t2 Sj by simp
      ultimately have "t + h \<in> U" using seg by auto
      then show "t \<in> U \<and> t + h \<in> U" using tU by blast
    qed
    have seg_V: "{x..x + real j * h} \<subseteq> V"
      unfolding V_def Ush_def using inU by auto

    text \<open>Commutation of \<open>D\<^sub>h\<close> with every derivative order the argument uses.\<close>
    have chain': "\<And>i t. i < Suc (Suc j) \<Longrightarrow> t \<in> U
                    \<Longrightarrow> ((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f t) (at t)"
      using chain by simp
    have commut: "\<And>m t. \<lbrakk>m \<le> Suc (Suc j); t \<in> V\<rbrakk>
                    \<Longrightarrow> (deriv ^^ m) (Dh h f) t = Dh h ((deriv ^^ m) f) t"
    proof -
      fix m :: nat and t :: real
      assume mle: "m \<le> Suc (Suc j)" and tV: "t \<in> V"
      show "(deriv ^^ m) (Dh h f) t = Dh h ((deriv ^^ m) f) t"
        using higher_deriv_Dh[OF h_nz U_open chain' mle] tV unfolding V_def by blast
    qed

    text \<open>The induction hypothesis applies to \<open>D\<^sub>h f\<close> on \<open>V\<close>: first the derivative chain.\<close>
    have chain_V: "\<And>i t. \<lbrakk>i \<le> j; t \<in> V\<rbrakk>
                     \<Longrightarrow> ((deriv ^^ i) (Dh h f) has_real_derivative
                            (deriv ^^ Suc i) (Dh h f) t) (at t)"
    proof -
      fix i :: nat and t :: real
      assume ij: "i \<le> j" and tV: "t \<in> V"
      have tU: "t \<in> U" using tV unfolding V_def by (rule Ush_mem)
      have thU: "t + h \<in> U" using tV unfolding V_def by (rule Ush_shift)
      have d1: "((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f t) (at t)"
        using chain[OF le_SucI[OF ij] tU] .
      have d2: "((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f (t + h)) (at (t + h))"
        using chain[OF le_SucI[OF ij] thU] .
      have base: "(Dh h ((deriv ^^ i) f) has_real_derivative Dh h ((deriv ^^ Suc i) f) t) (at t)"
        by (rule Dh_has_derivative[OF h_nz d1 d2])
      have agree: "\<And>s. s \<in> V \<Longrightarrow> Dh h ((deriv ^^ i) f) s = (deriv ^^ i) (Dh h f) s"
      proof -
        fix s :: real assume sV: "s \<in> V"
        show "Dh h ((deriv ^^ i) f) s = (deriv ^^ i) (Dh h f) s"
          using commut[of i s] ij sV by simp
      qed
      have transferred: "((deriv ^^ i) (Dh h f) has_real_derivative
                            Dh h ((deriv ^^ Suc i) f) t) (at t)"
        by (rule has_field_derivative_transform_within_open[OF base V_open tV agree])
      have "Dh h ((deriv ^^ Suc i) f) t = (deriv ^^ Suc i) (Dh h f) t"
        using commut[of "Suc i" t] ij tV by simp
      then show "((deriv ^^ i) (Dh h f) has_real_derivative
                    (deriv ^^ Suc i) (Dh h f) t) (at t)"
        using transferred by simp
    qed

    text \<open>Then the derivative bound, via the mean value theorem.\<close>
    have bnd_V: "\<And>t. \<lbrakk>x \<le> t; t \<le> x + real j * h\<rbrakk>
                   \<Longrightarrow> \<bar>(deriv ^^ Suc j) (Dh h f) t\<bar> \<le> M"
    proof -
      fix t :: real
      assume t1: "x \<le> t" and t2: "t \<le> x + real j * h"
      have tV: "t \<in> V" using seg_V t1 t2 by auto
      have range_s: "\<And>s. \<lbrakk>t \<le> s; s \<le> t + h\<rbrakk> \<Longrightarrow> x \<le> s \<and> s \<le> x + real (Suc j) * h"
      proof -
        fix s :: real assume s1: "t \<le> s" and s2: "s \<le> t + h"
        have "x \<le> s" using t1 s1 by simp
        moreover have "s \<le> x + real (Suc j) * h" using s2 t2 Sj by simp
        ultimately show "x \<le> s \<and> s \<le> x + real (Suc j) * h" by blast
      qed
      have der_s: "\<And>s. \<lbrakk>t \<le> s; s \<le> t + h\<rbrakk>
                     \<Longrightarrow> ((deriv ^^ Suc j) f has_real_derivative
                            (deriv ^^ Suc (Suc j)) f s) (at s)"
      proof -
        fix s :: real assume s1: "t \<le> s" and s2: "s \<le> t + h"
        have "s \<in> U" using range_s[OF s1 s2] seg by auto
        then show "((deriv ^^ Suc j) f has_real_derivative
                      (deriv ^^ Suc (Suc j)) f s) (at s)"
          using chain[of "Suc j" s] by simp
      qed
      have bnd_s: "\<And>s. \<lbrakk>t \<le> s; s \<le> t + h\<rbrakk> \<Longrightarrow> \<bar>(deriv ^^ Suc (Suc j)) f s\<bar> \<le> M"
        using range_s bnd by blast
      have "\<bar>Dh h ((deriv ^^ Suc j) f) t\<bar> \<le> M"
        by (rule Dh_abs_bound[OF h_pos der_s bnd_s])
      moreover have "(deriv ^^ Suc j) (Dh h f) t = Dh h ((deriv ^^ Suc j) f) t"
        using commut[of "Suc j" t] tV by simp
      ultimately show "\<bar>(deriv ^^ Suc j) (Dh h f) t\<bar> \<le> M" by simp
    qed

    have hyps: "open V
                \<and> (\<forall>i t. i \<le> j \<longrightarrow> t \<in> V
                     \<longrightarrow> ((deriv ^^ i) (Dh h f) has_real_derivative
                            (deriv ^^ Suc i) (Dh h f) t) (at t))
                \<and> {x..x + real j * h} \<subseteq> V
                \<and> (\<forall>t. x \<le> t \<and> t \<le> x + real j * h
                      \<longrightarrow> \<bar>(deriv ^^ Suc j) (Dh h f) t\<bar> \<le> M)"
      using V_open chain_V seg_V bnd_V by blast
    have IH_applied: "\<bar>(Dh h ^^ j) (Dh h f) x - (deriv ^^ j) (Dh h f) x\<bar> \<le> real j * M * h"
      using Suc.IH hyps by blast

    text \<open>Rewriting the two halves of the triangle inequality.\<close>
    text \<open>\<open>funpow_swap1\<close>, not \<open>funpow_Suc_right\<close>: \<open>simp\<close> normalises \<open>^^ Suc j\<close> to
      \<open>D\<^sub>h \<circ> (D\<^sub>h ^^ j)\<close>, leaving exactly the swap as the residual goal.\<close>
    have funpow_eq: "(Dh h ^^ j) (Dh h f) x = (Dh h ^^ Suc j) f x"
      by (simp add: funpow_swap1)
    have xV: "x \<in> V" using seg_V jh_nonneg by auto
    have mid: "(deriv ^^ j) (Dh h f) x = Dh h ((deriv ^^ j) f) x"
      using commut[of j x] xV by simp
    have first: "\<bar>(Dh h ^^ Suc j) f x - Dh h ((deriv ^^ j) f) x\<bar> \<le> real j * M * h"
      using IH_applied unfolding funpow_eq mid .

    text \<open>The second half: \<open>D\<^sub>h(f\<^sup>(\<^sup>j\<^sup>))(x) = f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)(\<eta>)\<close> for an interior \<open>\<eta>\<close>, and \<open>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<close> moves by
      at most \<open>M h\<close> across a step.\<close>
    have der_j: "\<And>s. \<lbrakk>x \<le> s; s \<le> x + h\<rbrakk>
                   \<Longrightarrow> ((deriv ^^ j) f has_real_derivative (deriv ^^ Suc j) f s) (at s)"
    proof -
      fix s :: real assume s1: "x \<le> s" and s2: "s \<le> x + h"
      have "s \<le> x + real (Suc j) * h" using s2 Sj jh_nonneg by simp
      then have "s \<in> U" using s1 seg by auto
      then show "((deriv ^^ j) f has_real_derivative (deriv ^^ Suc j) f s) (at s)"
        using chain[of j s] by simp
    qed
    obtain \<eta> where \<eta>1: "x < \<eta>" and \<eta>2: "\<eta> < x + h"
      and \<eta>eq: "Dh h ((deriv ^^ j) f) x = (deriv ^^ Suc j) f \<eta>"
      using Dh_mvt[OF h_pos der_j] by blast

    have second: "\<bar>Dh h ((deriv ^^ j) f) x - (deriv ^^ Suc j) f x\<bar> \<le> M * h"
    proof -
      have der2: "\<And>s. \<lbrakk>x \<le> s; s \<le> \<eta>\<rbrakk>
                    \<Longrightarrow> ((deriv ^^ Suc j) f has_real_derivative
                           (deriv ^^ Suc (Suc j)) f s) (at s)"
      proof -
        fix s :: real assume s1: "x \<le> s" and s2: "s \<le> \<eta>"
        have "s \<le> x + real (Suc j) * h" using s2 \<eta>2 Sj jh_nonneg by simp
        then have "s \<in> U" using s1 seg by auto
        then show "((deriv ^^ Suc j) f has_real_derivative
                      (deriv ^^ Suc (Suc j)) f s) (at s)"
          using chain[of "Suc j" s] by simp
      qed
      obtain z where z1: "x < z" and z2: "z < \<eta>"
        and zeq: "(deriv ^^ Suc j) f \<eta> - (deriv ^^ Suc j) f x
                    = (\<eta> - x) * (deriv ^^ Suc (Suc j)) f z"
        using MVT2[OF \<eta>1 der2] by blast
      have zM: "\<bar>(deriv ^^ Suc (Suc j)) f z\<bar> \<le> M"
      proof -
        have "x \<le> z" using z1 by simp
        moreover have "z \<le> x + real (Suc j) * h"
          using z2 \<eta>2 Sj jh_nonneg by simp
        ultimately show ?thesis using bnd by blast
      qed
      have "\<bar>(deriv ^^ Suc j) f \<eta> - (deriv ^^ Suc j) f x\<bar>
              = \<bar>\<eta> - x\<bar> * \<bar>(deriv ^^ Suc (Suc j)) f z\<bar>"
        using zeq by (simp add: abs_mult)
      also have "\<dots> \<le> h * M"
      proof (rule mult_mono)
        show "\<bar>\<eta> - x\<bar> \<le> h" using \<eta>1 \<eta>2 by simp
        show "\<bar>(deriv ^^ Suc (Suc j)) f z\<bar> \<le> M" using zM .
        show "0 \<le> h" using h_pos by simp
        show "0 \<le> \<bar>(deriv ^^ Suc (Suc j)) f z\<bar>" by simp
      qed
      finally show ?thesis
        unfolding \<eta>eq by (simp add: mult.commute)
    qed

    have "\<bar>(Dh h ^^ Suc j) f x - (deriv ^^ Suc j) f x\<bar>
            \<le> \<bar>(Dh h ^^ Suc j) f x - Dh h ((deriv ^^ j) f) x\<bar>
              + \<bar>Dh h ((deriv ^^ j) f) x - (deriv ^^ Suc j) f x\<bar>"
      using abs_triangle_ineq[of "(Dh h ^^ Suc j) f x - Dh h ((deriv ^^ j) f) x"
                                 "Dh h ((deriv ^^ j) f) x - (deriv ^^ Suc j) f x"]
      by simp
    also have "\<dots> \<le> real j * M * h + M * h"
      using first second by simp
    also have "\<dots> = real (Suc j) * M * h"
      by (simp add: algebra_simps)
    finally show "\<bar>(Dh h ^^ Suc j) f x - (deriv ^^ Suc j) f x\<bar> \<le> real (Suc j) * M * h" .
  qed
qed

text \<open>The same estimate with the project's usual \<^const>\<open>C_k_on\<close> hypothesis.\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
corollary Dh_iterate_error:
  fixes f :: "real \<Rightarrow> real" and h M x :: real and j :: nat and U :: "real set"
  assumes h_pos: "0 < h"
  assumes U_open: "open U"
  assumes Ck: "C_k_on (Suc j) f U"
  assumes seg: "{x..x + real j * h} \<subseteq> U"
  assumes bnd: "\<And>t. \<lbrakk>x \<le> t; t \<le> x + real j * h\<rbrakk> \<Longrightarrow> \<bar>(deriv ^^ Suc j) f t\<bar> \<le> M"
  shows "\<bar>(Dh h ^^ j) f x - (deriv ^^ j) f x\<bar> \<le> real j * M * h"
proof -
  have chain: "\<And>i t. i \<le> j \<Longrightarrow> t \<in> U
                 \<Longrightarrow> ((deriv ^^ i) f has_real_derivative (deriv ^^ Suc i) f t) (at t)"
    using Ck_on_derivative_chain[OF Ck] by simp
  show ?thesis
    using Dh_iterate_error_all[OF h_pos] U_open chain seg bnd by blast
qed

subsection \<open>Equation (4.4) in the paper's own notation\<close>

text \<open>
  On a uniform partition the nodes entering (4.2) are exactly the \<open>+h\<close> translates of \<open>x\<^sub>k\<close>, so
  \<^const>\<open>forward_diff\<close> is the iterate of \<^const>\<open>Dh\<close> anchored at \<open>x\<^sub>k\<close>.
\<close>
(* Auxiliary for estimate (4.4) in the proof of Theorem 4.1; not separately numbered. *)
lemma forward_diff_eq_Dh:
  fixes a b h :: real and N j k :: nat and xs :: "real list" and f :: "real \<Rightarrow> real"
  assumes h_def: "h = (b - a) / real N"
  assumes xs_def: "xs = unif_part a b N"
  assumes h_pos: "0 < h"
  assumes kj: "k + j \<le> N + 1"
  shows "forward_diff f xs h j k = (Dh h ^^ j) f (xs ! k)"
proof -
  have nodes: "\<And>v. v \<in> {0..j} \<Longrightarrow> f (xs ! (k + j - v)) = f (xs ! k + (real j - real v) * h)"
  proof -
    fix v :: nat assume "v \<in> {0..j}"
    then have vj: "v \<le> j" by simp
    have node1: "xs ! (k + j - v) = a + (real (k + j - v) - 1) * h"
      using xs_els[OF h_def xs_def] kj by auto
    have node2: "xs ! k = a + (real k - 1) * h"
      using xs_els[OF h_def xs_def] kj by auto
    have realsub: "real (k + j - v) = real k + real j - real v"
      using vj by (simp only: of_nat_diff)
    have "xs ! (k + j - v) = xs ! k + (real j - real v) * h"
      unfolding node1 node2 realsub by (simp add: algebra_simps)
    then show "f (xs ! (k + j - v)) = f (xs ! k + (real j - real v) * h)" by simp
  qed
  have sums: "(\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v * f (xs ! (k + j - v)))
                = (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v
                                 * f (xs ! k + (real j - real v) * h))"
    by (rule sum.cong[OF refl]) (simp add: nodes)
  have "forward_diff f xs h j k
          = (1 / h ^ j) * (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v * f (xs ! (k + j - v)))"
    unfolding forward_diff_def by simp
  also have "\<dots> = (1 / h ^ j)
                    * (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v
                                     * f (xs ! k + (real j - real v) * h))"
    unfolding sums by (rule refl)
  also have "\<dots> = (Dh h ^^ j) f (xs ! k)"
  proof -
    have "(Dh h ^^ j) f (xs ! k)
            = (1 / h ^ j) * (\<Sum>v\<in>{0..j}. real (j choose v) * (- 1) ^ v
                                            * f (xs ! k + (real j - real v) * h))"
      using Dh_iterate_sum[OF h_pos] by blast
    then show ?thesis by (rule sym)
  qed
  finally show ?thesis .
qed

text \<open>
  Equation (4.4) of the paper: \<open>\<bar>\<Delta>\<^sup>j\<^sub>k f - f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k)\<bar> \<le> Ctilde\<^sub>j h\<close> with the explicit constant
  \<open>Ctilde\<^sub>j = j\<sqdot>M\<close>, \<open>M\<close> any bound for \<open>\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar>\<close> on the cell \<open>[x\<^sub>k, x\<^sub>k\<^sub>+\<^sub>j]\<close> -- so, as the paper says,
  depending only on \<open>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<close>.  Since \<open>h=(b-a)/N\<close> this is the \<open>C\<^sub>j/N\<close> form used in Theorem 4.2.
\<close>
(* Equation (4.4): general-order consistency estimate. *)
theorem forward_diff_consistency:
  fixes f :: "real \<Rightarrow> real" and a b h M :: real and N j k :: nat
    and xs :: "real list" and U :: "real set"
  assumes h_def: "h = (b - a) / real N"
  assumes xs_def: "xs = unif_part a b N"
  assumes h_pos: "0 < h"
  assumes kj: "k + j \<le> N + 1"
  assumes U_open: "open U"
  assumes Ck: "C_k_on (Suc j) f U"
  assumes seg: "{xs ! k..xs ! (k + j)} \<subseteq> U"
  assumes bnd: "\<And>t. \<lbrakk>xs ! k \<le> t; t \<le> xs ! (k + j)\<rbrakk> \<Longrightarrow> \<bar>(deriv ^^ Suc j) f t\<bar> \<le> M"
  shows "\<bar>forward_diff f xs h j k - (deriv ^^ j) f (xs ! k)\<bar> \<le> real j * M * h"
proof -
  have node1: "xs ! (k + j) = a + (real (k + j) - 1) * h"
    using xs_els[OF h_def xs_def] kj by auto
  have node2: "xs ! k = a + (real k - 1) * h"
    using xs_els[OF h_def xs_def] kj by auto
  have top: "xs ! (k + j) = xs ! k + real j * h"
    unfolding node1 node2 by (simp add: algebra_simps)
  have "\<bar>(Dh h ^^ j) f (xs ! k) - (deriv ^^ j) f (xs ! k)\<bar> \<le> real j * M * h"
    using Dh_iterate_error[OF h_pos U_open Ck] seg bnd unfolding top by blast
  then show ?thesis
    unfolding forward_diff_eq_Dh[OF h_def xs_def h_pos kj] .
qed

end
