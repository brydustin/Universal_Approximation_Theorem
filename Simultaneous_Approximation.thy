section \<open>Simultaneous Approximation of \<open>f\<close> and \<open>f'\<close> (Theorem 4.1, \<open>j=1\<close> case)\<close>

theory Simultaneous_Approximation
  imports Derivative_Approximation
begin

text \<open>
  This theory begins the proof of Theorem 4.1 of Costarelli and Spigler~\cite{CostarelliSpigler}
  for \<open>j=1\<close>: the same network construction that approximates \<open>f\<close> uniformly (Theorem 2.1) also
  approximates \<open>f'\<close>, once its coefficients are replaced by \<open>\<Delta>\<^sup>1 f\<close>-differences (\<open>Gj_network\<close>,
  eq. (4.3)). The proof reuses Theorem 2.1's own argument structure (a local two-step proxy
  \<open>L_i\<close>, split into \<open>I_1\<close>/\<open>I_2\<close> errors), transported onto \<open>\<Delta>\<^sup>1 f\<close> via the bridge lemmas already
  proved in theory \<open>Derivative_Approximation\<close> (\<open>forward_diff_one_node_error\<close>,
  \<open>forward_diff_one_two_node_bound\<close>). It is NOT yet complete: this theory only sets up the
  preamble (choice of \<open>\<eta>\<close>, \<open>\<delta>\<close>, \<open>N\<close>, \<open>w\<close>) common to every case of the eventual proof, verified
  to compile against the real supporting lemmas; the case-split proof body (mirroring Theorem
  2.1's \<open>L_i\<close>/\<open>I_1\<close>/\<open>I_2\<close> argument, plus the extra right-boundary case \<open>Gj_network\<close>'s missing
  \<open>N+1\<close>-th node forces -- see the discussion recorded alongside this development) is future
  work.
\<close>

(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
theorem forward_diff_one_approximation_preamble:
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>N w \<eta> \<delta>. N > 3 \<and> w > 0 \<and> \<eta> > 0 \<and> \<delta> > 0 \<and>
           (\<forall>x \<in> {a..b}. \<forall>y \<in> {a..b}. \<bar>x - y\<bar> < \<delta>
              \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>) \<and>
           (real N) * \<delta> > 2 * (b - a) \<and> 1 / real N < \<eta> \<and>
           (b - a) / real N
             * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta> \<and>
           \<eta> * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) \<le> \<epsilon> \<and>
           (\<forall>k < N + 2. (\<forall>x. x - unif_part a b N ! k \<ge> (b - a) / real N
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / real N) \<and>
                        (\<forall>x. x - unif_part a b N ! k \<le> - ((b - a) / real N)
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / real N))"
proof -
  text \<open>\<open>g := f'\<close> is continuous on \<open>[a,b]\<close>, so uniformly continuous there (\<open>Ck_on_continuous_first_derivative\<close>).\<close>
  have g_cont: "continuous_on {a..b} (deriv f)"
    using Ck_on_continuous_first_derivative[OF Ck] continuous_on_subset[OF _ ab_subset]
    by blast

  text \<open>\<open>C\<^sub>1\<close>, the supremum of \<open>|f''|\<close> on \<open>[a,b]\<close>: the constant governing \<open>\<Delta>\<^sup>1 f\<close>'s own \<open>O(h)\<close> node error
    (\<open>forward_diff_one_node_error\<close>), needed as an extra slack term \<open>\<eta>\<close> must absorb, on top of
    the role \<open>\<eta>\<close> already plays in Theorem 2.1's own proof.\<close>
  obtain C1 where C1_def: "C1 = Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
    by blast
  have C1_nonneg: "C1 \<ge> 0"
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
    have bdd: "bdd_above ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
      using a_lt_b cont continuous_image_closed_interval continuous_on_rabs
      by (metis bdd_above_Icc order_less_le)
    show ?thesis
      unfolding C1_def using a_lt_b bdd
      by (meson a_lt_b abs_ge_zero atLeastAtMost_iff cSUP_upper2 order_le_less)
  qed

  text \<open>Choose \<open>\<eta>\<close> from \<open>\<epsilon>\<close> and bounds on \<open>f'\<close> and \<open>\<sigma>\<close>. Unlike Theorem 2.1's own \<open>\<eta>\<close> (denominator
    the sup of \<open>|f'|\<close> plus twice the sup of \<open>|\<sigma>|\<close> plus \<open>2\<close>), this theorem's combined \<open>I_1+J_2\<close>
    bound (worst case, the generic/left-boundary cases: \<open>I_1<\<eta>(5/2+M_1)\<close>,
    \<open>J_2<\<eta>(1+2S)+C_1h(1/2+2S)\<close>, and \<open>C_1h<\<eta>\<close>) needs a larger denominator, \<open>4+M_1+4S\<close>, to close
    (worked out by hand): \<open>\<eta>(5/2+M_1)+\<eta>(1+2S)+\<eta>(1/2+2S)=\<eta>(4+M_1+4S)\<close>.\<close>
  obtain \<eta> where \<eta>_def: "\<eta> = \<epsilon> / (4 + (Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}))
                                  + (4 * (Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV))))"
    by blast
  have sup_g_nonneg: "Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) \<ge> 0"
  proof -
    have "bdd_above ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
      by (metis a_lt_b bdd_above_Icc g_cont continuous_image_closed_interval continuous_on_rabs order_less_le)
    thus ?thesis
      by (meson a_lt_b abs_ge_zero atLeastAtMost_iff cSUP_upper2 order_le_less)
  qed
  have sup_\<sigma>_nonneg: "Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV) \<ge> 0"
    using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I abs_ge_zero cSUP_upper2)
  have \<eta>_pos: "\<eta> > 0"
    unfolding \<eta>_def using eps_pos sup_g_nonneg sup_\<sigma>_nonneg by simp

  text \<open>Uniform continuity of \<open>f'\<close> gives \<open>\<delta>\<close> (this is the generic, already-proved
    \<open>uniform_continuity_interval\<close>, exactly as Theorem 2.1 uses it for \<open>f\<close> itself).\<close>
  obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and \<delta>_prop: "\<forall>x \<in> {a..b}. \<forall>y \<in> {a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
    using uniform_continuity_interval[OF g_cont \<eta>_pos] by blast

  text \<open>Choose \<open>N\<close> large enough for all four needs: mesh \<open>h<\<delta>/2\<close>, \<open>1/N<\<eta>\<close>, the extra
    \<open>\<Delta>\<^sup>1 f\<close>-specific slack \<open>h\<sqdot>C_1<\<eta>\<close>, and \<open>N>3\<close> (matching Theorem 2.1's own \<open>N_def\<close>, with one
    more term folded into the max).\<close>
  obtain N where N_def: "N = (nat (\<lfloor>max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>)))\<rfloor>) + 1)"
    by simp
  have N_defining_properties: "N > 2 * (b - a) / \<delta> \<and> N > 3 \<and> N > 1 / \<eta> \<and> N > (b - a) * C1 / \<eta>"
    unfolding N_def
  proof -
    have "max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>))) \<ge> 2 * (b - a) / \<delta> \<and>
          max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>))) \<ge> 2 \<and>
          max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>))) \<ge> 1 / \<eta> \<and>
          max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>))) \<ge> (b - a) * C1 / \<eta>"
      unfolding max_def by simp
    then show "2 * (b - a) / \<delta> < nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>)))\<rfloor> + 1 \<and>
               3 < nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>)))\<rfloor> + 1 \<and>
               1 / \<eta> < nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>)))\<rfloor> + 1 \<and>
               (b - a) * C1 / \<eta> < nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (max (1 / \<eta>) ((b - a) * C1 / \<eta>)))\<rfloor> + 1"
      by (smt (verit, best) floor_le_one numeral_Bit1 numeral_less_real_of_nat_iff numeral_plus_numeral
          of_nat_1 of_nat_add of_nat_nat one_plus_numeral real_of_int_floor_add_one_gt)
  qed
  have N_gt_3: "N > 3"
    using N_defining_properties by simp
  then have N_pos: "N > 0"
    by simp

  obtain h where h_def: "h = (b - a) / N"
    by simp
  have h_pos: "h > 0"
    using N_defining_properties a_lt_b h_def by force

  have h_lt_\<delta>_half: "h < \<delta> / 2"
  proof -
    have "N > 2 * (b - a) / \<delta>"
      using N_defining_properties by force
    then have "N / 2 > (b - a) / \<delta>"
      by (simp add: mult.commute)
    then have "(N / 2) * \<delta> > (b - a)"
      by (smt (verit, ccfv_SIG) \<delta>_pos divide_less_cancel nonzero_mult_div_cancel_right)
    then have "(\<delta> / 2) * N > (b - a)"
      by (simp add: mult.commute)
    then have "(\<delta> / 2) > (b - a) / N"
      by (smt (verit, ccfv_SIG) \<delta>_pos a_lt_b divide_less_cancel nonzero_mult_div_cancel_right zero_less_divide_iff)
    then show "h < \<delta> / 2"
      using h_def by blast
  qed

  have one_over_N_lt_eta: "1 / N < \<eta>"
  proof -
    have f1: "real N \<ge> max (2 * (b - a) / \<delta> - 1) (max (1 / \<eta>) ((b-a)*C1/\<eta>) )"
      unfolding N_def
      by (smt (verit) N_def N_defining_properties) 
    have "real N \<ge> 1 / \<eta>"
      unfolding max_def using f1 max.bounded_iff by (smt (verit))
    hence f2: "1 / real N \<le> \<eta>"
      using \<eta>_pos by (smt (verit, ccfv_SIG) divide_divide_eq_right le_divide_eq_1 mult.commute zero_less_divide_1_iff)
    then show "1 / real N < \<eta>"
      using N_defining_properties nle_le by fastforce
  qed

  have h_C1_lt_eta: "h * C1 < \<eta>"
  proof -
    have "real N > (b - a) * C1 / \<eta>"
      using N_defining_properties by force
    then show ?thesis
      unfolding h_def by (simp add: N_pos \<eta>_pos mult_of_nat_commute pos_divide_less_eq)
  qed

  text \<open>Apply \<open>sigmoidal_uniform_approximation\<close> exactly as Theorem 2.1 does, at \<open>1/N, h>0\<close> and
    the (extended) partition \<open>unif_part a b N\<close>.\<close>
  from sigmoidal_function N_pos h_pos have
    "\<exists>\<omega> > 0. \<forall>w \<ge> \<omega>. \<forall>k < length (unif_part a b N).
             (\<forall>x. x - unif_part a b N ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1/N) \<and>
             (\<forall>x. x - unif_part a b N ! k \<le> -h \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1/N)"
    by (subst sigmoidal_uniform_approximation, simp_all)
  then obtain \<omega> where \<omega>_pos: "\<omega> > 0"
    and \<omega>_prop: "\<forall>w \<ge> \<omega>. \<forall>k < length (unif_part a b N).
             (\<forall>x. x - unif_part a b N ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1/N) \<and>
             (\<forall>x. x - unif_part a b N ! k \<le> -h \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1/N)"
    by blast
  obtain w where w_def: "w = \<omega>"
    by blast
  have w_pos: "w > 0"
    unfolding w_def by (rule \<omega>_pos)
  have w_prop: "\<forall>k < length (unif_part a b N).
             (\<forall>x. x - unif_part a b N ! k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1/N) \<and>
             (\<forall>x. x - unif_part a b N ! k \<le> -h \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1/N)"
    unfolding w_def using \<omega>_prop by simp

  have length_xs: "length (unif_part a b N) = N + 2"
    unfolding unif_part_def by simp

  have delta_bound: "(real N) * \<delta> > 2 * (b - a)"
  proof -
    have "(b - a) / N < \<delta> / 2"
      using h_lt_\<delta>_half h_def by simp
    then have "2 * ((b - a) / N) < \<delta>"
      by (simp add: algebra_simps)
    then have step: "2 * ((b - a) / N) * N < \<delta> * N"
      using N_pos by (intro mult_strict_right_mono) simp_all
    have "2 * ((b - a) / N) * N = 2 * (b - a)"
      using N_pos by simp
    then have "2 * (b - a) < \<delta> * N"
      using step by simp
    then show ?thesis
      by (simp only: mult.commute)
  qed
  have C1_bound: "(b - a) / real N * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
    using h_C1_lt_eta unfolding h_def C1_def by simp
  have w_prop': "\<forall>k < N + 2. (\<forall>x. x - unif_part a b N ! k \<ge> (b - a) / real N
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / real N) \<and>
                       (\<forall>x. x - unif_part a b N ! k \<le> - ((b - a) / real N)
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / real N)"
    using w_prop length_xs h_def by simp
  text \<open>\<open>\<eta>\<close> was chosen exactly so that this holds with equality (see \<open>\<eta>_def\<close> above); export it
    explicitly, since the final case-dispatch assembly (\<open>Simultaneous_Approximation.thy\<close>'s
    \<open>forward_diff_one_approximation\<close>) needs this relationship and cannot recover it from \<open>\<eta>\<close>'s
    other listed properties alone.\<close>
  have eps_bound: "\<eta> * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) \<le> \<epsilon>"
  proof -
    have denom_pos: "4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV) > 0"
      using sup_g_nonneg sup_\<sigma>_nonneg by simp
    show ?thesis
      unfolding \<eta>_def using denom_pos by (simp add: field_simps)
  qed

  have main: "N > 3 \<and> w > 0 \<and> \<eta> > 0 \<and> \<delta> > 0 \<and>
           (\<forall>x \<in> {a..b}. \<forall>y \<in> {a..b}. \<bar>x - y\<bar> < \<delta>
              \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>) \<and>
           (real N) * \<delta> > 2 * (b - a) \<and> 1 / real N < \<eta> \<and>
           (b - a) / real N
             * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta> \<and>
           \<eta> * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) \<le> \<epsilon> \<and>
           (\<forall>k < N + 2. (\<forall>x. x - unif_part a b N ! k \<ge> (b - a) / real N
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / real N) \<and>
                        (\<forall>x. x - unif_part a b N ! k \<le> - ((b - a) / real N)
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / real N))"
  proof (intro conjI)
    show "N > 3" by (rule N_gt_3)
    show "w > 0" by (rule w_pos)
    show "\<eta> > 0" by (rule \<eta>_pos)
    show "\<delta> > 0" by (rule \<delta>_pos)
    show "\<forall>x \<in> {a..b}. \<forall>y \<in> {a..b}. \<bar>x - y\<bar> < \<delta>
             \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
      by (rule \<delta>_prop)
    show "(real N) * \<delta> > 2 * (b - a)" by (rule delta_bound)
    show "1 / real N < \<eta>" by (rule one_over_N_lt_eta)
    show "(b - a) / real N * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
      by (rule C1_bound)
    show "\<eta> * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) \<le> \<epsilon>"
      by (rule eps_bound)
    show "\<forall>k < N + 2. (\<forall>x. x - unif_part a b N ! k \<ge> (b - a) / real N
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / real N) \<and>
                       (\<forall>x. x - unif_part a b N ! k \<le> - ((b - a) / real N)
                            \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / real N)"
      by (rule w_prop')
  qed
  then show ?thesis
    by blast
qed

text \<open>
  The interior (\<open>I_2\<close>-style) piece of Theorem 4.1's case-split proof body: for a node \<open>i\<close> away
  from both boundaries (\<open>2 \<le> i \<le> N-1\<close>, so that \<open>i-1\<close> and \<open>i+1\<close> are both valid \<open>\<Delta>\<^sup>1 f\<close>
  indices), the local two-step proxy
  \<open>L_i(x) := \<Delta>\<^sup>1_{i-1}f + (\<Delta>\<^sup>1_i f - \<Delta>\<^sup>1_{i-1} f)\<sigma>(w(x-x_i)) + (\<Delta>\<^sup>1_{i+1}f-\<Delta>\<^sup>1_i f)\<sigma>(w(x-x_{i+1}))\<close>
  (Theorem 2.1's own \<open>L_i\<close> template, eq. after telescoping the leading sum, with \<open>\<Delta>\<^sup>1 f\<close> in
  place of \<open>f\<close> itself) approximates \<open>f'(x)\<close> to within \<open>\<eta>(1+2S) + C_1 h(1/2+2S)\<close>, where
  \<open>S\<close> the supremum of \<open>|\<sigma>|\<close> and \<open>C\<^sub>1\<close> the supremum of \<open>|f''|\<close> on \<open>[a,b]\<close>. This is exactly
  Theorem 2.1's own \<open>I_2\<close> bound
  (which would just be \<open>\<eta>(1+2S)\<close>, from uniform continuity of \<open>f\<close> alone) plus one extra
  \<open>C_1 h\<close>-sized slack term, coming from replacing \<open>f\<close>'s own node values by the \<open>O(h)\<close>-accurate
  \<open>\<Delta>\<^sup>1 f\<close> values (\<open>forward_diff_one_node_error\<close>) and coefficient differences
  (\<open>forward_diff_one_two_node_bound\<close>) -- confirming the earlier prediction that the \<open>I_2\<close>-style
  argument needs no new technique beyond the bridge lemmas already proved.

  Paper correspondence: Theorem 4.1 itself has no proof written out in the paper -- it cites
  "the same argument as that in Theorem 4.1" inside the \<open>Theorem 4.2\<close> proof, which is where
  this argument actually appears in print (p.180-181 of the PDF). Specifically: the \<open>L_i\<close>
  formula above is the paper's own \<open>L_i(x)\<close>, case "\<open>i = 3, \<dots>, N-j\<close>" (p.180, just below the
  \<open>i=1,2\<close> case); this lemma proves the \<open>j=1\<close> specialization of the bound the paper calls
  \<open>J_2\<close>, "Case 2: \<open>i = 3, \<dots>, N-j\<close>" (p.181, immediately after "We now estimate \<open>J_2\<close> in four
  different cases"). \<open>J_2 := |L_i(x) - f^{(j)}(x)|\<close> is the second half of the paper's own
  triangle-inequality split \<open>(G_N^j f)(x)-f^{(j)}(x) \<le> J_1+J_2\<close>; \<open>J_1 := |(G_N^j f)(x)-L_i(x)|\<close>
  (the \<open>I_1\<close>-style, \<open>\<sigma>\<close>-saturation-weighted global-sum piece) is not yet formalized.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_generic_L_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "2 * h < \<delta>"
  assumes i_range: "i \<in> {2..N - 1}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))
          - deriv f x\<bar>
       \<le> \<eta> * (1 + 2 * S) + C1 * h * (1 / 2 + 2 * S)"
proof -
  have h_pos': "h > 0"
    by (rule h_pos[OF a_lt_b N_pos h_def])
  have im1_range: "i - 1 \<in> {1..N}" and i_range': "i \<in> {1..N}" and ip1_range: "i + 1 \<in> {1..N}"
    using i_range by auto
  have im1_N1: "i - 1 \<in> {1..N+1}" and i_N1: "i \<in> {1..N+1}" and ip1_N1: "i + 1 \<in> {1..N+1}"
    using i_range by auto

  have x_in_ab: "x \<in> {a..b}"
  proof -
    have i_in_ab: "xs ! i \<in> {a..b}" and ip1_in_ab: "xs ! (i + 1) \<in> {a..b}"
      using els_in_ab[OF a_lt_b N_pos h_def xs_def] i_range' ip1_N1 by auto
    show ?thesis
      using x_in_cell i_in_ab ip1_in_ab by auto
  qed

  text \<open>Node distances: \<open>x\<close> is within \<open>h\<close> of \<open>x_i\<close>/\<open>x_{i+1}\<close>, and within \<open>2h\<close> of \<open>x_{i-1}\<close>.\<close>
  have step_i: "xs ! (i + 1) - xs ! i = h"
    using difference_of_adj_terms[OF h_def xs_def, of "i + 1"] ip1_N1 by auto
  have step_im1: "xs ! i - xs ! (i - 1) = h"
    using difference_of_adj_terms[OF h_def xs_def, of i] i_N1 by auto
  have x_minus_i: "\<bar>x - xs ! i\<bar> \<le> h"
    using x_in_cell step_i h_pos' by auto
  have x_minus_im1: "\<bar>x - xs ! (i - 1)\<bar> \<le> 2 * h"
    using x_in_cell step_i step_im1 h_pos' by auto

  have nodes_in_ab: "xs ! (i - 1) \<in> {a..b}" "xs ! i \<in> {a..b}" "xs ! (i + 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] im1_N1 i_N1 ip1_N1 by auto

  text \<open>Bound A: \<open>\<Delta>\<^sup>1_{i-1} f\<close> is within \<open>C_1h/2\<close> of \<open>f'(x_{i-1})\<close>, itself within \<open>\<eta>\<close> of \<open>f'(x)\<close>.\<close>
  have boundA: "\<bar>forward_diff f xs h 1 (i - 1) - deriv f x\<bar> \<le> C1 * h / 2 + \<eta>"
  proof -
    have node: "\<bar>forward_diff f xs h 1 (i - 1) - deriv f (xs ! (i - 1))\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def
      by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset im1_range])
    have cont: "\<bar>deriv f (xs ! (i - 1)) - deriv f x\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(1) x_in_ab x_minus_im1 h_lt by auto
    show ?thesis
      using node cont by linarith
  qed

  text \<open>Bound B: consecutive \<open>\<Delta>\<^sup>1 f\<close>-values are within \<open>\<eta> + C_1h\<close> of each other.\<close>
  have boundB: "\<bar>forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)\<bar> \<le> \<eta> + C1 * h"
  proof -
    have two_node: "\<bar>forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)\<bar>
         \<le> \<bar>deriv f (xs ! i) - deriv f (xs ! (i - 1))\<bar> + C1 * h"
      unfolding C1_def
      by (rule forward_diff_one_two_node_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset i_range' im1_range])
    have cont: "\<bar>deriv f (xs ! i) - deriv f (xs ! (i - 1))\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(2) nodes_in_ab(1) step_im1 h_pos' h_lt by auto
    show ?thesis
      using two_node cont by linarith
  qed

  have boundC: "\<bar>forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i\<bar> \<le> \<eta> + C1 * h"
  proof -
    have two_node: "\<bar>forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i\<bar>
         \<le> \<bar>deriv f (xs ! (i + 1)) - deriv f (xs ! i)\<bar> + C1 * h"
      unfolding C1_def
      by (rule forward_diff_one_two_node_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset ip1_range i_range'])
    have cont: "\<bar>deriv f (xs ! (i + 1)) - deriv f (xs ! i)\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(3) nodes_in_ab(2) step_i h_pos' h_lt by auto
    show ?thesis
      using two_node cont by linarith
  qed

  have S_bound1: "\<bar>\<sigma> (w * (x - xs ! i))\<bar> \<le> S"
    unfolding S_def using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I cSUP_upper2 order_refl)
  have S_bound2: "\<bar>\<sigma> (w * (x - xs ! (i + 1)))\<bar> \<le> S"
    unfolding S_def using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I cSUP_upper2 order_refl)

  have rearrange: "(forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))
          - deriv f x
      = (forward_diff f xs h 1 (i - 1) - deriv f x)
        + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
        + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1)))"
    by simp

  have "\<bar>(forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))
          - deriv f x\<bar>
      \<le> \<bar>forward_diff f xs h 1 (i - 1) - deriv f x\<bar>
        + \<bar>forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! i))\<bar>
        + \<bar>forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i\<bar> * \<bar>\<sigma> (w * (x - xs ! (i + 1)))\<bar>"
  proof -
    have triangle3: "\<And>p q r::real. \<bar>p + q + r\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar> + \<bar>r\<bar>"
    proof -
      fix p q r :: real
      have s1: "\<bar>p + q + r\<bar> \<le> \<bar>p + q\<bar> + \<bar>r\<bar>"
        by (rule abs_triangle_ineq)
      have s2: "\<bar>p + q\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar>"
        by (rule abs_triangle_ineq)
      from s1 s2 show "\<bar>p + q + r\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar> + \<bar>r\<bar>"
        by linarith
    qed
    show ?thesis
      unfolding rearrange
      using triangle3[of "forward_diff f xs h 1 (i - 1) - deriv f x"
                          "(forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))"
                          "(forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1)))"]
      by (simp only: abs_mult)
  qed
  also have "\<dots> \<le> (C1 * h / 2 + \<eta>) + (\<eta> + C1 * h) * S + (\<eta> + C1 * h) * S"
  proof -
    have S_nonneg: "S \<ge> 0"
      using S_bound1 by linarith
    have coeff_nonneg: "0 \<le> \<eta> + C1 * h"
      using boundB by linarith
    have prodB: "\<bar>forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! i))\<bar>
       \<le> (\<eta> + C1 * h) * S"
    proof -
      have "\<bar>forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! i))\<bar>
         \<le> (\<eta> + C1 * h) * \<bar>\<sigma> (w * (x - xs ! i))\<bar>"
        using boundB by (simp only: mult_right_mono)
      also have "\<dots> \<le> (\<eta> + C1 * h) * S"
        using S_bound1 coeff_nonneg by (rule mult_left_mono)
      finally show ?thesis .
    qed
    have prodC: "\<bar>forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i\<bar> * \<bar>\<sigma> (w * (x - xs ! (i + 1)))\<bar>
       \<le> (\<eta> + C1 * h) * S"
    proof -
      have
        "\<bar>forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i\<bar> * \<bar>\<sigma> (w * (x - xs ! (i + 1)))\<bar>
         \<le> (\<eta> + C1 * h) * \<bar>\<sigma> (w * (x - xs ! (i + 1)))\<bar>"
        using boundC by (simp only: mult_right_mono)
      also have "\<dots> \<le> (\<eta> + C1 * h) * S"
        using S_bound2 coeff_nonneg by (rule mult_left_mono)
      finally show ?thesis .
    qed
    then show ?thesis
      using boundA prodB by linarith
  qed
  also have "\<dots> = \<eta> * (1 + 2 * S) + C1 * h * (1 / 2 + 2 * S)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>
  The left-boundary (\<open>i=1,2\<close>) case of the same \<open>J_2\<close> bound: paper's own \<open>L_i(x) := \<Delta>\<^sup>j_0f +
  (\<Delta>\<^sup>j_2f-\<Delta>\<^sup>j_1f)\<sigma>(w(x-x_2)) + (\<Delta>\<^sup>j_1f-\<Delta>\<^sup>j_0f)\<sigma>(w(x-x_1))\<close> "for \<open>i=1,2\<close>" (p.180, just above the
  \<open>i=3,\<dots>,N-j\<close> case), and \<open>J_2\<close> "Case 1: \<open>i=1,2\<close>" (p.181, immediately before Case 2). In our
  \<open>xs\<close>-offset-by-one convention (\<open>xs!k\<close> = paper's \<open>x_{k-1}\<close>, so paper's \<open>\<Delta>\<^sup>1_m f\<close> is our
  \<open>forward_diff f xs h 1 (m+1)\<close>): paper's \<open>x_0=a\<close>, \<open>x_1\<close>, \<open>x_2\<close> become our \<open>xs!1\<close>, \<open>xs!2\<close>,
  \<open>xs!3\<close>, and \<open>\<Delta>\<^sup>1_0f\<close>, \<open>\<Delta>\<^sup>1_1f\<close>, \<open>\<Delta>\<^sup>1_2f\<close> become \<open>forward_diff f xs h 1 1\<close>,
  \<open>forward_diff f xs h 1 2\<close>, \<open>forward_diff f xs h 1 3\<close>. The proof is identical in shape to
  \<open>forward_diff_one_generic_L_bound\<close> (same three bridge-lemma applications, same combination),
  the only difference being that \<open>x\<close> is within \<open>2h\<close> of \<open>a\<close> (not of an interior node \<open>x_{i-1}\<close>)
  -- so it gives the exact same bound.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_left_boundary_L_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "2 * h < \<delta>"
  assumes i_range: "i \<in> {1, 2}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h 1 1
           + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
           + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2)))
          - deriv f x\<bar>
       \<le> \<eta> * (1 + 2 * S) + C1 * h * (1 / 2 + 2 * S)"
proof -
  have N_pos: "N > 0"
    using N_gt3 by simp
  have one_N: "(1::nat) \<in> {1..N}" and two_N: "(2::nat) \<in> {1..N}" and three_N: "(3::nat) \<in> {1..N}"
    using N_gt3 by auto
  have one_N1: "(1::nat) \<in> {1..N+1}" and two_N1: "(2::nat) \<in> {1..N+1}" and three_N1: "(3::nat) \<in> {1..N+1}"
    using N_gt3 by auto

  have x_in_ab: "x \<in> {a..b}"
  proof -
    have i_in_ab: "xs ! i \<in> {a..b}" and ip1_in_ab: "xs ! (i + 1) \<in> {a..b}"
      using els_in_ab[OF a_lt_b N_pos h_def xs_def] i_range one_N1 two_N1 three_N1 by auto
    show ?thesis
      using x_in_cell i_in_ab ip1_in_ab by auto
  qed

  text \<open>\<open>x\<close> is within \<open>2h\<close> of \<open>a = xs!1\<close>, whichever of \<open>i=1,2\<close> holds.\<close>
  have step_1: "xs ! 2 - xs ! 1 = h"
    using difference_of_adj_terms[OF h_def xs_def, of 2] two_N1 by auto
  have step_2: "xs ! 3 - xs ! 2 = h"
    using difference_of_adj_terms[OF h_def xs_def, of 3] three_N1 by auto
  have i_disj: "i = 1 \<or> i = 2"
    using i_range by auto
  have x_minus_a: "\<bar>x - xs ! 1\<bar> \<le> 2 * h"
    using i_disj
  proof
    assume "i = 1"
    then have "x \<in> {xs ! 1 .. xs ! 2}"
      using x_in_cell by (simp add: eval_nat_numeral)
    then show ?thesis
      using step_1 h_pos[OF a_lt_b N_pos h_def] by auto
  next
    assume "i = 2"
    then have "x \<in> {xs ! 2 .. xs ! 3}"
      using x_in_cell by (simp add: eval_nat_numeral)
    then show ?thesis
      using step_1 step_2 by auto
  qed

  have nodes_in_ab: "xs ! 1 \<in> {a..b}" "xs ! 2 \<in> {a..b}" "xs ! 3 \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] one_N1 two_N1 three_N1 by auto

  have boundA: "\<bar>forward_diff f xs h 1 1 - deriv f x\<bar> \<le> C1 * h / 2 + \<eta>"
  proof -
    have node: "\<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def
      by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset one_N])
    have cont: "\<bar>deriv f (xs ! 1) - deriv f x\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(1) x_in_ab x_minus_a h_lt by auto
    show ?thesis
      using node cont by linarith
  qed

  have boundB: "\<bar>forward_diff f xs h 1 3 - forward_diff f xs h 1 2\<bar> \<le> \<eta> + C1 * h"
  proof -
    have two_node: "\<bar>forward_diff f xs h 1 3 - forward_diff f xs h 1 2\<bar>
         \<le> \<bar>deriv f (xs ! 3) - deriv f (xs ! 2)\<bar> + C1 * h"
      unfolding C1_def
      by (rule forward_diff_one_two_node_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset three_N two_N])
    have cont: "\<bar>deriv f (xs ! 3) - deriv f (xs ! 2)\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(3) nodes_in_ab(2) step_2 h_pos[OF a_lt_b N_pos h_def] h_lt by auto
    show ?thesis
      using two_node cont by linarith
  qed

  have boundC: "\<bar>forward_diff f xs h 1 2 - forward_diff f xs h 1 1\<bar> \<le> \<eta> + C1 * h"
  proof -
    have two_node: "\<bar>forward_diff f xs h 1 2 - forward_diff f xs h 1 1\<bar>
         \<le> \<bar>deriv f (xs ! 2) - deriv f (xs ! 1)\<bar> + C1 * h"
      unfolding C1_def
      by (rule forward_diff_one_two_node_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset two_N one_N])
    have cont: "\<bar>deriv f (xs ! 2) - deriv f (xs ! 1)\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(2) nodes_in_ab(1) step_1 h_pos[OF a_lt_b N_pos h_def] h_lt by auto
    show ?thesis
      using two_node cont by linarith
  qed

  have S_bound1: "\<bar>\<sigma> (w * (x - xs ! 3))\<bar> \<le> S"
    unfolding S_def using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I cSUP_upper2 order_refl)
  have S_bound2: "\<bar>\<sigma> (w * (x - xs ! 2))\<bar> \<le> S"
    unfolding S_def using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I cSUP_upper2 order_refl)

  have rearrange: "(forward_diff f xs h 1 1
           + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
           + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2)))
          - deriv f x
      = (forward_diff f xs h 1 1 - deriv f x)
        + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
        + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2))"
    by simp

  have "\<bar>(forward_diff f xs h 1 1
           + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
           + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2)))
          - deriv f x\<bar>
      \<le> \<bar>forward_diff f xs h 1 1 - deriv f x\<bar>
        + \<bar>forward_diff f xs h 1 3 - forward_diff f xs h 1 2\<bar> * \<bar>\<sigma> (w * (x - xs ! 3))\<bar>
        + \<bar>forward_diff f xs h 1 2 - forward_diff f xs h 1 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 2))\<bar>"
  proof -
    have triangle3: "\<And>p q r::real. \<bar>p + q + r\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar> + \<bar>r\<bar>"
    proof -
      fix p q r :: real
      have s1: "\<bar>p + q + r\<bar> \<le> \<bar>p + q\<bar> + \<bar>r\<bar>"
        by (rule abs_triangle_ineq)
      have s2: "\<bar>p + q\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar>"
        by (rule abs_triangle_ineq)
      from s1 s2 show "\<bar>p + q + r\<bar> \<le> \<bar>p\<bar> + \<bar>q\<bar> + \<bar>r\<bar>"
        by linarith
    qed
    show ?thesis
      unfolding rearrange
      using triangle3[of "forward_diff f xs h 1 1 - deriv f x"
                          "(forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))"
                          "(forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2))"]
      by (simp only: abs_mult)
  qed
  also have "\<dots> \<le> (C1 * h / 2 + \<eta>) + (\<eta> + C1 * h) * S + (\<eta> + C1 * h) * S"
  proof -
    have S_nonneg: "S \<ge> 0"
      using S_bound1 by linarith
    show ?thesis
      using boundA boundB boundC S_bound1 S_bound2 S_nonneg
      by (meson abs_ge_zero add_mono mult_mono')
  qed
  also have "\<dots> = \<eta> * (1 + 2 * S) + C1 * h * (1 / 2 + 2 * S)"
    by (simp only: algebra_simps)
  finally show ?thesis .
qed

text \<open>
  The right-boundary case, \<open>i=N\<close>: paper's own \<open>L_i(x)\<close> "for \<open>i=N-j+1\<close>" (p.180) and \<open>J_2\<close>
  "Case 3: \<open>i=N-j+1\<close>" (p.181-182). For \<open>j=1\<close> this is \<open>i=N\<close> exactly, and it is the ONLY
  right-boundary case that occurs: the paper's own "Case 4: \<open>i=N-j+2,\<dots>,N\<close>" needs
  \<open>N-j+2\<le>N\<close>, i.e. \<open>j\<ge>2\<close>, so it is vacuous for \<open>j=1\<close> -- matching the structural fact recorded
  above that \<open>Gj_network\<close>'s sum has no \<open>\<Delta>\<^sup>1_{N+1}f\<close> term to build a second \<open>\<sigma>\<close>-step from. After
  telescoping (as in the generic case), the paper's \<open>L_i\<close> for \<open>i=N-j+1\<close> reduces to
  \<open>L(x) := \<Delta>\<^sup>1_{N-1}f + (\<Delta>\<^sup>1_Nf-\<Delta>\<^sup>1_{N-1}f)\<sigma>(w(x-x_{N-1}))\<close> (paper indices; in our
  \<open>xs\<close>-offset-by-one convention, \<open>x_{N-1}=xs!N\<close>), with only ONE active \<open>\<sigma>\<close>-step -- matching
  the paper's own Case 3 bound having coefficient \<open>2\<close> where Cases 1/2 have \<open>4\<close> (one \<open>S\<close>-term
  instead of two). Proof is the two-bridge-lemma restriction of the generic-case argument.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_right_boundary_L_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "2 * h < \<delta>"
  assumes x_in_cell: "x \<in> {xs ! N .. xs ! (N + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>(forward_diff f xs h 1 (N - 1)
           + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N)))
          - deriv f x\<bar>
       \<le> \<eta> * (1 + S) + C1 * h * (1 / 2 + S)"
proof -
  have N_pos: "N > 0"
    using N_gt3 by simp
  have Nm1_N: "N - 1 \<in> {1..N}" and N_N: "N \<in> {1..N}"
    using N_gt3 by auto
  have Nm1_N1: "N - 1 \<in> {1..N+1}" and N_N1: "N \<in> {1..N+1}" and Np1_N1: "N + 1 \<in> {1..N+1}"
    using N_gt3 by auto

  have x_in_ab: "x \<in> {a..b}"
  proof -
    have i_in_ab: "xs ! N \<in> {a..b}" and ip1_in_ab: "xs ! (N + 1) \<in> {a..b}"
      using els_in_ab[OF a_lt_b N_pos h_def xs_def] N_N1 Np1_N1 by auto
    show ?thesis
      using x_in_cell i_in_ab ip1_in_ab by auto
  qed

  text \<open>\<open>x\<close> is within \<open>2h\<close> of \<open>x_{N-1}=xs!N\<close> and within \<open>h\<close> of \<open>xs!N\<close>.\<close>
  have step_N: "xs ! N - xs ! (N - 1) = h"
    using difference_of_adj_terms[OF h_def xs_def, of N] N_N1 by auto
  have step_Np1: "xs ! (N + 1) - xs ! N = h"
    using difference_of_adj_terms[OF h_def xs_def, of "N + 1"] Np1_N1 by auto
  have x_minus_N: "\<bar>x - xs ! N\<bar> \<le> h"
    using x_in_cell step_Np1 h_pos[OF a_lt_b N_pos h_def] by auto
  have x_minus_Nm1: "\<bar>x - xs ! (N - 1)\<bar> \<le> 2 * h"
    using x_in_cell step_N step_Np1 h_pos[OF a_lt_b N_pos h_def] by auto

  have nodes_in_ab: "xs ! (N - 1) \<in> {a..b}" "xs ! N \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] Nm1_N1 N_N1 by auto

  have boundA: "\<bar>forward_diff f xs h 1 (N - 1) - deriv f x\<bar> \<le> C1 * h / 2 + \<eta>"
  proof -
    have node: "\<bar>forward_diff f xs h 1 (N - 1) - deriv f (xs ! (N - 1))\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def
      by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset Nm1_N])
    have cont: "\<bar>deriv f (xs ! (N - 1)) - deriv f x\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(1) x_in_ab x_minus_Nm1 h_lt by auto
    show ?thesis
      using node cont by linarith
  qed

  have boundB: "\<bar>forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)\<bar> \<le> \<eta> + C1 * h"
  proof -
    have two_node: "\<bar>forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)\<bar>
         \<le> \<bar>deriv f (xs ! N) - deriv f (xs ! (N - 1))\<bar> + C1 * h"
      unfolding C1_def
      by (rule forward_diff_one_two_node_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset N_N Nm1_N])
    have cont: "\<bar>deriv f (xs ! N) - deriv f (xs ! (N - 1))\<bar> < \<eta>"
      using \<delta>_prop nodes_in_ab(2) nodes_in_ab(1) step_N h_pos[OF a_lt_b N_pos h_def] h_lt by auto
    show ?thesis
      using two_node cont by linarith
  qed

  have S_bound1: "\<bar>\<sigma> (w * (x - xs ! N))\<bar> \<le> S"
    unfolding S_def using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I cSUP_upper2 order_refl)

  have rearrange: "(forward_diff f xs h 1 (N - 1)
           + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N)))
          - deriv f x
      = (forward_diff f xs h 1 (N - 1) - deriv f x)
        + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N))"
    by simp

  have "\<bar>(forward_diff f xs h 1 (N - 1)
           + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N)))
          - deriv f x\<bar>
      \<le> \<bar>forward_diff f xs h 1 (N - 1) - deriv f x\<bar>
        + \<bar>forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! N))\<bar>"
    unfolding rearrange by (rule order_trans[OF abs_triangle_ineq]) (simp add: abs_mult)
  also have "\<dots> \<le> (C1 * h / 2 + \<eta>) + (\<eta> + C1 * h) * S"
    by (meson S_bound1 abs_ge_zero add_mono_thms_linordered_semiring(1) boundA boundB mult_mono') 
  also have "\<dots> = \<eta> * (1 + S) + C1 * h * (1 / 2 + S)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>
  The first building block of the \<open>J_1\<close>/\<open>I_1\<close> estimate (paper p.180-181, the harder,
  \<open>\<sigma>\<close>-saturation-weighted global-sum piece of Theorem 4.1's proof, not yet assembled as a
  whole). \<open>J_1\<close>'s printed form (e.g. \<open>(1/N)\<Sum>_k|\<Delta>^j_kf-f^{(j)}(x_k)|\<close>) already has the
  \<open>\<sigma>\<close>-saturation bound (either \<open>|\<sigma>(w(x-x_k))-1|<1/N\<close> or \<open>|\<sigma>(w(x-x_k))|<1/N\<close>) folded in -- this
  lemma is exactly that folding step for one term, combining \<open>forward_diff_one_node_error\<close> with
  a saturation hypothesis in the shape the preamble's own conclusion supplies. Two versions, one
  per saturation direction (\<open>\<sigma>\<approx>1\<close> for nodes to the left of \<open>x\<close>, \<open>\<sigma>\<approx>0\<close> for nodes to the right);
  each still needs its own node-index range hypothesis and target node, matching how
  \<open>Gj_network\<close>'s own sum indexes its coefficients.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_saturated_term_bound_left:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes k_range: "k \<in> {1..N}"
  assumes sat: "\<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> < 1 / real N"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
       \<le> (C1 / 2) * h * (1 / real N)"
proof -
  have node: "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> \<le> (C1 / 2) * h"
    unfolding C1_def
    by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_range])
  have node_nonneg: "0 \<le> (C1 / 2) * h"
    using order_trans[OF abs_ge_zero node] .
  show ?thesis
    using mult_mono[OF node less_imp_le[OF sat] node_nonneg abs_ge_zero] .
qed

(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_saturated_term_bound_right:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes k_range: "k \<in> {1..N}"
  assumes sat: "\<bar>\<sigma> (w * (x - xs ! k))\<bar> < 1 / real N"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>
       \<le> (C1 / 2) * h * (1 / real N)"
proof -
  have node: "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> \<le> (C1 / 2) * h"
    unfolding C1_def
    by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_range])
  have node_nonneg: "0 \<le> (C1 / 2) * h"
    using order_trans[OF abs_ge_zero node] .
  show ?thesis
    using mult_mono[OF node less_imp_le[OF sat] node_nonneg abs_ge_zero] .
qed

text \<open>
  The second building block of \<open>J_1\<close> (paper p.180-181): the "consecutive node" piece
  \<open>(1/N)\<Sum>_k|f^{(j)}(x_k)-f^{(j)}(x_{k-1})|\<close>, bounded per-term via the Lipschitz constant for
  \<open>f'\<close> supplied by \<open>deriv_lipschitz_bound\<close> together with the fact that adjacent nodes are
  distance \<open>h\<close> apart. Restricted to \<open>k\<in>{2..N}\<close> so both \<open>xs!k\<close> and \<open>xs!(k-1)\<close> stay inside
  \<open>{a..b}\<close>; the \<open>k=1\<close> edge term (paper's \<open>x_{-1}\<close>-adjacent boundary piece) is one of \<open>J_1\<close>'s
  separate boundary terms and is not covered here.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_node_diff_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes k_range: "k \<in> {2..N}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar> \<le> C1 * h"
proof -
  have k_in_range: "k \<in> {1..N+1}" and km1_in_range: "k - 1 \<in> {1..N+1}"
    using k_range by auto
  have xk_in: "xs ! k \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] k_in_range by blast
  have xkm1_in: "xs ! (k - 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] km1_in_range by blast
  have step: "xs ! k - xs ! (k - 1) = h"
    using difference_of_adj_terms[OF h_def xs_def] k_range by auto
  have hpos: "h > 0"
    using h_pos[OF a_lt_b N_pos h_def] .
  have "\<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>
      \<le> C1 * \<bar>xs ! k - xs ! (k - 1)\<bar>"
    unfolding C1_def
    using deriv_lipschitz_bound[OF Ck ab_subset a_lt_b xk_in xkm1_in] .
  also have "\<dots> = C1 * h"
    using step hpos by simp
  finally show ?thesis .
qed

text \<open>
  The last piece \<open>J_1\<close> needs beyond the sum itself (paper p.181, the final term
  \<open>(1/N)|f^{(j)}(x_0)|\<close> of the printed bound): unlike the other \<open>J_1\<close> terms this one does not
  vanish on its own, it is simply bounded by the sup of \<open>|f'|\<close> over \<open>[a,b]\<close>, so that multiplying
  by the preamble's \<open>1/N<\<eta>\<close> makes its contribution to \<open>J_1\<close> vanish as N grows. (The paired term
  \<open>|\<Delta>^j_0f-f^{(j)}(x_0)|\<close> needs no separate lemma: with \<open>x_0=xs!1=a\<close> in this project's indexing,
  it is exactly \<open>forward_diff_one_node_error\<close> at \<open>m=1\<close>.)
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_boundary_deriv_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "\<bar>deriv f (xs ! 1)\<bar> \<le> M1"
proof -
  have cont: "continuous_on U (deriv f)"
    using Ck_on_continuous_first_derivative[OF Ck] .
  have cont': "continuous_on {a..b} (deriv f)"
    using cont ab_subset continuous_on_subset by blast
  have bdd: "bdd_above ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
    using a_lt_b cont' continuous_image_closed_interval continuous_on_rabs
    by (metis bdd_above_Icc order_less_le)
  have x1_a: "xs ! 1 = a"
    using first_element[OF h_def xs_def] .
  have a_in: "a \<in> {a..b}"
    using a_lt_b by simp
  show ?thesis
    unfolding M1_def x1_a
    using cSUP_upper[OF a_in bdd] .
qed

text \<open>
  The first \<open>J_1\<close> sum, as literally printed (paper p.181, first term of the displayed bound):
  \<open>(1/N)\<Sum>_{k=1}^{N-j}|\<Delta>^j_kf-f^{(j)}(x_k)|\<close> -- here just the un-scaled sum
  \<open>\<Sum>_{k=1}^{M}|\<Delta>^1_kf-f'(x_k)|\<close> for \<open>M\<le>N\<close> (the \<open>1/N\<close> scaling and the \<open>M=N-j\<close> instantiation
  happen at the final assembly step), bounded termwise by \<open>forward_diff_one_node_error\<close> and
  summed. Confirms the paper's own claim that this whole sum stays \<open>O(1)\<close> (not \<open>O(1/N)\<close>) before
  the outer \<open>1/N\<close> is applied, since it has \<open>\<le>N\<close> terms each \<open>O(h)=O(1/N)\<close>.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_node_error_sum_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes M_le_N: "M \<le> N"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "(\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>) \<le> real M * ((C1 / 2) * h)"
proof -
  have term_bound: "\<And>k. k \<in> {1..M} \<Longrightarrow> \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> \<le> (C1 / 2) * h"
  proof -
    fix k assume "k \<in> {1..M}"
    then have "k \<in> {1..N}" using M_le_N by auto
    then show "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def
      by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset])
  qed
  have "(\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>) \<le> (\<Sum>k=1..M. (C1 / 2) * h)"
    using term_bound by (intro sum_mono) auto
  also have "\<dots> = real M * ((C1 / 2) * h)"
    by simp
  finally show ?thesis .
qed

text \<open>
  The second \<open>J_1\<close> sum, as literally printed (paper p.181, second term):
  \<open>(1/N)\<Sum>_{k=1}^{N-j}|f^{(j)}(x_k)-f^{(j)}(x_{k-1})|\<close>. In this project's indexing (\<open>xs!m=x_{m-1}\<close>),
  the paper's index \<open>k\<close> shifts to \<open>k+1\<close>, so the sum runs over \<open>k'\<in>{2..M+1}\<close> for \<open>M=N-j\<close>; we
  state it directly with the shifted bound \<open>M'\<le>N\<close> (\<open>=M+1\<close> at the final assembly step) and sum
  over \<open>{2..M'}\<close>, matching \<open>forward_diff_one_node_diff_bound\<close>'s own \<open>k\<in>{2..N}\<close> range.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_node_diff_sum_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes M_le_N: "M \<le> N"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "(\<Sum>k=2..M. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>) \<le> real (M - 1) * (C1 * h)"
proof -
  have term_bound: "\<And>k. k \<in> {2..M} \<Longrightarrow> \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar> \<le> C1 * h"
  proof -
    fix k assume "k \<in> {2..M}"
    then have "k \<in> {2..N}" using M_le_N by auto
    then show "\<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar> \<le> C1 * h"
      unfolding C1_def
      by (rule forward_diff_one_node_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset])
  qed
  have "(\<Sum>k=2..M. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>) \<le> (\<Sum>k=2..M. C1 * h)"
    using term_bound by (intro sum_mono) auto
  also have "\<dots> = real (M - 1) * (C1 * h)"
    by simp
  finally show ?thesis .
qed

text \<open>
  The third \<open>J_1\<close> sum (paper p.181, third term): \<open>(1/N)\<Sum>_{k=1}^{N-j}|f^{(j)}(x_{k-1})-\<Delta>^j_{k-1}f|\<close>.
  In this project's indexing this is \<open>forward_diff_one_node_error\<close>'s bound again, but over the
  node-index set shifted down by one from the first sum's -- rather than re-deriving a second
  shifted-range lemma matching \<open>forward_diff_one_node_error_sum_bound\<close>'s pattern, this general
  arbitrary-finite-index-set version covers both shifted sums (and the plain \<open>{1..M}\<close> case, as a
  trivial corollary via \<open>S={1..M}\<close>) uniformly, since every individual term's bound
  (\<open>forward_diff_one_node_error\<close>) only needs its index in \<open>{1..N}\<close>, not any particular range shape.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_node_error_sum_bound_general:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes S_sub: "S \<subseteq> {1..N}" and S_fin: "finite S"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "(\<Sum>k\<in>S. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>) \<le> real (card S) * ((C1 / 2) * h)"
proof -
  have term_bound: "\<And>k. k \<in> S \<Longrightarrow> \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> \<le> (C1 / 2) * h"
  proof -
    fix k assume "k \<in> S"
    then have "k \<in> {1..N}" using S_sub by auto
    then show "\<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def
      by (rule forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset])
  qed
  have "(\<Sum>k\<in>S. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>) \<le> (\<Sum>k\<in>S. (C1 / 2) * h)"
    using term_bound by (intro sum_mono) auto
  also have "\<dots> = real (card S) * ((C1 / 2) * h)"
    using S_fin by simp
  finally show ?thesis .
qed

text \<open>
  Full \<open>J_1\<close> sum assembly for \<open>j=1\<close> (paper p.181, combining all five printed terms via the
  triangle inequality, \<open>M:=N-1\<close> in this project's own building blocks): the un-scaled total
  \<open>\<Sum>_{k=1}^{M}|\<Delta>^1_kf-f'(x_k)| + \<Sum>_{k=2}^{M+1}|f'(x_k)-f'(x_{k-1})|
     + \<Sum>_{k=2}^{M+1}|\<Delta>^1_kf-f'(x_k)| + |\<Delta>^1_1f-f'(x_1)| + |f'(x_1)|\<close>
  stays \<open>O(1)\<close> (not growing with \<open>N\<close>), matching the paper's own claim that \<open>J_1=O(1/N)\<close> once the
  outer \<open>1/N\<close> (from the preamble's \<open>\<eta>\<close>/saturation choice, not re-derived here) is applied.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_J1_sum_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes M_le_N: "M < N" and M_pos: "M \<ge> 1"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "(\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
       + (\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>)
       + (\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
       + \<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar>
       + \<bar>deriv f (xs ! 1)\<bar>
       \<le> real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h)
       + (C1 / 2) * h + M1"
proof -
  have first: "(\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>) \<le> real M * ((C1 / 2) * h)"
    unfolding C1_def
    using forward_diff_one_node_error_sum_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset] M_le_N
    by simp
  have second: "(\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>) \<le> real M * (C1 * h)"
    unfolding C1_def
    using forward_diff_one_node_diff_sum_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of "M+1"]
          M_le_N
    by simp
  have S_sub: "{2..M+1} \<subseteq> {1..N}"
    using M_le_N by auto
  have S_fin: "finite {2..M+1::nat}"
    by simp
  have card_S: "card {2..M+1::nat} = M"
    by simp
  have third: "(\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>) \<le> real M * ((C1 / 2) * h)"
    unfolding C1_def
    using forward_diff_one_node_error_sum_bound_general[OF a_lt_b N_pos h_def xs_def Ck ab_subset
      S_sub S_fin] card_S
    by simp
  have fourth: "\<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar> \<le> (C1 / 2) * h"
    unfolding C1_def
    using forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 1] N_pos
    by simp
  have fifth: "\<bar>deriv f (xs ! 1)\<bar> \<le> M1"
    unfolding M1_def
    using forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset]
    by simp
  show ?thesis
    using first second third fourth fifth by linarith
qed

text \<open>
  Scaling \<open>forward_diff_one_J1_sum_bound\<close> by the outer \<open>1/N\<close> (paper p.181's own \<open>J_1\<close> formula
  has this \<open>1/N\<close> multiplying the whole bracket) and folding in the preamble's two slack
  conditions \<open>h\<cdot>C_1<\<eta>\<close> and \<open>1/N<\<eta>\<close> (\<open>forward_diff_one_approximation_preamble\<close>) collapses the
  five-term \<open>O(1)\<close> total into a single bound purely in terms of \<open>\<eta>\<close> (and the fixed constant
  \<open>M_1\<close>, the sup of \<open>|f'|\<close>), matching the paper's own claim that \<open>J_1\<close> vanishes as N grows (\<open>\<eta>\<close>
  shrinking to \<open>0\<close>). This is the O(1/N)-rate statement Theorem 4.2 itself needs; Theorem 4.1 only
  needs \<open>J_1\<close> to vanish, which follows immediately once \<open>\<eta>\<close> is chosen small (as the preamble
  already does).
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_J1_eta_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes M_le_N: "M < N" and M_pos: "M \<ge> 1"
  assumes \<eta>_pos: "\<eta> > 0"
  assumes hC1_lt_\<eta>: "h * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
  assumes N_inv_lt_\<eta>: "1 / real N < \<eta>"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "(1 / real N) *
         ((\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
          + (\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>)
          + (\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
          + \<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar>
          + \<bar>deriv f (xs ! 1)\<bar>)
       < \<eta> * (5 / 2 + M1)"
proof -
  have hC1_lt: "h * C1 < \<eta>"
    unfolding C1_def using hC1_lt_\<eta> .
  have hpos: "h > 0"
    using h_pos[OF a_lt_b N_pos h_def] .
  have C1h_nonneg: "0 \<le> C1 * h"
    using order_trans[OF abs_ge_zero forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def
      Ck ab_subset, of 1]] N_pos
    unfolding C1_def by simp
  have C1_nonneg: "C1 \<ge> 0"
    using C1h_nonneg hpos by (simp add: zero_le_mult_iff)
  have M1_nonneg: "M1 \<ge> 0"
    using order_trans[OF abs_ge_zero forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def
      xs_def Ck ab_subset]] unfolding M1_def by simp
  have MN: "real M / real N < 1"
    using M_le_N N_pos by (simp add: divide_less_eq)
  have MN_nonneg: "real M / real N \<ge> 0"
    using M_le_N N_pos by simp

  have sum_bound: "(\<Sum>k=1..M. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
       + (\<Sum>k=2..M+1. \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar>)
       + (\<Sum>k=2..M+1. \<bar>forward_diff f xs h 1 k - deriv f (xs ! k)\<bar>)
       + \<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar>
       + \<bar>deriv f (xs ! 1)\<bar>
       \<le> real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h)
       + (C1 / 2) * h + M1"
    unfolding C1_def M1_def
    using forward_diff_one_J1_sum_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset M_le_N M_pos] .

  have term123: "(1 / real N) * (real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h))
       < \<eta> / 2 + \<eta> + \<eta> / 2"
  proof -
    have "(1 / real N) * (real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h))
        = 2 * ((real M / real N) * (C1 * h))"
      by (simp add: field_simps)
    also have "\<dots> \<le> 2 * (1 * (C1 * h))"
      using MN MN_nonneg hC1_lt hpos C1_nonneg
      by (intro mult_left_mono mult_right_mono) auto
    also have "\<dots> < \<eta> / 2 + \<eta> + \<eta> / 2"
      using hC1_lt by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have term4: "(1 / real N) * ((C1 / 2) * h) < \<eta> / 2"
  proof -
    have N_ge_1: "real N \<ge> 1"
      using N_pos by (simp add: less_eq_Suc_le)
    have "1 / real N \<le> 1"
      using N_ge_1 by simp
    then have "(1 / real N) * ((C1 / 2) * h) \<le> 1 * ((C1 / 2) * h)"
      using hpos C1_nonneg by (intro mult_right_mono) auto
    also have "\<dots> = (C1 / 2) * h" by simp
    finally have "(1 / real N) * ((C1 / 2) * h) \<le> (C1 / 2) * h" .
    also have "\<dots> < \<eta> / 2"
      using hC1_lt by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have term5': "(1 / real N) * M1 \<le> \<eta> * M1"
    using N_inv_lt_\<eta> M1_nonneg by (intro mult_right_mono) auto

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
  also have "\<dots> = (1 / real N) * (real M * ((C1 / 2) * h) + real M * (C1 * h) + real M * ((C1 / 2) * h))
                 + (1 / real N) * ((C1 / 2) * h) + (1 / real N) * M1"
    by (simp add: ring_distribs)
  also have "\<dots> < (\<eta> / 2 + \<eta> + \<eta> / 2) + \<eta> / 2 + \<eta> * M1"
    using term123 term4 term5' by linarith
  also have "\<dots> = \<eta> * (5 / 2 + M1)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>
  The telescoping-sum identity underlying \<open>J_1\<close> itself (not yet formalized above as an
  identity, only its final consequence): replaying Theorem 2.1's own \<open>I_1\<close> derivation
  (\<open>Universal_Approximation_1d.thy\<close>, the main case \<open>i\<ge>3\<close> of \<open>I1_decomp\<close>) with \<open>\<Delta>\<^sup>1f\<close> in place
  of \<open>f\<close>: this shows the actual network quantity \<open>|(G_N^1f)(x)-L_i(x)|\<close> (not just an abstract
  sum, as the earlier \<open>J_1\<close> building blocks assumed) is bounded by exactly the sum this
  project's \<open>forward_diff_one_saturated_term_bound_left\<close>/\<open>_right\<close> lemmas were built for --
  confirming those two lemmas (flagged earlier as "not used in this particular assembly") are
  in fact the ones this identity needs. \<open>Gj_network\<close>'s own sum (eq 4.3) is reindexed here from
  its \<open>k\<in>{1..N-1}\<close>/\<open>k+1\<close> form to the \<open>m\<in>{2..N}\<close> form matching \<open>G_Nf\<close>'s own shape (the \<open>N+1\<close> of
  Theorem 2.1 becomes \<open>N\<close> here, per the structural fact recorded above that \<open>Gj_network\<close> has no
  \<open>\<Delta>\<^sup>1_{N+1}f\<close> term). Matches paper's \<open>J_2\<close> "Case 2: \<open>i=3,\<dots>,N-j\<close>" range, i.e. \<open>i\<in>{3..N-1}\<close> for
  \<open>j=1\<close>.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_I1_generic_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes i_range: "i \<in> {3..N - 1}"
  shows "\<bar>Gj_network \<sigma> f xs h N 1 w x -
          (forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))\<bar>
       \<le> (\<Sum>k=2..i - 1. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
             * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
         + \<bar>forward_diff f xs h 1 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
         + (\<Sum>k=i + 2..N. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
             * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
proof -
  define Df where "Df = (\<lambda>k. forward_diff f xs h 1 k)"
  have three_leq_i: "i \<ge> 3" and i_leq: "i \<le> N - 1"
    using i_range by auto

  text \<open>Reindex \<open>Gj_network\<close>'s sum from \<open>k\<in>{1..N-1}\<close> (shifted by \<open>k+1\<close>) to \<open>m\<in>{2..N}\<close>.\<close>
  have Gnet_eq: "Gj_network \<sigma> f xs h N 1 w x
      = (\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m))) + Df 1 * \<sigma> (w * (x - xs ! 0))"
  proof -
    have "(\<Sum>k\<in>{1..N-1}. (Df (k + 1) - Df k) * \<sigma> (w * (x - xs ! (k + 1))))
        = (\<Sum>m\<in>{2..N}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>m. m - 1" "\<lambda>k. k + 1"]) auto
    then show ?thesis
      unfolding Gj_network_def Df_def by simp
  qed

  text \<open>Telescoping: the raw sum from \<open>2\<close> to \<open>i-1\<close>, plus \<open>Df 1\<close>, collapses to \<open>Df(i-1)\<close>.\<close>
  have telescope_shift: "(\<Sum>k=2..i - 1. Df k - Df (k - 1)) + Df 1 = Df (i - 1)"
  proof -
    have full: "(\<Sum>k=1..i - 1. Df k - Df (k - 1)) + Df 0 = Df (i - 1)"
      unfolding Df_def using forward_diff_telescope[of f xs h 1 "i - 1"] .
    have split: "(\<Sum>k=1..i - 1. Df k - Df (k - 1))
        = (Df 1 - Df 0) + (\<Sum>k=2..i - 1. Df k - Df (k - 1))"
      using three_leq_i by (subst sum.atLeast_Suc_atMost) (auto simp add: eval_nat_numeral)
    from full split show ?thesis by linarith
  qed

  have disjoint: "{2..i - 1} \<inter> {i..N} = {}"
    by auto
  have union: "{2..i - 1} \<union> {i..N} = {2..N}"
    using three_leq_i i_leq by auto
  have sum_of_terms:
    "(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
     + (\<Sum>k=i..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
     = (\<Sum>k=2..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
  proof -
    have "(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
       + (\<Sum>k=i..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
       = (\<Sum>k\<in>{2..i - 1} \<union> {i..N}. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
      by (rule sum.union_disjoint[symmetric]) (auto simp add: disjoint)
    then show ?thesis
      using union by simp
  qed

  have step1: "Gj_network \<sigma> f xs h N 1 w x
      - (Df (i - 1)
         + (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
         + (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1))))
    = ((\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
       - (\<Sum>k=2..i - 1. Df k - Df (k - 1)))
      + (\<Sum>k=i..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
      + Df 1 * \<sigma> (w * (x - xs ! 0))
      - Df 1
      - (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
      - (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1)))"
    unfolding Gnet_eq sum_of_terms[symmetric] telescope_shift[symmetric] by simp

  have peel1: "(\<Sum>k=i..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
      = (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
        + (\<Sum>k=i+1..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
    using i_leq by (subst sum.atLeast_Suc_atMost) auto
  have peel2: "(\<Sum>k=i+1..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))
      = (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1)))
        + (\<Sum>k=i+2..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
    using i_leq three_leq_i by (subst sum.atLeast_Suc_atMost) auto

  have step2: "Gj_network \<sigma> f xs h N 1 w x
      - (Df (i - 1)
         + (Df i - Df (i - 1)) * \<sigma> (w * (x - xs ! i))
         + (Df (i + 1) - Df i) * \<sigma> (w * (x - xs ! (i + 1))))
    = (\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)
      + (\<Sum>k=i+2..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"
    unfolding step1 peel1 peel2
    by (simp add: sum_subtractf right_diff_distrib' left_diff_distrib')

  have abs_bound: "\<bar>(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)
      + (\<Sum>k=i+2..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))\<bar>
    \<le> (\<Sum>k=2..i - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
      + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
      + (\<Sum>k=i+2..N. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
  proof -
    have t1: "\<bar>(\<Sum>k=2..i - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))\<bar>
        \<le> (\<Sum>k=2..i - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)"
      by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
    have t2: "\<bar>Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar> = \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
      by (simp add: abs_mult)
    have t3: "\<bar>(\<Sum>k=i+2..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))\<bar>
        \<le> (\<Sum>k=i+2..N. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)"
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
                   "(\<Sum>k=i+2..N. (Df k - Df (k - 1)) * \<sigma> (w * (x - xs ! k)))"]
            t1 t2 t3
      by linarith
  qed
  show ?thesis
    using Df_def abs_bound step2 by presburger
qed

text \<open>
  Bounding \<open>I_1\<close> numerically needs a per-term bound on \<open>|\<Delta>^1_k f-\<Delta>^1_{k-1}f|\<close> itself (the
  quantity \<open>forward_diff_one_I1_generic_bound\<close>'s sum weights by \<open>\<sigma>\<close>), NOT a bound against the
  true derivative \<open>f'(x_k)\<close> (that was what \<open>forward_diff_one_saturated_term_bound_left\<close>/
  \<open>_right\<close> were for, and turns out NOT to be what this identity's own sum needs -- a
  correction to this project's own earlier speculation). This is exactly
  \<open>forward_diff_one_generic_L_bound\<close>'s own \<open>boundB\<close>/\<open>boundC\<close> step, generalized to an arbitrary
  pair of adjacent nodes \<open>k,k-1\<close> rather than only \<open>i,i-1\<close> and \<open>i+1,i\<close>: consecutive nodes are
  always \<open>h\<close> apart, and \<open>h<\<delta>\<close> (the preamble's own mesh condition) makes \<open>f'\<close> itself \<open>\<eta>\<close>-close
  there, regardless of \<open>k\<close>'s position relative to the active cell.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_coeff_diff_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "h < \<delta>"
  assumes k_range: "k \<in> {2..N}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> \<le> \<eta> + C1 * h"
proof -
  have k_N: "k \<in> {1..N}" and km1_N: "k - 1 \<in> {1..N}"
    using k_range by auto
  have k_N1: "k \<in> {1..N+1}" and km1_N1: "k - 1 \<in> {1..N+1}"
    using k_range by auto
  have nodes_in: "xs ! k \<in> {a..b}" "xs ! (k - 1) \<in> {a..b}"
    using els_in_ab[OF a_lt_b N_pos h_def xs_def] k_N1 km1_N1 by auto
  have step: "xs ! k - xs ! (k - 1) = h"
    using difference_of_adj_terms[OF h_def xs_def] k_range by auto
  have hpos: "h > 0"
    using h_pos[OF a_lt_b N_pos h_def] .
  have two_node: "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
       \<le> \<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar> + C1 * h"
    unfolding C1_def
    by (rule forward_diff_one_two_node_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset k_N km1_N])
  have dist_lt: "\<bar>xs ! k - xs ! (k - 1)\<bar> < \<delta>"
    using step hpos h_lt by simp
  have cont: "\<bar>deriv f (xs ! k) - deriv f (xs ! (k - 1))\<bar> < \<eta>"
    using \<delta>_prop nodes_in dist_lt by auto
  show ?thesis
    using two_node cont by linarith
qed

text \<open>
  Folding the preamble's \<open>\<sigma>\<close>-saturation hypothesis (for the "left" direction) into
  \<open>forward_diff_one_coeff_diff_bound\<close> gives the actual per-term product bound
  \<open>forward_diff_one_I1_generic_bound\<close>'s left-hand sum needs.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_coeff_diff_saturated_left:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "h < \<delta>"
  assumes k_range: "k \<in> {2..N}"
  assumes sat: "\<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> < 1 / real N"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
       \<le> (\<eta> + C1 * h) * (1 / real N)"
proof -
  have coeff: "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> \<le> \<eta> + C1 * h"
    unfolding C1_def
    using forward_diff_one_coeff_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset \<delta>_pos
      \<delta>_prop h_lt k_range] .
  have coeff_nonneg: "0 \<le> \<eta> + C1 * h"
    using order_trans[OF abs_ge_zero coeff] .
  show ?thesis
    using mult_mono[OF coeff less_imp_le[OF sat] coeff_nonneg abs_ge_zero] .
qed

text \<open>The "right" direction analogue.\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_coeff_diff_saturated_right:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "h < \<delta>"
  assumes k_range: "k \<in> {2..N}"
  assumes sat: "\<bar>\<sigma> (w * (x - xs ! k))\<bar> < 1 / real N"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  shows "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>
       \<le> (\<eta> + C1 * h) * (1 / real N)"
proof -
  have coeff: "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> \<le> \<eta> + C1 * h"
    unfolding C1_def
    using forward_diff_one_coeff_diff_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset \<delta>_pos
      \<delta>_prop h_lt k_range] .
  have coeff_nonneg: "0 \<le> \<eta> + C1 * h"
    using order_trans[OF abs_ge_zero coeff] .
  show ?thesis
    using mult_mono[OF coeff less_imp_le[OF sat] coeff_nonneg abs_ge_zero] .
qed

text \<open>
  Full numeric \<open>I_1\<close> bound for the generic case (paper's own \<open>J_2\<close>/\<open>I_1\<close> Case 2 range,
  \<open>i\<in>{3,\<dots>,N-1}\<close> for \<open>j=1\<close>): combines \<open>forward_diff_one_I1_generic_bound\<close> (the telescoping
  identity) with \<open>forward_diff_one_coeff_diff_saturated_left\<close>/\<open>_right\<close> (the per-term product
  bounds) and the preamble's own \<open>\<sigma>\<close>-saturation hypothesis, instantiated at each summation
  index via the geometric fact that \<open>x\<close>'s distance to any node outside \<open>{i,i+1}\<close> grows by at
  least \<open>h\<close> per extra step away from the active cell -- exactly mirroring how Theorem 2.1's own
  \<open>I1_final_bound\<close> (\<open>Universal_Approximation_1d.thy\<close>) turns its saturation hypothesis into a
  numeric \<open>\<eta>\<close>-bound. Yields the same closed form \<open>\<eta>\<sqdot>(5/2+M_1)\<close> as
  \<open>forward_diff_one_J1_eta_bound\<close> -- confirming both routes (the paper's literal \<open>J_1\<close> formula,
  and the actual network-telescoping \<open>I_1\<close>) land on the same asymptotic rate, as they must.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_I1_generic_eta_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "2 * h < \<delta>"
  assumes hC1_lt_\<eta>: "h * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
  assumes N_inv_lt_\<eta>: "1 / real N < \<eta>"
  assumes sat_clause: "\<forall>k < N + 2. (\<forall>y. y - xs ! k \<ge> h
                       \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                     \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  assumes i_range: "i \<in> {3..N - 1}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N 1 w x -
          (forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))\<bar>
       < \<eta> * (5 / 2 + M1)"
proof -
  have N_pos: "N > 0" using N_gt3 by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have h_lt_delta: "h < \<delta>"
    using h_lt hpos by linarith
  have three_leq_i: "i \<ge> 3" and i_leq: "i \<le> N - 1"
    using i_range by auto

  text \<open>Node-position arithmetic: \<open>xs!m=a+(m-1)h\<close> for \<open>m\<in>{0..N+1}\<close>.\<close>
  have xs_pos: "\<And>m. m \<in> {0..N + 1} \<Longrightarrow> xs ! m = a + (real m - 1) * h"
    using xs_els[OF h_def xs_def] by auto
  have i_range01: "i \<in> {0..N + 1}" and ip1_range01: "i + 1 \<in> {0..N + 1}"
    using i_range by auto
  have xsi: "xs ! i = a + real i * h - h"
    using xs_pos[OF i_range01] by (simp add: left_diff_distrib')
  have xsip1: "xs ! (i + 1) = a + real i * h"
    using xs_pos[OF ip1_range01] by (simp add: left_diff_distrib')
  have x_lower: "x \<ge> a + real i * h - h"
    using x_in_cell xsi by simp
  have x_upper: "x \<le> a + real i * h"
    using x_in_cell xsip1 by simp

  text \<open>Left-side nodes \<open>k\<in>{2..i-1}\<close>: \<open>x-xs!k\<ge>h\<close>.\<close>
  have left_dist: "\<And>k. k \<in> {2..i - 1} \<Longrightarrow> x - xs ! k \<ge> h"
  proof -
    fix k assume k_in: "k \<in> {2..i - 1}"
    then have k_range01: "k \<in> {0..N + 1}" using i_range by auto
    have xsk: "xs ! k = a + real k * h - h"
      using xs_pos[OF k_range01] by (simp add: left_diff_distrib')
    have k_le_nat: "k + 1 \<le> i"
    proof -
      have "k + 1 \<le> (i - 1) + 1" using k_in by simp
      also have "(i - 1) + 1 = i" using three_leq_i by simp
      finally show ?thesis .
    qed
    have k_le_real: "real (k + 1) \<le> real i"
      using k_le_nat of_nat_mono by blast
    have k_le_im1: "1 \<le> real i - real k"
      using k_le_real by simp
    have "1 * h \<le> (real i - real k) * h"
      using k_le_im1 hpos by (intro mult_right_mono) auto
    then have dist_ineq: "real i * h - real k * h \<ge> h"
      by (simp add: left_diff_distrib')
    then show "x - xs ! k \<ge> h"
      using xsk x_lower by linarith
  qed

  text \<open>Right-side nodes \<open>k\<in>{i+2..N}\<close>: \<open>x-xs!k\<le>-h\<close>.\<close>
  have right_dist: "\<And>k. k \<in> {i + 2..N} \<Longrightarrow> x - xs ! k \<le> - h"
  proof -
    fix k assume k_in: "k \<in> {i + 2..N}"
    then have k_range01: "k \<in> {0..N + 1}" using i_range by auto
    have xsk: "xs ! k = a + real k * h - h"
      using xs_pos[OF k_range01] by (simp add: left_diff_distrib')
    have k_ge_nat: "i + 2 \<le> k"
      using k_in by simp
    have k_ge_real: "real (i + 2) \<le> real k"
      using k_ge_nat of_nat_mono by blast
    have k_ge: "1 \<le> real k - real i - 1"
      using k_ge_real by simp
    have "1 * h \<le> (real k - real i - 1) * h"
      using k_ge hpos by (intro mult_right_mono) auto
    then have dist_ineq: "real k * h - real i * h - h \<ge> h"
      by (simp add: left_diff_distrib' right_diff_distrib')
    then show "x - xs ! k \<le> - h"
      using xsk x_upper by linarith
  qed

  text \<open>The boundary node \<open>k=0\<close>: \<open>x-xs!0\<ge>h\<close> (in fact \<open>\<ge>3h\<close>, since \<open>i\<ge>3\<close>).\<close>
  have boundary_dist: "x - xs ! 0 \<ge> h"
  proof -
    have xs0: "xs ! 0 = a - h" using xs_pos[of 0] by simp
    have i_ge: "1 \<le> real i"
      using three_leq_i by simp
    have "1 * h \<le> real i * h"
      using i_ge hpos by (intro mult_right_mono) auto
    then have "real i * h \<ge> h" by simp
    then show ?thesis
      using xs0 x_lower by linarith
  qed

  text \<open>Instantiate the saturation clause at each index.\<close>
  have left_sat: "\<And>k. k \<in> {2..i - 1} \<Longrightarrow> \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> < 1 / real N"
    using sat_clause left_dist i_range by auto
  have right_sat: "\<And>k. k \<in> {i + 2..N} \<Longrightarrow> \<bar>\<sigma> (w * (x - xs ! k))\<bar> < 1 / real N"
    using sat_clause right_dist i_range by auto
  have boundary_sat: "\<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar> < 1 / real N"
    using sat_clause boundary_dist N_gt3 by auto

  text \<open>Per-term product bounds, summed over each range.\<close>
  have left_term_bound: "\<And>k. k \<in> {2..i - 1}
      \<Longrightarrow> \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
          \<le> (\<eta> + C1 * h) * (1 / real N)"
  proof -
    fix k assume k_in: "k \<in> {2..i - 1}"
    then have k_le_N: "k \<in> {2..N}" using i_range by auto
    show "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>
          \<le> (\<eta> + C1 * h) * (1 / real N)"
      unfolding C1_def
      using forward_diff_one_coeff_diff_saturated_left[where a = a and b = b and N = N and h = h
          and xs = xs and f = f and \<sigma> = \<sigma> and w = w and x = x and \<eta> = \<eta> and \<delta> = \<delta> and k = k,
        OF a_lt_b N_pos h_def xs_def Ck ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt_delta k_le_N
          left_sat[OF k_in]]
      by simp
  qed
  have right_term_bound: "\<And>k. k \<in> {i + 2..N}
      \<Longrightarrow> \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>
          \<le> (\<eta> + C1 * h) * (1 / real N)"
  proof -
    fix k assume k_in: "k \<in> {i + 2..N}"
    then have k_le_N: "k \<in> {2..N}" using i_range by auto
    show "\<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>
          \<le> (\<eta> + C1 * h) * (1 / real N)"
      unfolding C1_def
      using forward_diff_one_coeff_diff_saturated_right[where a = a and b = b and N = N and h = h
          and xs = xs and f = f and \<sigma> = \<sigma> and w = w and x = x and \<eta> = \<eta> and \<delta> = \<delta> and k = k,
        OF a_lt_b N_pos h_def xs_def Ck ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt_delta k_le_N
          right_sat[OF k_in]]
      by simp
  qed

  have left_sum_bound: "(\<Sum>k=2..i - 1. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
        * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>) \<le> real (i - 2) * ((\<eta> + C1 * h) * (1 / real N))"
  proof -
    have "(\<Sum>k=2..i - 1. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
          * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
        \<le> (\<Sum>k=2..i - 1. (\<eta> + C1 * h) * (1 / real N))"
      using left_term_bound by (intro sum_mono) auto
    also have "\<dots> = real (i - 2) * ((\<eta> + C1 * h) * (1 / real N))"
      by (simp add: eval_nat_numeral)
    finally show ?thesis .
  qed
  have right_sum_bound: "(\<Sum>k=i + 2..N. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
        * \<bar>\<sigma> (w * (x - xs ! k))\<bar>) \<le> real (N - i - 1) * ((\<eta> + C1 * h) * (1 / real N))"
  proof -
    have "(\<Sum>k=i + 2..N. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
          * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)
        \<le> (\<Sum>k=i + 2..N. (\<eta> + C1 * h) * (1 / real N))"
      using right_term_bound by (intro sum_mono) auto
    also have "\<dots> = real (N - i - 1) * ((\<eta> + C1 * h) * (1 / real N))"
      by (simp add: eval_nat_numeral)
    finally show ?thesis .
  qed

  text \<open>The boundary term: bounded via \<open>forward_diff_one_node_error\<close> at \<open>m=1\<close> and
    \<open>forward_diff_one_boundary_deriv_bound\<close>, exactly as in \<open>forward_diff_one_J1_eta_bound\<close>.\<close>
  have Df1_bound: "\<bar>forward_diff f xs h 1 1\<bar> \<le> M1 + (C1 / 2) * h"
  proof -
    have node: "\<bar>forward_diff f xs h 1 1 - deriv f (xs ! 1)\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def
      using forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 1] N_pos
      by simp
    have deriv_bound: "\<bar>deriv f (xs ! 1)\<bar> \<le> M1"
      unfolding M1_def
      using forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset] .
    show ?thesis using node deriv_bound by linarith
  qed
  have M1_nonneg: "M1 \<ge> 0"
    using order_trans[OF abs_ge_zero forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def
      xs_def Ck ab_subset]] unfolding M1_def by simp
  have C1_nonneg: "C1 \<ge> 0"
  proof -
    have "0 \<le> C1 * h"
      using order_trans[OF abs_ge_zero forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def
        Ck ab_subset, of 1]] N_pos
      unfolding C1_def by simp
    then show ?thesis using hpos by (simp add: zero_le_mult_iff)
  qed
  have boundary_term_bound: "\<bar>forward_diff f xs h 1 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
      \<le> (M1 + (C1 / 2) * h) * (1 / real N)"
    using mult_mono[OF Df1_bound less_imp_le[OF boundary_sat]] M1_nonneg C1_nonneg hpos
    by (simp add: mult_mono)

  text \<open>Assemble via \<open>forward_diff_one_I1_generic_bound\<close> and the three bounds above.\<close>
  have total_bound: "(\<Sum>k=2..i - 1. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
        * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
      + \<bar>forward_diff f xs h 1 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
      + (\<Sum>k=i + 2..N. \<bar>forward_diff f xs h 1 k - forward_diff f xs h 1 (k - 1)\<bar>
        * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)
    \<le> real (i - 2) * ((\<eta> + C1 * h) * (1 / real N))
      + (M1 + (C1 / 2) * h) * (1 / real N)
      + real (N - i - 1) * ((\<eta> + C1 * h) * (1 / real N))"
    using left_sum_bound right_sum_bound boundary_term_bound by linarith

  have identity_bound: "\<bar>Gj_network \<sigma> f xs h N 1 w x -
          (forward_diff f xs h 1 (i - 1)
           + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
           + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1))))\<bar>
       \<le> real (i - 2) * ((\<eta> + C1 * h) * (1 / real N))
         + (M1 + (C1 / 2) * h) * (1 / real N)
         + real (N - i - 1) * ((\<eta> + C1 * h) * (1 / real N))"
    unfolding C1_def M1_def
    using order_trans[OF forward_diff_one_I1_generic_bound[OF N_gt3 h_def xs_def i_range]
      total_bound[unfolded C1_def M1_def]] .

  text \<open>Collapse the \<open>N\<close>-scaled count \<open>((i-2)+(N-i-1))<N\<close> exactly as in
    \<open>forward_diff_one_J1_eta_bound\<close>.\<close>
  have count_lt: "real (i - 2) + real (N - i - 1) < real N"
    using three_leq_i i_leq by (simp only: of_nat_diff)
  have count_nonneg: "real (i - 2) + real (N - i - 1) \<ge> 0"
    by simp
  have hC1_lt: "h * C1 < \<eta>"
    unfolding C1_def using hC1_lt_\<eta> .
  have coeff_nonneg: "0 \<le> \<eta> + C1 * h"
    using \<eta>_pos C1_nonneg hpos by simp

  have "real (i - 2) * ((\<eta> + C1 * h) * (1 / real N))
      + (M1 + (C1 / 2) * h) * (1 / real N)
      + real (N - i - 1) * ((\<eta> + C1 * h) * (1 / real N))
    = (real (i - 2) + real (N - i - 1)) * ((\<eta> + C1 * h) / real N)
      + (M1 + (C1 / 2) * h) / real N"
    by (simp add: ring_distribs add_divide_distrib)
  also have "\<dots> < 1 * (\<eta> + C1 * h) + (M1 + (C1 / 2) * h) / real N"
  proof -
    have coeff_pos: "0 < \<eta> + C1 * h"
    proof -
      have "0 \<le> C1 * h" using C1_nonneg hpos by simp
      then show ?thesis using \<eta>_pos by linarith
    qed
    have div_pos: "0 < (\<eta> + C1 * h) / real N"
      using coeff_pos N_pos by simp
    have step_a: "(real (i - 2) + real (N - i - 1)) * ((\<eta> + C1 * h) / real N)
        < real N * ((\<eta> + C1 * h) / real N)"
      using count_lt div_pos
      by (rule mult_strict_right_mono)
    also have "\<dots> = \<eta> + C1 * h"
      using N_pos by simp
    finally have step_b: "(real (i - 2) + real (N - i - 1)) * ((\<eta> + C1 * h) / real N)
        < \<eta> + C1 * h" .
    have step_c: "(real (i - 2) + real (N - i - 1)) * ((\<eta> + C1 * h) / real N)
        + (M1 + (C1 / 2) * h) / real N
      < (\<eta> + C1 * h) + (M1 + (C1 / 2) * h) / real N"
      using step_b by (rule add_strict_right_mono)
    show ?thesis
      using step_c by simp
  qed
  also have "\<dots> = \<eta> + C1 * h + (M1 + (C1 / 2) * h) / real N"
    by simp
  also have "\<dots> < \<eta> * (5 / 2 + M1)"
  proof -
    have N_ge_1: "real N \<ge> 1"
      using N_pos by (simp add: less_eq_Suc_le)
    have split_div: "(M1 + (C1 / 2) * h) / real N = M1 / real N + ((C1 / 2) * h) / real N"
      by (simp add: add_divide_distrib)
    have M1_term: "M1 / real N \<le> \<eta> * M1"
    proof -
      have "(1 / real N) * M1 \<le> \<eta> * M1"
        using N_inv_lt_\<eta> M1_nonneg by (intro mult_right_mono) auto
      then show ?thesis by (simp add: field_simps)
    qed
    have half_term: "((C1 / 2) * h) / real N \<le> (C1 / 2) * h"
    proof -
      have "1 / real N \<le> 1" using N_ge_1 by simp
      then have "(1 / real N) * ((C1 / 2) * h) \<le> 1 * ((C1 / 2) * h)"
        using C1_nonneg hpos by (intro mult_right_mono) auto
      then show ?thesis by (simp add: field_simps)
    qed
    have half_bound: "(C1 / 2) * h < \<eta> / 2"
      using hC1_lt by (simp add: mult.commute)
    have rhs_eq: "\<eta> * (5 / 2 + M1) = \<eta> * (5 / 2) + \<eta> * M1"
      by (simp add: ring_distribs)
    show ?thesis
      unfolding rhs_eq
      using split_div M1_term half_term half_bound hC1_lt by linarith
  qed
  finally show ?thesis
    using identity_bound by linarith
qed

text \<open>
  The left-boundary (\<open>i=1,2\<close>) \<open>I_1\<close> analogue (paper's \<open>J_2\<close>/\<open>I_1\<close> Case 1). Since \<open>L_i(x)\<close> is the
  SAME fixed formula for both \<open>i=1\<close> and \<open>i=2\<close> (using indices \<open>1,2,3\<close>, not \<open>i\<close> itself --
  matching \<open>forward_diff_one_left_boundary_L_bound\<close>), the telescoping identity is simpler than
  the generic case: peeling \<open>Gj_network\<close>'s sum at its own first two active steps (\<open>m=2,3\<close>)
  cancels exactly against \<open>L_i\<close>'s two \<open>\<sigma>\<close>-steps, leaving only the tail sum \<open>{4..N}\<close> plus the
  boundary term -- no left sum at all.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_I1_left_boundary_eta_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "2 * h < \<delta>"
  assumes hC1_lt_\<eta>: "h * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
  assumes N_inv_lt_\<eta>: "1 / real N < \<eta>"
  assumes sat_clause: "\<forall>k < N + 2. (\<forall>y. y - xs ! k \<ge> h
                       \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                     \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  assumes i_range: "i \<in> {1, 2}"
  assumes x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N 1 w x -
          (forward_diff f xs h 1 1
           + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
           + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2)))\<bar>
       < \<eta> * (5 / 2 + M1)"
proof -
  have N_pos: "N > 0" using N_gt3 by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have h_lt_delta: "h < \<delta>" using h_lt hpos by linarith
  define Df where "Df = (\<lambda>k. forward_diff f xs h 1 k)"

  have i_in: "i = 1 \<or> i = 2" using i_range by auto
  have i_range01: "i \<in> {0..N+1}" and ip1_range01: "i + 1 \<in> {0..N+1}"
    using i_in N_gt3 by auto
  have xs_pos: "\<And>m. m \<in> {0..N + 1} \<Longrightarrow> xs ! m = a + (real m - 1) * h"
    using xs_els[OF h_def xs_def] by auto
  have xsi: "xs ! i \<le> xs ! 3"
    using i_in xs_pos[OF i_range01] xs_pos[of 3] N_gt3 hpos by auto
  have x_le3: "x \<le> xs ! 3"
    using x_in_cell xsi xs_pos[OF ip1_range01] xs_pos[of 3] i_in N_gt3 hpos by auto

  text \<open>Reindex \<open>Gj_network\<close>'s sum, exactly as in the generic case.\<close>
  have Gnet_eq: "Gj_network \<sigma> f xs h N 1 w x
      = (\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m))) + Df 1 * \<sigma> (w * (x - xs ! 0))"
  proof -
    have "(\<Sum>k\<in>{1..N-1}. (Df (k + 1) - Df k) * \<sigma> (w * (x - xs ! (k + 1))))
        = (\<Sum>m\<in>{2..N}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>m. m - 1" "\<lambda>k. k + 1"]) auto
    then show ?thesis
      unfolding Gj_network_def Df_def by simp
  qed

  have peel23: "(\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
      = (Df 2 - Df 1) * \<sigma> (w * (x - xs ! 2)) + (Df 3 - Df 2) * \<sigma> (w * (x - xs ! 3))
        + (\<Sum>m=4..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
  proof -
    have s1: "(\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        = (Df 2 - Df 1) * \<sigma> (w * (x - xs ! 2))
          + (\<Sum>m=3..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      using N_gt3 by (subst sum.atLeast_Suc_atMost) (auto simp add: eval_nat_numeral)
    have s2: "(\<Sum>m=3..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        = (Df 3 - Df 2) * \<sigma> (w * (x - xs ! 3))
          + (\<Sum>m=4..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      using N_gt3 by (subst sum.atLeast_Suc_atMost) (auto simp add: eval_nat_numeral)
    from s1 s2 show ?thesis by simp
  qed

  have identity: "Gj_network \<sigma> f xs h N 1 w x -
      (Df 1 + (Df 3 - Df 2) * \<sigma> (w * (x - xs ! 3)) + (Df 2 - Df 1) * \<sigma> (w * (x - xs ! 2)))
    = (\<Sum>m=4..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m))) + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
    unfolding Gnet_eq peel23 by (simp add: right_diff_distrib' left_diff_distrib')

  have abs_bound: "\<bar>(\<Sum>m=4..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>
    \<le> (\<Sum>m=4..N. \<bar>Df m - Df (m - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! m))\<bar>)
      + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
  proof -
    have t1: "\<bar>(\<Sum>m=4..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))\<bar>
        \<le> (\<Sum>m=4..N. \<bar>Df m - Df (m - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! m))\<bar>)"
      by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
    have t2: "\<bar>Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar> = \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
      by (simp add: abs_mult)
    show ?thesis using t1 t2 abs_triangle_ineq by linarith
  qed

  text \<open>Geometric distance facts and saturation instantiation.\<close>
  have right_dist: "\<And>k. k \<in> {4..N} \<Longrightarrow> x - xs ! k \<le> - h"
  proof -
    fix k assume k_in: "k \<in> {4..N}"
    then have k_range01: "k \<in> {0..N + 1}" using N_gt3 by auto
    have xsk: "xs ! k = a + real k * h - h"
      using xs_pos[OF k_range01] by (simp add: left_diff_distrib')
    have xs3: "xs ! 3 = a + 3 * h - h"
      using xs_pos[of 3] N_gt3 by (simp add: left_diff_distrib')
    have k_ge_nat: "4 \<le> k" using k_in by simp
    have k_ge_real: "real 4 \<le> real k" using k_ge_nat of_nat_mono by blast
    have "1 * h \<le> (real k - 3) * h"
      using k_ge_real hpos by (intro mult_right_mono) auto
    then have "real k * h - real 3 * h \<ge> h"
      by (simp add: left_diff_distrib')
    then show "x - xs ! k \<le> - h"
      using xsk xs3 x_le3 by simp
  qed
  have boundary_dist: "x - xs ! 0 \<ge> h"
  proof -
    have xs0: "xs ! 0 = a - h" using xs_pos[of 0] by simp
    have xsi_eq: "xs ! i = a + real i * h - h" using xs_pos[OF i_range01] by (simp add: left_diff_distrib')
    have x_ge: "x \<ge> a + real i * h - h"
      using x_in_cell xsi_eq by simp
    have i_ge_1: "real i \<ge> 1" using i_in by auto
    have "1 * h \<le> real i * h" using i_ge_1 hpos by (intro mult_right_mono) auto
    then have ih_ge: "real i * h \<ge> h" by simp
    show ?thesis using xs0 x_ge ih_ge by linarith
  qed
  have right_sat: "\<And>k. k \<in> {4..N} \<Longrightarrow> \<bar>\<sigma> (w * (x - xs ! k))\<bar> < 1 / real N"
    using sat_clause right_dist N_gt3 by auto
  have boundary_sat: "\<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar> < 1 / real N"
    using sat_clause boundary_dist N_gt3 by auto

  have C1_nonneg: "C1 \<ge> 0"
  proof -
    have "0 \<le> C1 * h"
      using order_trans[OF abs_ge_zero forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def
        Ck ab_subset, of 1]] N_pos
      unfolding C1_def by simp
    then show ?thesis using hpos by (simp add: zero_le_mult_iff)
  qed

  have right_term_bound: "\<And>k. k \<in> {4..N}
      \<Longrightarrow> \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar> \<le> (\<eta> + C1 * h) * (1 / real N)"
  proof -
    fix k assume k_in: "k \<in> {4..N}"
    then have k_le_N: "k \<in> {2..N}" by auto
    show "\<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar> \<le> (\<eta> + C1 * h) * (1 / real N)"
      unfolding Df_def C1_def
      using forward_diff_one_coeff_diff_saturated_right[where a = a and b = b and N = N and h = h
          and xs = xs and f = f and \<sigma> = \<sigma> and w = w and x = x and \<eta> = \<eta> and \<delta> = \<delta> and k = k,
        OF a_lt_b N_pos h_def xs_def Ck ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt_delta k_le_N
          right_sat[OF k_in]]
      by simp
  qed
  have right_sum_bound: "(\<Sum>k=4..N. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)
      \<le> real (N - 3) * ((\<eta> + C1 * h) * (1 / real N))"
  proof -
    have "(\<Sum>k=4..N. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)
        \<le> (\<Sum>k=4..N. (\<eta> + C1 * h) * (1 / real N))"
      using right_term_bound by (intro sum_mono) auto
    also have "\<dots> = real (N - 3) * ((\<eta> + C1 * h) * (1 / real N))"
      by (simp add: eval_nat_numeral)
    finally show ?thesis .
  qed

  have Df1_bound: "\<bar>Df 1\<bar> \<le> M1 + (C1 / 2) * h"
  proof -
    have node: "\<bar>Df 1 - deriv f (xs ! 1)\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def Df_def
      using forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 1] N_pos
      by simp
    have deriv_bound: "\<bar>deriv f (xs ! 1)\<bar> \<le> M1"
      unfolding M1_def
      using forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset] .
    show ?thesis using node deriv_bound by linarith
  qed
  have M1_nonneg: "M1 \<ge> 0"
    using order_trans[OF abs_ge_zero forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def
      xs_def Ck ab_subset]] unfolding M1_def by simp
  have boundary_term_bound: "\<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
      \<le> (M1 + (C1 / 2) * h) * (1 / real N)"
    using mult_mono[OF Df1_bound less_imp_le[OF boundary_sat]] M1_nonneg C1_nonneg hpos
    by (simp add: mult_mono)

  have total_bound: "(\<Sum>k=4..N. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k))\<bar>)
      + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
    \<le> real (N - 3) * ((\<eta> + C1 * h) * (1 / real N))
      + (M1 + (C1 / 2) * h) * (1 / real N)"
    using right_sum_bound boundary_term_bound by linarith

  have identity_bound: "\<bar>Gj_network \<sigma> f xs h N 1 w x -
      (forward_diff f xs h 1 1 + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2)
         * \<sigma> (w * (x - xs ! 3)) + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1)
         * \<sigma> (w * (x - xs ! 2)))\<bar>
      \<le> real (N - 3) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)"
  proof -
    have "\<bar>Gj_network \<sigma> f xs h N 1 w x -
        (Df 1 + (Df 3 - Df 2) * \<sigma> (w * (x - xs ! 3)) + (Df 2 - Df 1) * \<sigma> (w * (x - xs ! 2)))\<bar>
        = \<bar>(\<Sum>m=4..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
           + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>"
      using identity by simp
    also have "\<dots> \<le> (\<Sum>m=4..N. \<bar>Df m - Df (m - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! m))\<bar>)
        + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
      using abs_bound .
    also have "\<dots> \<le> real (N - 3) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)"
      using total_bound .
    finally show ?thesis
      unfolding Df_def .
  qed

  have count_lt: "real (N - 3) < real N"
    using N_gt3 by simp
  have hC1_lt: "h * C1 < \<eta>" unfolding C1_def using hC1_lt_\<eta> .
  have coeff_pos: "0 < \<eta> + C1 * h"
  proof -
    have "0 \<le> C1 * h" using C1_nonneg hpos by simp
    then show ?thesis using \<eta>_pos by linarith
  qed
  have div_pos: "0 < (\<eta> + C1 * h) / real N" using coeff_pos N_pos by simp
  have step_a: "real (N - 3) * ((\<eta> + C1 * h) / real N) < real N * ((\<eta> + C1 * h) / real N)"
    using count_lt div_pos by (rule mult_strict_right_mono)
  have step_b: "real (N - 3) * ((\<eta> + C1 * h) / real N) < \<eta> + C1 * h"
    using step_a N_pos by simp
  have step_c: "real (N - 3) * ((\<eta> + C1 * h) / real N) + (M1 + (C1 / 2) * h) / real N
      < (\<eta> + C1 * h) + (M1 + (C1 / 2) * h) / real N"
    using step_b by (rule add_strict_right_mono)

  have split_div: "(M1 + (C1 / 2) * h) / real N = M1 / real N + ((C1 / 2) * h) / real N"
    by (simp add: add_divide_distrib)
  have N_ge_1: "real N \<ge> 1" using N_pos by (simp add: less_eq_Suc_le)
  have M1_term: "M1 / real N \<le> \<eta> * M1"
  proof -
    have "(1 / real N) * M1 \<le> \<eta> * M1"
      using N_inv_lt_\<eta> M1_nonneg by (intro mult_right_mono) auto
    then show ?thesis by (simp add: field_simps)
  qed
  have half_term: "((C1 / 2) * h) / real N \<le> (C1 / 2) * h"
  proof -
    have "1 / real N \<le> 1" using N_ge_1 by simp
    then have "(1 / real N) * ((C1 / 2) * h) \<le> 1 * ((C1 / 2) * h)"
      using C1_nonneg hpos by (intro mult_right_mono) auto
    then show ?thesis by (simp add: field_simps)
  qed
  have half_bound: "(C1 / 2) * h < \<eta> / 2"
    using hC1_lt by (simp add: mult.commute)
  have rhs_eq: "\<eta> * (5 / 2 + M1) = \<eta> * (5 / 2) + \<eta> * M1"
    by (simp add: ring_distribs)

  have final_bound: "real (N - 3) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)
      < \<eta> * (5 / 2 + M1)"
  proof -
    have "real (N - 3) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)
        = real (N - 3) * ((\<eta> + C1 * h) / real N) + (M1 / real N + ((C1 / 2) * h) / real N)"
      using split_div by simp
    also have "\<dots> < (\<eta> + C1 * h) + (M1 / real N + ((C1 / 2) * h) / real N)"
      using step_b by linarith
    also have "\<dots> \<le> (\<eta> + C1 * h) + (\<eta> * M1 + (C1 / 2) * h)"
      using M1_term half_term by linarith
    also have "\<dots> < \<eta> * (5 / 2) + \<eta> * M1"
      using hC1_lt half_bound by linarith
    also have "\<dots> = \<eta> * (5 / 2 + M1)"
      using rhs_eq by simp
    finally show ?thesis .
  qed

  show ?thesis
    using identity_bound final_bound by linarith
qed

text \<open>
  The right-boundary (\<open>i=N\<close>) \<open>I_1\<close> analogue (paper's \<open>J_2\<close>/\<open>I_1\<close> Case 3, the mirror image of
  the left-boundary case just proved): peeling \<open>Gj_network\<close>'s LAST active step (\<open>m=N\<close>) and
  using the SAME telescoping trick as the generic case (with \<open>i-1\<close> replaced by \<open>N-1\<close>) gives an
  identity with a left sum \<open>{2..N-1}\<close> plus the boundary term, no right sum -- matching
  \<open>forward_diff_one_right_boundary_L_bound\<close>'s single active \<open>\<sigma>\<close>-step.
\<close>
(* Auxiliary for Theorem 4.1, first-derivative case; not separately numbered. *)
lemma forward_diff_one_I1_right_boundary_eta_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes f :: "real \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_gt3: "N > 3"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes Ck: "C_k_on 2 f U" and ab_subset: "{a..b} \<subseteq> U"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
  assumes h_lt: "2 * h < \<delta>"
  assumes hC1_lt_\<eta>: "h * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
  assumes N_inv_lt_\<eta>: "1 / real N < \<eta>"
  assumes sat_clause: "\<forall>k < N + 2. (\<forall>y. y - xs ! k \<ge> h
                       \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k)) - 1\<bar> < 1 / real N)
                     \<and> (\<forall>y. y - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (y - xs ! k))\<bar> < 1 / real N)"
  assumes x_in_cell: "x \<in> {xs ! N .. xs ! (N + 1)}"
  defines "C1 \<equiv> Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b})"
  defines "M1 \<equiv> Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  shows "\<bar>Gj_network \<sigma> f xs h N 1 w x -
          (forward_diff f xs h 1 (N - 1)
           + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N)))\<bar>
       < \<eta> * (5 / 2 + M1)"
proof -
  have N_pos: "N > 0" using N_gt3 by simp
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have h_lt_delta: "h < \<delta>" using h_lt hpos by linarith
  define Df where "Df = (\<lambda>k. forward_diff f xs h 1 k)"

  have xs_pos: "\<And>m. m \<in> {0..N + 1} \<Longrightarrow> xs ! m = a + (real m - 1) * h"
    using xs_els[OF h_def xs_def] by auto
  have N_range01: "N \<in> {0..N + 1}" using N_gt3 by auto
  have xsN: "xs ! N = a + real N * h - h"
    using xs_pos[OF N_range01] by (simp add: left_diff_distrib')
  have x_ge: "x \<ge> a + real N * h - h"
    using x_in_cell xsN by simp

  text \<open>Reindex \<open>Gj_network\<close>'s sum, exactly as before.\<close>
  have Gnet_eq: "Gj_network \<sigma> f xs h N 1 w x
      = (\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m))) + Df 1 * \<sigma> (w * (x - xs ! 0))"
  proof -
    have "(\<Sum>k\<in>{1..N-1}. (Df (k + 1) - Df k) * \<sigma> (w * (x - xs ! (k + 1))))
        = (\<Sum>m\<in>{2..N}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>m. m - 1" "\<lambda>k. k + 1"]) auto
    then show ?thesis
      unfolding Gj_network_def Df_def by simp
  qed

  have peelN: "(\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
      = (\<Sum>m=2..N-1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        + (Df N - Df (N - 1)) * \<sigma> (w * (x - xs ! N))"
  proof -
    have set_eq: "insert N {2..N-1} = {2..N}"
      using N_gt3 by auto
    have not_in: "N \<notin> {2..N-1}"
      by auto
    have "(\<Sum>m=2..N. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))
        = (\<Sum>m\<in>insert N {2..N-1}. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      using set_eq by simp
    also have "\<dots> = (Df N - Df (N - 1)) * \<sigma> (w * (x - xs ! N))
        + (\<Sum>m=2..N-1. (Df m - Df (m - 1)) * \<sigma> (w * (x - xs ! m)))"
      using not_in by (subst sum.insert) auto
    finally show ?thesis by simp
  qed

  text \<open>Telescoping: raw sum from \<open>2\<close> to \<open>N-1\<close>, plus \<open>Df 1\<close>, collapses to \<open>Df(N-1)\<close>.\<close>
  have telescope_shift: "(\<Sum>k=2..N - 1. Df k - Df (k - 1)) + Df 1 = Df (N - 1)"
  proof -
    have full: "(\<Sum>k=1..N - 1. Df k - Df (k - 1)) + Df 0 = Df (N - 1)"
      unfolding Df_def using forward_diff_telescope[of f xs h 1 "N - 1"] .
    have split: "(\<Sum>k=1..N - 1. Df k - Df (k - 1))
        = (Df 1 - Df 0) + (\<Sum>k=2..N - 1. Df k - Df (k - 1))"
      using N_gt3 by (subst sum.atLeast_Suc_atMost) (auto simp add: eval_nat_numeral)
    from full split show ?thesis by linarith
  qed

  have identity: "Gj_network \<sigma> f xs h N 1 w x -
      (Df (N - 1) + (Df N - Df (N - 1)) * \<sigma> (w * (x - xs ! N)))
    = (\<Sum>k=2..N - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)"
    unfolding Gnet_eq peelN telescope_shift[symmetric]
    by (simp add: sum_subtractf right_diff_distrib' left_diff_distrib')

  have abs_bound: "\<bar>(\<Sum>k=2..N - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
      + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>
    \<le> (\<Sum>k=2..N - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
      + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
  proof -
    have t1: "\<bar>(\<Sum>k=2..N - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))\<bar>
        \<le> (\<Sum>k=2..N - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)"
      by (rule order_trans[OF sum_abs]) (simp add: abs_mult)
    have t2: "\<bar>Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar> = \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
      by (simp add: abs_mult)
    show ?thesis using t1 t2 abs_triangle_ineq by linarith
  qed

  text \<open>Geometric distance facts and saturation instantiation.\<close>
  have left_dist: "\<And>k. k \<in> {2..N - 1} \<Longrightarrow> x - xs ! k \<ge> h"
  proof -
    fix k assume k_in: "k \<in> {2..N - 1}"
    then have k_range01: "k \<in> {0..N + 1}" using N_gt3 by auto
    have xsk: "xs ! k = a + real k * h - h"
      using xs_pos[OF k_range01] by (simp add: left_diff_distrib')
    have k_le_nat: "k \<le> N - 1" using k_in by simp
    have k_le_real: "real k \<le> real (N - 1)" using k_le_nat of_nat_mono by blast
    have Nm1_eq: "real (N - 1) = real N - 1" using N_gt3 by (simp only: of_nat_diff)
    have "1 * h \<le> (real N - real k) * h"
      using k_le_real Nm1_eq hpos by (intro mult_right_mono) auto
    then have "real N * h - real k * h \<ge> h"
      by (simp add: left_diff_distrib')
    then show "x - xs ! k \<ge> h"
      using xsk x_ge by simp
  qed
  have boundary_dist: "x - xs ! 0 \<ge> h"
  proof -
    have xs0: "xs ! 0 = a - h" using xs_pos[of 0] by simp
    have N_ge_1: "real N \<ge> 1" using N_pos by (simp add: less_eq_Suc_le)
    have "1 * h \<le> real N * h" using N_ge_1 hpos by (intro mult_right_mono) auto
    then have Nh_ge: "real N * h \<ge> h" by simp
    show ?thesis using xs0 x_ge Nh_ge by linarith
  qed
  have left_sat: "\<And>k. k \<in> {2..N - 1} \<Longrightarrow> \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> < 1 / real N"
    using sat_clause left_dist N_gt3 by auto
  have boundary_sat: "\<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar> < 1 / real N"
    using sat_clause boundary_dist N_gt3 by auto

  have C1_nonneg: "C1 \<ge> 0"
  proof -
    have "0 \<le> C1 * h"
      using order_trans[OF abs_ge_zero forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def
        Ck ab_subset, of 1]] N_pos
      unfolding C1_def by simp
    then show ?thesis using hpos by (simp add: zero_le_mult_iff)
  qed

  have left_term_bound: "\<And>k. k \<in> {2..N - 1}
      \<Longrightarrow> \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> \<le> (\<eta> + C1 * h) * (1 / real N)"
  proof -
    fix k assume k_in: "k \<in> {2..N - 1}"
    then have k_le_N: "k \<in> {2..N}" by auto
    show "\<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> \<le> (\<eta> + C1 * h) * (1 / real N)"
      unfolding Df_def C1_def
      using forward_diff_one_coeff_diff_saturated_left[where a = a and b = b and N = N and h = h
          and xs = xs and f = f and \<sigma> = \<sigma> and w = w and x = x and \<eta> = \<eta> and \<delta> = \<delta> and k = k,
        OF a_lt_b N_pos h_def xs_def Ck ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt_delta k_le_N
          left_sat[OF k_in]]
      by simp
  qed
  have left_sum_bound: "(\<Sum>k=2..N - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
      \<le> real (N - 2) * ((\<eta> + C1 * h) * (1 / real N))"
  proof -
    have "(\<Sum>k=2..N - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
        \<le> (\<Sum>k=2..N - 1. (\<eta> + C1 * h) * (1 / real N))"
      using left_term_bound by (intro sum_mono) auto
    also have "\<dots> = real (N - 2) * ((\<eta> + C1 * h) * (1 / real N))"
      by (simp add: eval_nat_numeral)
    finally show ?thesis .
  qed

  have Df1_bound: "\<bar>Df 1\<bar> \<le> M1 + (C1 / 2) * h"
  proof -
    have node: "\<bar>Df 1 - deriv f (xs ! 1)\<bar> \<le> (C1 / 2) * h"
      unfolding C1_def Df_def
      using forward_diff_one_node_error[OF a_lt_b N_pos h_def xs_def Ck ab_subset, of 1] N_pos
      by simp
    have deriv_bound: "\<bar>deriv f (xs ! 1)\<bar> \<le> M1"
      unfolding M1_def
      using forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset] .
    show ?thesis using node deriv_bound by linarith
  qed
  have M1_nonneg: "M1 \<ge> 0"
    using order_trans[OF abs_ge_zero forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def
      xs_def Ck ab_subset]] unfolding M1_def by simp
  have boundary_term_bound: "\<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
      \<le> (M1 + (C1 / 2) * h) * (1 / real N)"
    using mult_mono[OF Df1_bound less_imp_le[OF boundary_sat]] M1_nonneg C1_nonneg hpos
    by (simp add: mult_mono)

  have total_bound: "(\<Sum>k=2..N - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
      + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>
    \<le> real (N - 2) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)"
    using left_sum_bound boundary_term_bound by linarith

  have identity_bound: "\<bar>Gj_network \<sigma> f xs h N 1 w x -
      (forward_diff f xs h 1 (N - 1)
       + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N)))\<bar>
      \<le> real (N - 2) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)"
  proof -
    have "\<bar>Gj_network \<sigma> f xs h N 1 w x -
        (Df (N - 1) + (Df N - Df (N - 1)) * \<sigma> (w * (x - xs ! N)))\<bar>
        = \<bar>(\<Sum>k=2..N - 1. (Df k - Df (k - 1)) * (\<sigma> (w * (x - xs ! k)) - 1))
           + Df 1 * (\<sigma> (w * (x - xs ! 0)) - 1)\<bar>"
      using identity by simp
    also have "\<dots> \<le> (\<Sum>k=2..N - 1. \<bar>Df k - Df (k - 1)\<bar> * \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar>)
        + \<bar>Df 1\<bar> * \<bar>\<sigma> (w * (x - xs ! 0)) - 1\<bar>"
      using abs_bound .
    also have "\<dots> \<le> real (N - 2) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)"
      using total_bound .
    finally show ?thesis
      unfolding Df_def .
  qed

  have count_lt: "real (N - 2) < real N"
    using N_gt3 by simp
  have hC1_lt: "h * C1 < \<eta>" unfolding C1_def using hC1_lt_\<eta> .
  have coeff_pos: "0 < \<eta> + C1 * h"
  proof -
    have "0 \<le> C1 * h" using C1_nonneg hpos by simp
    then show ?thesis using \<eta>_pos by linarith
  qed
  have div_pos: "0 < (\<eta> + C1 * h) / real N" using coeff_pos N_pos by simp
  have step_a: "real (N - 2) * ((\<eta> + C1 * h) / real N) < real N * ((\<eta> + C1 * h) / real N)"
    using count_lt div_pos by (rule mult_strict_right_mono)
  have step_b: "real (N - 2) * ((\<eta> + C1 * h) / real N) < \<eta> + C1 * h"
    using step_a N_pos by simp

  have split_div: "(M1 + (C1 / 2) * h) / real N = M1 / real N + ((C1 / 2) * h) / real N"
    by (simp add: add_divide_distrib)
  have N_ge_1: "real N \<ge> 1" using N_pos by (simp add: less_eq_Suc_le)
  have M1_term: "M1 / real N \<le> \<eta> * M1"
  proof -
    have "(1 / real N) * M1 \<le> \<eta> * M1"
      using N_inv_lt_\<eta> M1_nonneg by (intro mult_right_mono) auto
    then show ?thesis by (simp add: field_simps)
  qed
  have half_term: "((C1 / 2) * h) / real N \<le> (C1 / 2) * h"
  proof -
    have "1 / real N \<le> 1" using N_ge_1 by simp
    then have "(1 / real N) * ((C1 / 2) * h) \<le> 1 * ((C1 / 2) * h)"
      using C1_nonneg hpos by (intro mult_right_mono) auto
    then show ?thesis by (simp add: field_simps)
  qed
  have half_bound: "(C1 / 2) * h < \<eta> / 2"
    using hC1_lt by (simp add: mult.commute)
  have rhs_eq: "\<eta> * (5 / 2 + M1) = \<eta> * (5 / 2) + \<eta> * M1"
    by (simp add: ring_distribs)

  have final_bound: "real (N - 2) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)
      < \<eta> * (5 / 2 + M1)"
  proof -
    have "real (N - 2) * ((\<eta> + C1 * h) * (1 / real N)) + (M1 + (C1 / 2) * h) * (1 / real N)
        = real (N - 2) * ((\<eta> + C1 * h) / real N) + (M1 / real N + ((C1 / 2) * h) / real N)"
      using split_div by simp
    also have "\<dots> < (\<eta> + C1 * h) + (M1 / real N + ((C1 / 2) * h) / real N)"
      using step_b by linarith
    also have "\<dots> \<le> (\<eta> + C1 * h) + (\<eta> * M1 + (C1 / 2) * h)"
      using M1_term half_term by linarith
    also have "\<dots> < \<eta> * (5 / 2) + \<eta> * M1"
      using hC1_lt half_bound by linarith
    also have "\<dots> = \<eta> * (5 / 2 + M1)"
      using rhs_eq by simp
    finally show ?thesis .
  qed

  show ?thesis
    using identity_bound final_bound by linarith
qed

text \<open>
  Theorem 4.1 (Simultaneous approximation of \<open>f\<close> and its derivative, \<open>j=1\<close> case), p.176: the
  final case-dispatch assembly, combining every piece built above. For each \<open>x\<in>[a,b]\<close>,
  \<open>exists_containing_interval\<close> locates the active cell \<open>i\<in>{1,...,N}\<close>; the three cases
  \<open>i\<in>{1,2}\<close>/\<open>i\<in>{3,...,N-1}\<close>/\<open>i=N\<close> exhaust \<open>{1,...,N}\<close> (using \<open>N>3\<close>) and dispatch to the matching
  \<open>L_i\<close>/\<open>J_2\<close>/\<open>I_1\<close> lemma triple; \<open>|(G_N^1f)(x)-f'(x)|\<le>|(G_N^1f)(x)-L_i(x)|+|L_i(x)-f'(x)|=I_1+J_2\<close>
  (triangle inequality), and the preamble's own \<open>\<eta>\<close> (denominator \<open>4+M_1+4S\<close>, chosen exactly to
  make this close) collapses \<open>I_1+J_2<\<eta>(4+M_1+4S)=\<epsilon>\<close> in every case.
\<close>
(* Theorem 4.1: first-derivative specialization. *)
theorem forward_diff_one_approximation:
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes Ck: "C_k_on 2 f U"
  assumes ab_subset: "{a..b} \<subseteq> U"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>N w. N > 3 \<and> w > 0 \<and>
           (\<forall>x \<in> {a..b}. \<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N 1 w x
                          - deriv f x\<bar> < \<epsilon>)"
proof -
  obtain N w \<eta> \<delta> where N_gt3: "N > 3" and w_pos: "w > 0" and \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
    and \<delta>_prop: "\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f y\<bar> < \<eta>"
    and N\<delta>: "real N * \<delta> > 2 * (b - a)" and N_inv_lt_\<eta>: "1 / real N < \<eta>"
    and hC1_lt_\<eta>: "(b - a) / real N * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
    and eps_bound: "\<eta> * (4 + Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b}) + 4 * Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) \<le> \<epsilon>"
    and sat_clause: "\<forall>k < N + 2. (\<forall>x. x - unif_part a b N ! k \<ge> (b - a) / real N
                          \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k)) - 1\<bar> < 1 / real N)
                       \<and> (\<forall>x. x - unif_part a b N ! k \<le> - ((b - a) / real N)
                          \<longrightarrow> \<bar>\<sigma> (w * (x - unif_part a b N ! k))\<bar> < 1 / real N)"
    using forward_diff_one_approximation_preamble[OF sigmoidal_function bounded_sigmoidal a_lt_b
      Ck ab_subset eps_pos]
    by blast

  define h where h_def: "h = (b - a) / real N"
  define xs where xs_def: "xs = unif_part a b N"
  have N_pos: "N > 0" using N_gt3 by simp
  have h_lt: "2 * h < \<delta>"
  proof -
    have "2 * (b - a) < real N * \<delta>" using N\<delta> by linarith
    then have "2 * (b - a) / real N < \<delta>" using N_pos by (simp add: divide_less_eq mult.commute)
    then show ?thesis unfolding h_def by (simp add: field_simps)
  qed
  have hC1_lt_\<eta>': "h * Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) < \<eta>"
    unfolding h_def using hC1_lt_\<eta> .
  have sat_clause': "\<forall>k < N + 2. (\<forall>x. x - xs ! k \<ge> h
                        \<longrightarrow> \<bar>\<sigma> (w * (x - xs ! k)) - 1\<bar> < 1 / real N)
                     \<and> (\<forall>x. x - xs ! k \<le> - h \<longrightarrow> \<bar>\<sigma> (w * (x - xs ! k))\<bar> < 1 / real N)"
    unfolding h_def xs_def using sat_clause .

  define M1 where M1_def: "M1 = Sup ((\<lambda>t. \<bar>deriv f t\<bar>) ` {a..b})"
  define S where S_def: "S = Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  have S_nonneg: "S \<ge> 0"
    using bounded_sigmoidal unfolding bounded_function_def S_def
    by (meson UNIV_I abs_ge_zero cSUP_upper2)
  have M1_nonneg: "M1 \<ge> 0"
  proof -
    have "0 \<le> \<bar>deriv f (xs ! 1)\<bar>" by simp
    also have "\<dots> \<le> M1"
      unfolding M1_def
      using forward_diff_one_boundary_deriv_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset] .
    finally show ?thesis .
  qed
  have eps_bound': "\<eta> * (4 + M1 + 4 * S) \<le> \<epsilon>"
    unfolding M1_def S_def using eps_bound .

  show ?thesis
  proof (intro exI[where x = N] exI[where x = w] conjI ballI)
    show "N > 3" using N_gt3 .
    show "w > 0" using w_pos .
  next
    fix x assume x_in_ab: "x \<in> {a..b}"
    obtain i where i_range: "i \<in> {1..N}" and x_in_cell: "x \<in> {xs ! i .. xs ! (i + 1)}"
      using exists_containing_interval[OF a_lt_b N_pos h_def xs_def x_in_ab] by blast

    have goal: "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar> < \<epsilon>"
    proof (cases "i < 3")
      case True
      then have i_in: "i \<in> {1, 2}" using i_range by auto
      define Li where "Li = forward_diff f xs h 1 1
          + (forward_diff f xs h 1 3 - forward_diff f xs h 1 2) * \<sigma> (w * (x - xs ! 3))
          + (forward_diff f xs h 1 2 - forward_diff f xs h 1 1) * \<sigma> (w * (x - xs ! 2))"
      have J2: "\<bar>Li - deriv f x\<bar> \<le> \<eta> * (1 + 2 * S) + Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h
                    * (1 / 2 + 2 * S)"
        unfolding Li_def S_def
        using forward_diff_one_left_boundary_L_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
          bounded_sigmoidal \<eta>_pos \<delta>_pos \<delta>_prop h_lt i_in x_in_cell] .
      have I1: "\<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> < \<eta> * (5 / 2 + M1)"
        unfolding Li_def M1_def
        using forward_diff_one_I1_left_boundary_eta_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
          \<eta>_pos \<delta>_pos \<delta>_prop h_lt hC1_lt_\<eta>' N_inv_lt_\<eta> sat_clause' i_in x_in_cell] .
      have C1h_bound: "Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + 2 * S) < \<eta> * (1 / 2 + 2 * S)"
      proof -
        have "0 < 1 / 2 + 2 * S" using S_nonneg by simp
        then show ?thesis
          using mult_strict_right_mono[OF hC1_lt_\<eta>'] by (simp add: mult.commute)
      qed
      have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
          = \<bar>(Gj_network \<sigma> f xs h N 1 w x - Li) + (Li - deriv f x)\<bar>"
        by simp
      also have "\<dots> \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>"
        by (rule abs_triangle_ineq)
      finally have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
          \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>" .
      also have "\<dots> < \<eta> * (5 / 2 + M1) + (\<eta> * (1 + 2 * S) + \<eta> * (1 / 2 + 2 * S))"
        using I1 J2 C1h_bound by linarith
      also have "\<dots> = \<eta> * (4 + M1 + 4 * S)"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> \<epsilon>" using eps_bound' by simp
      finally show ?thesis .
    next
      case False
      then show ?thesis
      proof (cases "i = N")
        case True
        define Li where "Li = forward_diff f xs h 1 (N - 1)
            + (forward_diff f xs h 1 N - forward_diff f xs h 1 (N - 1)) * \<sigma> (w * (x - xs ! N))"
        have x_in_cellN: "x \<in> {xs ! N .. xs ! (N + 1)}" using x_in_cell True by simp
        have J2: "\<bar>Li - deriv f x\<bar> \<le> \<eta> * (1 + S) + Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h
                      * (1 / 2 + S)"
          unfolding Li_def S_def
          using forward_diff_one_right_boundary_L_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
            bounded_sigmoidal \<eta>_pos \<delta>_pos \<delta>_prop h_lt x_in_cellN] .
        have I1: "\<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> < \<eta> * (5 / 2 + M1)"
          unfolding Li_def M1_def
          using forward_diff_one_I1_right_boundary_eta_bound[OF a_lt_b N_gt3 h_def xs_def Ck
            ab_subset \<eta>_pos \<delta>_pos \<delta>_prop h_lt hC1_lt_\<eta>' N_inv_lt_\<eta> sat_clause' x_in_cellN] .
        have C1h_bound: "Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + S) < \<eta> * (1 / 2 + S)"
        proof -
          have "0 < 1 / 2 + S" using S_nonneg by simp
          then show ?thesis
            using mult_strict_right_mono[OF hC1_lt_\<eta>'] by (simp add: mult.commute)
        qed
        have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
            = \<bar>(Gj_network \<sigma> f xs h N 1 w x - Li) + (Li - deriv f x)\<bar>"
          by simp
        also have "\<dots> \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>"
          by (rule abs_triangle_ineq)
        finally have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
            \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>" .
        also have "\<dots> < \<eta> * (5 / 2 + M1) + (\<eta> * (1 + S) + \<eta> * (1 / 2 + S))"
          using I1 J2 C1h_bound by linarith
        also have "\<dots> \<le> \<eta> * (4 + M1 + 4 * S)"
          using S_nonneg \<eta>_pos by (simp add: algebra_simps)
        also have "\<dots> \<le> \<epsilon>" using eps_bound' by simp
        finally show ?thesis .
      next
        case False
        then have i_in: "i \<in> {3..N - 1}" using i_range \<open>\<not> i < 3\<close> by auto
        have i_in2: "i \<in> {2..N - 1}" using i_in by auto
        define Li where "Li = forward_diff f xs h 1 (i - 1)
            + (forward_diff f xs h 1 i - forward_diff f xs h 1 (i - 1)) * \<sigma> (w * (x - xs ! i))
            + (forward_diff f xs h 1 (i + 1) - forward_diff f xs h 1 i) * \<sigma> (w * (x - xs ! (i + 1)))"
        have J2: "\<bar>Li - deriv f x\<bar> \<le> \<eta> * (1 + 2 * S) + Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h
                      * (1 / 2 + 2 * S)"
          unfolding Li_def S_def
          using forward_diff_one_generic_L_bound[OF a_lt_b N_pos h_def xs_def Ck ab_subset
            bounded_sigmoidal \<eta>_pos \<delta>_pos \<delta>_prop h_lt i_in2 x_in_cell] .
        have I1: "\<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> < \<eta> * (5 / 2 + M1)"
          unfolding Li_def M1_def
          using forward_diff_one_I1_generic_eta_bound[OF a_lt_b N_gt3 h_def xs_def Ck ab_subset
            \<eta>_pos \<delta>_pos \<delta>_prop h_lt hC1_lt_\<eta>' N_inv_lt_\<eta> sat_clause' i_in x_in_cell] .
        have C1h_bound: "Sup ((\<lambda>t. \<bar>(deriv ^^ 2) f t\<bar>) ` {a..b}) * h * (1 / 2 + 2 * S) < \<eta> * (1 / 2 + 2 * S)"
        proof -
          have "0 < 1 / 2 + 2 * S" using S_nonneg by simp
          then show ?thesis
            using mult_strict_right_mono[OF hC1_lt_\<eta>'] by (simp add: mult.commute)
        qed
        have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
            = \<bar>(Gj_network \<sigma> f xs h N 1 w x - Li) + (Li - deriv f x)\<bar>"
          by simp
        also have "\<dots> \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>"
          by (rule abs_triangle_ineq)
        finally have "\<bar>Gj_network \<sigma> f xs h N 1 w x - deriv f x\<bar>
            \<le> \<bar>Gj_network \<sigma> f xs h N 1 w x - Li\<bar> + \<bar>Li - deriv f x\<bar>" .
        also have "\<dots> < \<eta> * (5 / 2 + M1) + (\<eta> * (1 + 2 * S) + \<eta> * (1 / 2 + 2 * S))"
          using I1 J2 C1h_bound by linarith
        also have "\<dots> = \<eta> * (4 + M1 + 4 * S)"
          by (simp add: algebra_simps)
        also have "\<dots> \<le> \<epsilon>" using eps_bound' by simp
        finally show ?thesis .
      qed
    qed
    show "\<bar>Gj_network \<sigma> f (unif_part a b N) ((b - a) / real N) N 1 w x - deriv f x\<bar> < \<epsilon>"
      using goal unfolding h_def xs_def .
  qed
qed

end
