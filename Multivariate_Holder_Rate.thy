section \<open>Theorem 5.2: a convergence rate for Hoelder-continuous \<open>f\<close>\<close>

theory Multivariate_Holder_Rate
  imports Multivariate_Approximation
begin

text \<open>
  Theorem 5.2 of Costarelli and Spigler (p.185): for \<open>f\<close> Hoelder-continuous of order \<open>\<alpha>\<close> with
  constant \<open>L\<close>, the multivariate network of Theorem 5.1 approximates \<open>f\<close> uniformly on the box
  with an explicit \<open>O(N\<^sup>-\<^sup>\<alpha>)\<close> rate, for every \<open>N\<close>, once \<open>w\<close> is large enough (depending on \<open>N\<close>).

  Unlike Theorems 5.3/5.4 this is a QUANTITATIVE statement, so Theorem 5.1 cannot be reused as a
  black box: 5.1 chooses its \<open>\<sigma>\<close>-saturation tolerance \<open>\<epsilon>'\<close> AFTER \<open>N\<close>, which lets it bound each
  adjacent-node difference of \<open>f\<close> crudely by \<open>2M\<close>; here \<open>N\<close> is given first and that crude bound
  is too lossy. This is why \<open>multivariate_network_other_columns_bound\<close>,
  \<open>multivariate_network_same_column_bound\<close> and \<open>multivariate_network_H1_bound\<close> are parameterised
  by a bound \<open>Df\<close> on adjacent-node differences: Theorem 5.1 instantiates \<open>Df = 2M\<close>, and the
  theorem below instantiates \<open>Df = L h\<^sup>\<alpha>\<close> from the Hoelder condition.

  \<^bold>\<open>The constant is NOT the paper's.\<close> The paper works in \<open>\<real>\<^sup>2\<close> and its \<open>2\<^sup>\<alpha>\<^sup>/\<^sup>2\<close> comes from the
  cell diagonal \<open>\<surd>2 h\<close>. This development is \<open>n\<close>-dimensional and its \<open>H\<^sub>2\<close> estimate
  (\<open>multivariate_H2_bound\<close>) uses the sufficient mesh condition \<open>h * CARD('n) < \<delta>\<close>, so
  choosing \<open>\<delta> = h * (CARD('n)+2)\<close> gives the constant below. This is a valid
  replacement bound, not a proof of the paper's printed coefficient. The independent
  theory \<open>Paper_5_2_Counterexample\<close> refutes that printed coefficient under its stated
  hypotheses. Theory \<open>Paper_Multivariate\<close> provides the strict-supremum formulation
  of a corrected bound.
\<close>

(* Auxiliary for Theorem 5.2; not separately numbered. *)
lemma sample_point_adjacent_dist:
  fixes r0 :: "'n::finite"
  assumes ab: "a < b" and N: "N > 0"
    and h: "h = (b-a)/N" and xs: "xs = unif_part a b N"
    and j: "j \<in> {1..N}"
  shows "norm (sample_point r0 xs k j - sample_point r0 xs k (j-1)) \<le> h"
  using sample_point_step[OF h xs j, of r0 k] h_pos[OF ab N h] by simp


(* Theorem 5.2: endpoint-sampling operator, with a different explicit constant. *)
theorem multivariate_holder_rate:
  fixes a b :: real and f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: "'n::finite"
  fixes \<sigma> :: "real \<Rightarrow> real" and L \<alpha> :: real and N :: nat
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes N_pos: "N > 0"
  assumes L_pos: "L > 0"
  assumes \<alpha>_pos: "0 < \<alpha>" and \<alpha>_le1: "\<alpha> \<le> 1"
  assumes f_cont_on: "continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"
  assumes f_holder: "\<And>p q. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> (\<forall>r. q $ r \<in> {a..b}) \<Longrightarrow>
      \<bar>f p - f q\<bar> \<le> L * norm (p - q) powr \<alpha>"
  shows "\<exists>w0>0. \<forall>w\<ge>w0. \<forall>z. (\<forall>r. z $ r \<in> {a..b}) \<longrightarrow>
      \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z\<bar>
        < (1 + (1 + Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) * L
              * ((b - a) * (real CARD('n) + 2)) powr \<alpha>) / real N powr \<alpha>"
proof -
  define S where "S = Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  have S_nonneg: "S \<ge> 0"
    using bounded_sigmoidal unfolding S_def bounded_function_def
    by (meson UNIV_I abs_ge_zero cSUP_upper2)
  define xs where "xs = unif_part a b N"
  define h where "h = (b - a) / N"
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have Npowr_pos: "real N powr \<alpha> > 0" using N_pos by simp

  text \<open>\<open>M\<close>, a bound on \<open>|f|\<close> over the box.\<close>
  obtain M where M_prop: "\<forall>p. (\<forall>r. p $ r \<in> {a..b}) \<longrightarrow> \<bar>f p\<bar> \<le> M"
    using f_bounded_on_box[OF f_cont_on] by blast
  define z0 :: "(real, 'n) vec" where "z0 = (\<chi> r. a)"
  have z0_in_box: "\<forall>r. z0 $ r \<in> {a..b}" unfolding z0_def using a_lt_b by simp
  have M_nonneg: "M \<ge> 0" using M_prop z0_in_box by fastforce
  have f_bound: "\<And>p. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> \<bar>f p\<bar> \<le> M" using M_prop by blast

  text \<open>\<open>Df\<close>: adjacent grid points lie at distance \<open>\<le> h\<close>, so Hoelder gives \<open>|\<Delta>f| \<le> L h\<^sup>\<alpha>\<close>.\<close>
  define Df where "Df = L * h powr \<alpha>"
  have Df_nonneg: "0 \<le> Df" unfolding Df_def using L_pos by simp
  have df_bound: "\<And>k' j'. k' \<in> column_index r0 N \<Longrightarrow> j' \<in> {1..N} \<Longrightarrow>
      \<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> Df"
  proof -
    fix k' j' assume k'r: "k' \<in> column_index r0 N" and j'r: "j' \<in> {1..N}"
    have j'_box: "j' \<in> {0..N}" and jm1_box: "j' - 1 \<in> {0..N}" using j'r by auto
    have b1: "\<forall>r. sample_point r0 xs k' j' $ r \<in> {a..b}"
      using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j'_box k'r] .
    have b2: "\<forall>r. sample_point r0 xs k' (j' - 1) $ r \<in> {a..b}"
      using sample_point_in_box[OF a_lt_b N_pos h_def xs_def jm1_box k'r] .
    have d: "norm (sample_point r0 xs k' j' - sample_point r0 xs k' (j' - 1)) \<le> h"
      using sample_point_adjacent_dist[OF a_lt_b N_pos h_def xs_def j'r] .
    have "\<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar>
        \<le> L * norm (sample_point r0 xs k' j' - sample_point r0 xs k' (j' - 1)) powr \<alpha>"
      using f_holder[OF b1 b2] .
    also have "\<dots> \<le> L * h powr \<alpha>"
      using d L_pos \<alpha>_pos by (intro mult_left_mono powr_mono2) auto
    finally show "\<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> Df"
      unfolding Df_def .
  qed

  text \<open>\<open>\<delta>\<close>, \<open>\<eta>\<close> for \<open>H\<^sub>2\<close>: any \<open>\<delta>\<close> above the mesh threshold works; take \<open>\<delta> = h(n+2)\<close>.\<close>
  define \<delta> where "\<delta> = h * (real CARD('n) + 2)"
  have \<delta>_pos: "\<delta> > 0" unfolding \<delta>_def using hpos by simp
  have h_lt: "h * real CARD('n) < \<delta>"
    unfolding \<delta>_def using hpos by simp
  define \<eta> where "\<eta> = L * \<delta> powr \<alpha>"
  have \<eta>_pos: "\<eta> > 0" unfolding \<eta>_def using L_pos \<delta>_pos by simp
  have f_cont: "\<And>p q. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> (\<forall>r. q $ r \<in> {a..b}) \<Longrightarrow> norm (p - q) < \<delta>
                   \<Longrightarrow> \<bar>f p - f q\<bar> < \<eta>"
  proof -
    fix p q :: "(real, 'n) vec"
    assume pb: "\<forall>r. p $ r \<in> {a..b}" and qb: "\<forall>r. q $ r \<in> {a..b}" and lt: "norm (p - q) < \<delta>"
    have "\<bar>f p - f q\<bar> \<le> L * norm (p - q) powr \<alpha>" using f_holder[OF pb qb] .
    also have "\<dots> < L * \<delta> powr \<alpha>"
      using lt L_pos \<alpha>_pos by (intro mult_strict_left_mono powr_less_mono2) auto
    finally show "\<bar>f p - f q\<bar> < \<eta>" unfolding \<eta>_def .
  qed

  text \<open>\<open>\<epsilon>'\<close>, the \<open>\<sigma>\<close>-saturation tolerance, small enough that \<open>H\<^sub>1 < N\<^sup>-\<^sup>\<alpha>\<close>.\<close>
  define Nc where "Nc = real (card (column_index r0 N))"
  have Nc_nonneg: "Nc \<ge> 0" unfolding Nc_def by simp
  define B where "B = Nc * (real N * Df) + Nc * M + (real N - 1) * Df + M"
  have N_ge_1: "real N \<ge> 1" using N_pos by simp
  have B_nonneg: "B \<ge> 0"
    unfolding B_def using Nc_nonneg Df_nonneg M_nonneg N_ge_1 by simp
  define \<epsilon>' where "\<epsilon>' = 1 / (real N powr \<alpha> * (B + 1))"
  have \<epsilon>'_pos: "\<epsilon>' > 0" unfolding \<epsilon>'_def using Npowr_pos B_nonneg by simp

  text \<open>\<open>w\<^sub>0\<close>, the \<open>\<sigma>\<close>-saturation threshold at \<open>\<epsilon>'\<close> and \<open>h/2\<close>.\<close>
  have hhalf_pos: "h / 2 > 0" using hpos by simp
  obtain \<omega> where \<omega>_spec: "\<omega> > 0 \<and> (\<forall>w \<ge> \<omega>. \<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                     norm (z' - q) \<ge> h / 2 \<longrightarrow>
                     \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>')"
    using sigma_inactive_node_bound[OF sigmoidal_function \<epsilon>'_pos hhalf_pos] ..
  have \<omega>_pos: "\<omega> > 0" using \<omega>_spec by (rule conjunct1)
  have \<omega>_prop: "\<forall>w \<ge> \<omega>. \<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                     norm (z' - q) \<ge> h / 2 \<longrightarrow>
                     \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>'"
    using \<omega>_spec by (rule conjunct2)

  text \<open>The constant, and the two halves of the estimate.\<close>
  have H1_lt: "B * \<epsilon>' < 1 / real N powr \<alpha>"
  proof -
    have "B * \<epsilon>' = (B / (B + 1)) * (1 / real N powr \<alpha>)"
      unfolding \<epsilon>'_def using B_nonneg by (simp add: field_simps)
    also have "\<dots> < 1 * (1 / real N powr \<alpha>)"
    proof (rule mult_strict_right_mono)
      show "B / (B + 1) < 1" using B_nonneg by (simp add: divide_less_eq)
      show "0 < 1 / real N powr \<alpha>" using Npowr_pos by simp
    qed
    also have "\<dots> = 1 / real N powr \<alpha>" by simp
    finally show ?thesis .
  qed
  have H2_val: "(1 + S) * \<eta>
      = (1 + S) * L * ((b - a) * (real CARD('n) + 2)) powr \<alpha> / real N powr \<alpha>"
  proof -
    have dv: "\<delta> = (b - a) * (real CARD('n) + 2) / real N"
      unfolding \<delta>_def h_def by simp
    have "\<delta> powr \<alpha> = ((b - a) * (real CARD('n) + 2)) powr \<alpha> / real N powr \<alpha>"
      unfolding dv using a_lt_b by (simp add: powr_divide)
    then show ?thesis unfolding \<eta>_def by simp
  qed

  show ?thesis
  proof (intro exI[where x = \<omega>] conjI \<omega>_pos allI impI)
    \<comment> \<open>\<open>intro \<dots> allI impI\<close> strips BOTH the \<open>\<forall>w\<close> and the inner \<open>\<forall>z\<close>, so fix and assume
        both here -- an inner \<open>show "\<forall>z. \<dots>"\<close> fails to refine any pending goal\<close>
    fix w :: real and z :: "(real, 'n) vec"
    assume w_ge: "\<omega> \<le> w" and z_in_box: "\<forall>r. z $ r \<in> {a..b}"
    have step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow>
                   \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>'"
      using \<omega>_prop w_ge by blast
    obtain k j where k_range: "k \<in> column_index r0 N" and j_range: "j \<in> {1..N}"
        and z_in_column: "in_column r0 xs k z" and z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
        using exists_column_and_height[OF a_lt_b N_pos h_def xs_def z_in_box] by blast

      have H1: "\<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
          \<le> B * \<epsilon>'"
      proof -
        have raw: "\<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
            \<le> (real (card (column_index r0 N)) * (real N * (Df * \<epsilon>'))
                  + real (card (column_index r0 N)) * (M * \<epsilon>'))
                + ((real N - 1) * (Df * \<epsilon>') + M * \<epsilon>')"
          using multivariate_network_H1_bound[OF a_lt_b N_pos h_def xs_def \<epsilon>'_pos f_bound
            Df_nonneg df_bound k_range j_range z_height z_in_column z_in_box step0] .
        show ?thesis using raw unfolding B_def Nc_def by (simp add: algebra_simps)
      qed

      have H2: "\<bar>local_proxy r0 xs k j \<sigma> f w z - f z\<bar> < (1 + S) * \<eta>"
        unfolding S_def
        using multivariate_H2_bound[OF a_lt_b N_pos h_def xs_def bounded_sigmoidal \<eta>_pos \<delta>_pos
          f_cont h_lt j_range k_range z_in_column z_height z_in_box] .

      have triangle: "\<bar>multivariate_network \<sigma> f r0 xs N w z - f z\<bar>
          \<le> \<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
            + \<bar>local_proxy r0 xs k j \<sigma> f w z - f z\<bar>"
      proof -
        have "multivariate_network \<sigma> f r0 xs N w z - f z
            = (multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z)
              + (local_proxy r0 xs k j \<sigma> f w z - f z)" by simp
        then show ?thesis by (metis abs_triangle_ineq)
      qed

      have "\<bar>multivariate_network \<sigma> f r0 xs N w z - f z\<bar>
          < 1 / real N powr \<alpha> + (1 + S) * L
              * ((b - a) * (real CARD('n) + 2)) powr \<alpha> / real N powr \<alpha>"
        using triangle H1 H1_lt H2 H2_val by argo
      also have "\<dots> = (1 + (1 + S) * L * ((b - a) * (real CARD('n) + 2)) powr \<alpha>)
                      / real N powr \<alpha>"
        by (simp add: add_divide_distrib)
      finally show "\<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z\<bar>
          < (1 + (1 + Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)) * L
                * ((b - a) * (real CARD('n) + 2)) powr \<alpha>) / real N powr \<alpha>"
        unfolding S_def[symmetric] xs_def[symmetric] .
  qed
qed

end
