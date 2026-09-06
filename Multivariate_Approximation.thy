section \<open>Constructive Multivariate Approximation\<close>

theory Multivariate_Approximation
  imports Universal_Approximation_1d Partition_Facts Lp_Inequalities
begin

text \<open>
  This theory formalizes Section 5 of Costarelli and Spigler~\cite{CostarelliSpigler}: the
  constructive approximation theory of Sections 2-3 generalizes from functions of one
  variable to functions of \<open>n\<close> variables, using radial basis functions \<open>\<sigma>(w\<parallel>x-p_k\<parallel>)\<close> in
  place of \<open>\<sigma>(w(x-x_k))\<close>.  The paper states this "for simplicity... only for functions of two
  variables, as for higher dimensions the extension is straightforward" (p.182); we do not
  take that shortcut here and instead work directly in a general real normed vector space
  \<open>'a\<close> (which specializes to \<open>\<real>\<^sup>n\<close> for any \<open>n\<close>, via e.g. \<open>real^('n::finite)\<close>, without ever
  fixing \<open>n=2\<close>), so the 2-d case is never separately proved.

  The paper is explicit about what this substitution buys, immediately before Theorem 5.1
  (p.182): "note that here the function \<open>\<sigma>(\<parallel>(x,y)\<parallel>\<^sub>2)\<close> is actually a radial basis function
  (RBF)", and Remark 5.1 (p.184) adds that the resulting sums "lead to RBF neural networks",
  which is what distinguishes this construction from Cybenko's (where the variables are linked
  by an inner product inside the argument of \<open>\<sigma>\<close>) and from Lenze's.  That is exactly the shape
  of \<open>multivariate_network\<close> below: the activation is applied to a signed \<^emph>\<open>distance\<close>
  \<open>w \<sqdot> \<chi> \<sqdot> \<parallel>z-p\<parallel>\<close> from a center \<open>p\<close>, never to an affine functional of \<open>z\<close>.  The RBF reading is
  informal commentary in the paper, not a numbered claim, so nothing below is labelled by it;
  it is recorded here because it is the structural reason the radial saturation lemma
  (Lemma 5.1) replaces the one-sided Lemma 2.1.

  A second consequence of the same shape: the distinguished coordinate \<open>r0\<close>, along which the
  network takes its finite differences, is a \<^emph>\<open>parameter\<close> of every definition and theorem
  here.  The paper's (5.1) differences in \<open>y\<close> and its Remark 5.2 (p.184) observes that the
  transposed sum (5.3), differencing in \<open>x\<close>, works equally well.  Both are instances of the
  results below at \<open>CARD('n) = 2\<close>, obtained by the two choices of \<open>r0\<close>; no separate development
  is needed for (5.3).
\<close>

text \<open>
  Lemma 5.1, generalized: the sigmoidal saturation lemma of Lemma 2.1 (\<open>sigmoidal_uniform_approximation\<close>
  in theory Asymptotic\_Qualitative\_Properties) depends only on the scalar quantity \<open>w \<sqdot> d\<close>
  tending to \<open>\<plusminus>\<infinity>\<close>, not on the ambient space at all.  Replacing the signed real difference
  \<open>x - x_k\<close> by the (always nonnegative) distance
  \<open>\<parallel>x-p_k\<parallel>\<close> merges Lemma 2.1's two hypotheses \<open>x-x_k\<ge>h\<close> / \<open>x-x_k\<le>-h\<close> into the single
  hypothesis \<open>\<parallel>x-p_k\<parallel>\<ge>h\<close> (distance cannot be negative), giving both conclusions from a radial
  basis function \<open>\<sigma>(\<plusminus>w\<parallel>x-p_k\<parallel>)\<close> at once -- exactly matching the paper's own Lemma 5.1
  statement (which gives both \<open>|\<sigma>(w\<parallel>\<cdot>\<parallel>)-1|<\<epsilon>\<close> and \<open>|\<sigma>(-w\<parallel>\<cdot>\<parallel>)|<\<epsilon>\<close> under the one
  hypothesis \<open>\<parallel>(x,y)-(x_k,y_k)\<parallel>\<ge>h\<close>).
\<close>
(* Lemma 5.1: radial saturation, generalized to normed vector spaces. *)
lemma sigmoidal_uniform_approximation_dist:
  fixes ps :: "'a::real_normed_vector list"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes eps_pos: "(\<epsilon> :: real) > 0" and h_pos: "(h :: real) > 0"
  shows "\<exists>(\<omega>::real)>0. \<forall>w\<ge>\<omega>. \<forall>k<length ps. \<forall>x::'a. norm (x - ps ! k) \<ge> h \<longrightarrow>
           \<bar>\<sigma> (w * norm (x - ps ! k)) - 1\<bar> < \<epsilon> \<and> \<bar>\<sigma> (- w * norm (x - ps ! k))\<bar> < \<epsilon>"
proof -
  have lim_at_top: "(\<sigma> \<longlongrightarrow> 1) at_top"
    using sigmoidal_function unfolding sigmoidal_def by simp
  then obtain Ntop where Ntop_def: "\<forall>t \<ge> Ntop. \<bar>\<sigma> t - 1\<bar> < \<epsilon>"
    using eps_pos tendsto_at_top_epsilon_def by blast

  have lim_at_bot: "(\<sigma> \<longlongrightarrow> 0) at_bot"
    using sigmoidal_function unfolding sigmoidal_def by simp
  then obtain Nbot where Nbot_def: "\<forall>t \<le> Nbot. \<bar>\<sigma> t\<bar> < \<epsilon>"
    using eps_pos tendsto_at_bot_epsilon_def by fastforce

  obtain \<omega> where \<omega>_def: "\<omega> = max (max 1 (Ntop / h)) (-Nbot / h)"
    by blast
  then have \<omega>_pos: "0 < \<omega>"
    using h_pos by simp

  show ?thesis
  proof (intro exI[where x = \<omega>] allI impI conjI insert \<omega>_pos)
    fix w :: real and k :: nat and x :: 'a
    assume w_ge_\<omega>: "\<omega> \<le> w"
    assume k_bound: "k < length ps"
    assume d_ge_h: "norm (x - ps ! k) \<ge> h"

    have wh_ge_Ntop: "w * h \<ge> Ntop"
      using \<omega>_def h_pos pos_divide_le_eq w_ge_\<omega> by auto
    have wd_ge_wh: "w * norm (x - ps ! k) \<ge> w * h"
      using d_ge_h \<omega>_pos w_ge_\<omega> by (simp add: mult_left_mono)
    then have wd_ge_Ntop: "w * norm (x - ps ! k) \<ge> Ntop"
      using wh_ge_Ntop by linarith
    then show "\<bar>\<sigma> (w * norm (x - ps ! k)) - 1\<bar> < \<epsilon>"
      using Ntop_def by blast

    have neg_wh_le_Nbot: "- w * h \<le> Nbot"
    proof -
      have "- Nbot / h \<le> \<omega>"
        unfolding \<omega>_def by (rule max.cobounded2)
      then have "- Nbot / h \<le> w"
        using w_ge_\<omega> by linarith
      then have "- Nbot \<le> w * h"
        by (simp only: pos_divide_le_eq[OF h_pos])
      then have "- (w * h) \<le> Nbot"
        by linarith
      then show ?thesis
        by (simp only: mult_minus_left)
    qed
    then have neg_wd_le_Nbot: "- w * norm (x - ps ! k) \<le> Nbot"
      using wd_ge_wh by linarith
    then show "\<bar>\<sigma> (- w * norm (x - ps ! k))\<bar> < \<epsilon>"
      using Nbot_def by blast
  qed
qed

text \<open>
  Theorem 5.1, generalized to \<open>n\<close> dimensions (not just 2, per the paper's own remark that it
  restricts to \<open>n=2\<close> purely "for simplicity").  Points of \<open>\<real>\<^sup>n\<close> are represented as
  \<open>real^('n::finite)\<close> (so \<open>n = CARD('n)\<close>), the standard Isabelle/HOL-Analysis representation
  of Euclidean \<open>n\<close>-space.  Rather than the paper's own device of treating the last coordinate
  \<open>y\<close> specially by writing it as a separate argument (forced on them by fixing \<open>n=2\<close>), we fix
  \<open>r0 :: 'n\<close> as an arbitrary \<^emph>\<open>distinguished\<close> coordinate once and for all: the network
  telescopes \<open>f\<close>'s finite differences along direction \<open>r0\<close>, while every other coordinate
  \<open>r \<noteq> r0\<close> is held within one grid cell, exactly mirroring \<open>y\<close> vs. \<open>x\<close> in the paper's own
  \<open>\<chi>_ij\<close> for arbitrary \<open>n\<close> without singling out two axes by name.
\<close>

text \<open>
  A grid point in a \<open>k\<close>-indexed "column" (one grid cell per coordinate \<open>r \<noteq> r0\<close>, fixed by the
  multi-index \<open>k\<close>), at height \<open>j\<close> along the distinguished coordinate \<open>r0\<close>: the midpoint of
  cell \<open>k r\<close> in every other coordinate, and the midpoint of cell \<open>j\<close> in coordinate \<open>r0\<close> --
  generalizing the paper's node \<open>(t\<^sub>x\<^sub>i, t\<^sub>y\<^sub>j})\<close> (5.1).  As throughout this development, \<open>k\<close> and
  \<open>j\<close> are the paper's own unshifted indices (\<open>1,\<dots>,N\<close>, or \<open>0\<close> for the boundary term), while
  \<open>xs\<close> (as produced by \<open>unif_part\<close>) is offset by one from them, so every lookup into \<open>xs\<close> below
  uses \<open>k r\<close>/\<open>k r + 1\<close> or \<open>j\<close>/\<open>j+1\<close> rather than \<open>k r - 1\<close>/\<open>k r\<close> or \<open>j-1\<close>/\<open>j\<close> -- exactly the
  same convention theory Derivative\_Approximation's \<open>Gj_network\<close> uses for its own
  \<open>xs!(k+1)\<close>/\<open>xs!k\<close>.
\<close>
text \<open>
  The auxiliary geometry function \<open>grid_point\<close> uses midpoints at positive heights.
  Its height-zero case is a domain-contained auxiliary anchor, retained for older geometry
  lemmas. It is not a function-sampling point of equation (5.1). Function values are
  always evaluated at \<open>sample_point\<close>; the boundary radial center is \<open>sigma_anchor\<close>.
\<close>
definition grid_point :: "'n::finite \<Rightarrow> real list \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (real, 'n) vec" where
  "grid_point r0 xs k j =
     (\<chi> r. if r = r0 then (if j = 0 then xs ! 1 else (xs ! j + xs ! (j + 1)) / 2)
           else (xs ! (k r) + xs ! (k r + 1)) / 2)"

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_r0_zero: "grid_point r0 xs k 0 $ r0 = xs ! 1"
  unfolding grid_point_def by simp

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_r0_pos:
  assumes "j > 0"
  shows "grid_point r0 xs k j $ r0 = (xs ! j + xs ! (j + 1)) / 2"
  unfolding grid_point_def using assms by simp

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_r0: "grid_point r0 xs k j $ r0 = (if j = 0 then xs ! 1 else (xs ! j + xs ! (j + 1)) / 2)"
  unfolding grid_point_def by simp

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_other:
  assumes "r \<noteq> r0"
  shows "grid_point r0 xs k j $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
  unfolding grid_point_def using assms by simp

text \<open>
  Equation (5.1) has two different sets of points: endpoint samples for the coefficients,
  and midpoint radial centers for the activation arguments. At height zero, the sample
  lies on the boundary, whereas the radial center lies outside the box. Keeping these
  separate is necessary both for paper fidelity and for the saturation-distance bound.
\<close>
(* Equation (5.1): endpoint samples (x_i,y_j), distinct from midpoint radial centers. *)
definition sample_point :: "'n::finite \<Rightarrow> real list \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (real, 'n) vec" where
  "sample_point r0 xs k j = (\<chi> r. if r = r0 then xs ! (j + 1) else xs ! (k r + 1))"

(* Equation (5.1): midpoint radial centers, including the exterior boundary center. *)
definition sigma_anchor :: "'n::finite \<Rightarrow> real list \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (real, 'n) vec" where
  "sigma_anchor r0 xs k j =
     (\<chi> r. if r = r0 then (xs ! j + xs ! (j + 1)) / 2 else (xs ! (k r) + xs ! (k r + 1)) / 2)"

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_anchor_r0: "sigma_anchor r0 xs k j $ r0 = (xs ! j + xs ! (j + 1)) / 2"
  unfolding sigma_anchor_def by simp

text \<open>
  \<^const>\<open>grid_point\<close> and \<^const>\<open>sigma_anchor\<close> are the same point at every positive height, and
  differ only at height zero, where \<^const>\<open>grid_point\<close> returns the boundary node \<open>xs ! 1\<close>
  instead of the exterior midpoint.  Equation (5.1) uses \<^const>\<open>grid_point\<close> only for
  \<open>j \<in> {1..N}\<close> and \<^const>\<open>sigma_anchor\<close> for the boundary term, so the network is built from
  midpoints throughout; the height-zero case of \<^const>\<open>grid_point\<close> is used only inside
  mesh-arithmetic lemmas.  The bridge below records that identification, so that the two names
  cannot silently drift apart.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_eq_sigma_anchor:
  assumes j: "0 < j"
  shows "grid_point r0 xs k j = sigma_anchor r0 xs k j"
proof -
  have "\<And>r. grid_point r0 xs k j $ r = sigma_anchor r0 xs k j $ r"
  proof -
    fix r
    show "grid_point r0 xs k j $ r = sigma_anchor r0 xs k j $ r"
      using j by (cases "r = r0") (simp_all add: grid_point_def sigma_anchor_def)
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_anchor_other:
  assumes "r \<noteq> r0"
  shows "sigma_anchor r0 xs k j $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
  unfolding sigma_anchor_def using assms by simp

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_anchor_eq_grid_point:
  fixes r0 :: "'n::finite" and xs :: "real list" and k :: "'n \<Rightarrow> nat" and j :: nat
  assumes "j > 0"
  shows "sigma_anchor r0 xs k j = grid_point r0 xs k j"
  unfolding vec_eq_iff
proof
  fix r :: 'n
  show "sigma_anchor r0 xs k j $ r = grid_point r0 xs k j $ r"
    unfolding sigma_anchor_def grid_point_def using assms by simp
qed

text \<open>
  \<open>z\<close> lies in column \<open>k\<close>: every coordinate \<open>r \<noteq> r0\<close> of \<open>z\<close> falls in the \<open>k r\<close>-th grid cell
  of that axis, using \<^const>\<open>in_cell\<close> (\<open>Partition_Facts.thy\<close>) -- half-open, \<open>(xs!(k r),xs!(k r+1)]\<close>,
  except the first cell \<open>[xs!1,xs!2]\<close> -- exactly matching the paper's own \<open>\<chi>_{ij}\<close> convention
  (\<open>x\<in>(x_{i-1},x_i]\<close> for \<open>i\<ge>2\<close>, \<open>x\<in>[x_0,x_1]\<close> for \<open>i=1\<close>). UNIQUE per point (\<open>in_cell_unique\<close>),
  unlike an earlier closed-cell version of this definition: Theorem 5.1's own \<open>H_1\<close> argument
  needs that every column OTHER than the active one has \<open>column_sign\<close> forced to \<open>-1\<close>
  (\<open>column_sign_other_neg\<close> below) -- which requires a point to belong to at most one column,
  not just at least one (closed cells, allowing shared-boundary double-membership, would let an
  "other" column's sign spuriously come out \<open>+1\<close> at exactly such a boundary point, breaking the
  paper's own \<open>H_1\<close> estimate there). Named separately from \<open>column_sign\<close> below since the proof
  of Theorem 5.1 will repeatedly need to know \<^emph>\<open>which\<close> column (if any) a point lies in, not
  just the resulting \<open>\<plusminus>1\<close> sign.
\<close>
definition in_column :: "'n::finite \<Rightarrow> real list \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> (real, 'n) vec \<Rightarrow> bool" where
  "in_column r0 xs k z \<longleftrightarrow> (\<forall>r. r \<noteq> r0 \<longrightarrow> in_cell xs (k r) (z $ r))"

text \<open>
  The sign selector generalizing \<open>\<chi>_ij\<close> of (5.1): \<open>+1\<close> exactly when \<open>z\<close> lies in column \<open>k\<close>
  \<^emph>\<open>and\<close> is past height \<open>j\<close> (i.e. \<open>z$r0 \<ge> y_j = xs!(j+1)\<close>) along \<open>r0\<close>; \<open>-1\<close> otherwise.
\<close>
definition column_sign :: "'n::finite \<Rightarrow> real list \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (real, 'n) vec \<Rightarrow> real" where
  "column_sign r0 xs k j z =
     (if in_column r0 xs k z \<and> z $ r0 \<ge> xs ! (j + 1) then 1 else -1)"

text \<open>
  \<open>column_sign\<close> only ever takes the two values \<open>\<plusminus>1\<close> -- used together with
  \<open>sigmoidal_uniform_approximation_dist\<close> above (which gives saturation for both \<open>+w\<sqdot>d\<close> and
  \<open>-w\<sqdot>d\<close> at once) to control the radial basis function term \<open>\<sigma>(w \<sqdot> \<chi> \<sqdot> \<parallel>z-p\<parallel>)\<close> regardless of
  which of the two cases \<open>z\<close> falls into.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_sign_cases: "column_sign r0 xs k j z = 1 \<or> column_sign r0 xs k j z = -1"
  unfolding column_sign_def by auto

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
corollary abs_column_sign: "\<bar>column_sign r0 xs k j z\<bar> = 1"
  unfolding column_sign_def by auto

text \<open>
  The multi-indices ranging over the \<open>N\<^sup>n\<^sup>-\<^sup>1\<close> columns: functions assigning a grid cell
  \<open>k r \<in> {1..N}\<close> to every coordinate \<open>r \<noteq> r0\<close> (the value at \<open>r0\<close> itself is never read by
  \<^const>\<open>grid_point\<close> or \<^const>\<open>column_sign\<close>, so it is left unconstrained by using \<open>Pi\<^sub>E\<close> on
  the index set \<open>{r. r \<noteq> r0}\<close> rather than on all of \<open>'n\<close>: this is what keeps the column count
  at \<open>N\<^sup>n\<^sup>-\<^sup>1\<close> instead of \<open>N\<^sup>n\<close>).
\<close>
definition column_index :: "'n::finite \<Rightarrow> nat \<Rightarrow> ('n \<Rightarrow> nat) set" where
  "column_index r0 N = Pi\<^sub>E {r. r \<noteq> r0} (\<lambda>_. {1..N})"

text \<open>
  \<open>column_index\<close> is finite (it has exactly \<open>N\<^sup>n\<^sup>-\<^sup>1\<close> elements, since \<open>{r. r \<noteq> r0}\<close> has
  \<open>CARD('n)-1\<close> elements), which is what makes the two sums defining the network below
  genuine finite sums.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma finite_column_index: "finite (column_index r0 N)"
  unfolding column_index_def by (intro finite_PiE) auto

text \<open>\<open>column_index\<close> is nonempty whenever there is at least one grid cell per axis.\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_index_nonempty:
  assumes "N \<ge> (1::nat)"
  shows "column_index r0 N \<noteq> {}"
proof -
  have "(\<lambda>r\<in>{r. r \<noteq> r0}. 1) \<in> column_index r0 N"
    unfolding column_index_def using assms by (auto simp: PiE_def extensional_def)
  then show ?thesis by blast
qed

text \<open>
  Two different columns must differ at SOME coordinate \<open>r\<noteq>r0\<close> -- the witness \<open>H_1\<close>'s
  "other column" argument needs to invoke \<open>column_sign_other_neg\<close>/\<open>z_far_from_other_column\<close>
  at a concrete \<open>r\<close>, extracted here from mere function inequality via \<open>column_index\<close>'s own
  \<open>Pi\<^sub>E\<close>/extensionality.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_index_neq_witness:
  fixes r0 :: "'n::finite" and N :: nat and k k' :: "'n \<Rightarrow> nat"
  assumes k_range: "k \<in> column_index r0 N" and k'_range: "k' \<in> column_index r0 N"
  assumes k_neq: "k' \<noteq> k"
  shows "\<exists>r. r \<noteq> r0 \<and> k' r \<noteq> k r"
proof (rule ccontr)
  assume "\<not> (\<exists>r. r \<noteq> r0 \<and> k' r \<noteq> k r)"
  then have agree: "\<And>r. r \<noteq> r0 \<Longrightarrow> k' r = k r" by blast
  have ext_k: "\<And>r. r = r0 \<Longrightarrow> k r = undefined"
    using k_range unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have ext_k': "\<And>r. r = r0 \<Longrightarrow> k' r = undefined"
    using k'_range unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have "\<And>r. k' r = k r"
    using agree ext_k ext_k' by (metis)
  then have "k' = k" by (rule ext)
  then show False using k_neq by simp
qed

text \<open>
  The mechanism the paper's own \<open>H_1\<close> estimate (p.183-184) relies on: for a column \<open>k'\<close> OTHER
  than the one \<open>z\<close> actually lies in, \<open>column_sign\<close> is forced to \<open>-1\<close> REGARDLESS of height or
  of \<open>z$r0\<close> -- exactly matching how the paper's own \<open>\<chi>_{ij}(x,y)\<close>, for \<open>i\<close> other than the
  (unique, half-open-cell) active column, is \<open>-1\<close> unconditionally, no matter \<open>y\<close>. This is
  precisely where uniqueness of \<open>in_column\<close> (via \<open>in_cell\<close>'s half-open convention) is
  load-bearing: with the earlier closed-cell version, a point \<open>z\<close> on a shared cell boundary
  could satisfy \<open>in_column\<close> for TWO different columns at once, and this lemma -- hence the
  paper's own \<open>H_1\<close> bound on every "other column" term -- would fail exactly there.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_sign_other_neg:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k k' :: "'n \<Rightarrow> nat" and j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes k_range: "k \<in> column_index r0 N" and k'_range: "k' \<in> column_index r0 N"
  assumes k_diff: "r \<noteq> r0" "k' r \<noteq> k r"
  assumes z_in_column: "in_column r0 xs k z"
  shows "column_sign r0 xs k' j' z = -1"
proof -
  have kr_range: "k r \<in> {1..N}"
    using k_range k_diff(1) unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have kr'_range: "k' r \<in> {1..N}"
    using k'_range k_diff(1) unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have z_r_in_k: "in_cell xs (k r) (z $ r)"
    using z_in_column k_diff(1) unfolding in_column_def by blast
  have not_in_column_k': "\<not> in_column r0 xs k' z"
  proof
    assume "in_column r0 xs k' z"
    then have "in_cell xs (k' r) (z $ r)"
      using k_diff(1) unfolding in_column_def by blast
    then have "k' r = k r"
      using in_cell_unique[OF a_lt_b N_pos h_def xs_def kr'_range kr_range] z_r_in_k by blast
    then show False using k_diff(2) by simp
  qed
  then show ?thesis
    unfolding column_sign_def by simp
qed

text \<open>
  The network \<open>G_Nf\<close> (the paper's own notation decorates this \<open>G\<close> with a tilde) of (5.1),
  for arbitrary dimension \<open>n = CARD('n)\<close>: a finite difference
  of \<open>f\<close> along \<open>r0\<close>, for every column \<open>k\<close> and height \<open>j\<close>, weighted by a radial basis function
  centred at \<open>grid_point r0 xs k j\<close> with the directional sign \<open>column_sign r0 xs k j\<close>.
\<close>
(* Equation (5.1): endpoint coefficients with separate midpoint radial centers. *)
definition multivariate_network ::
  "(real \<Rightarrow> real) \<Rightarrow> ((real, 'n::finite) vec \<Rightarrow> real) \<Rightarrow> 'n \<Rightarrow> real list \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
   (real, 'n) vec \<Rightarrow> real" where
  "multivariate_network \<sigma> f r0 xs N w z =
     (\<Sum>k \<in> column_index r0 N. \<Sum>j\<in>{1..N}.
        (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
          * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)))
   + (\<Sum>k \<in> column_index r0 N.
        f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)))"

text \<open>
  Every point of the box \<open>[a,b]\<close> (in every coordinate) lies in \<^emph>\<open>some\<close> column: the
  n-dimensional analogue of \<open>exists_containing_interval\<close> (theory \<open>Partition_Facts\<close>),
  obtained by choosing a containing cell independently in each coordinate \<open>r \<noteq> r0\<close> (via the
  \<open>choice\<close> rule) and bundling the choices into a single multi-index.  This is the fact
  Theorem 5.1's proof will use to locate the "active" column for a given evaluation point,
  exactly as \<open>exists_containing_interval\<close> locates the active subinterval in Theorem 2.1.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma exists_column:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes z_in_box: "\<forall>r. z $ r \<in> {a..b}"
  shows "\<exists>k \<in> column_index r0 N. in_column r0 xs k z"
proof -
  have H: "\<forall>r. \<exists>i. i \<in> {1..N} \<and> in_cell xs i (z $ r)"
    using z_in_box exists_in_cell[OF a_lt_b N_pos h_def xs_def] by blast
  obtain i0 :: "'n \<Rightarrow> nat"
    where i0_def: "\<forall>r. i0 r \<in> {1..N} \<and> in_cell xs (i0 r) (z $ r)"
    using choice[OF H] by blast
  define k where "k = restrict i0 {r. r \<noteq> r0}"
  have k_mem: "k \<in> column_index r0 N"
    unfolding column_index_def
  proof (rule PiE_I)
    fix r :: 'n assume "r \<in> {r. r \<noteq> r0}"
    then show "k r \<in> {1..N}"
      using i0_def unfolding k_def by simp
  next
    fix r :: 'n assume "r \<notin> {r. r \<noteq> r0}"
    then show "k r = undefined"
      unfolding k_def by (simp add: restrict_def)
  qed
  have "in_column r0 xs k z"
    unfolding in_column_def using i0_def unfolding k_def by simp
  then show ?thesis
    using k_mem by blast
qed

text \<open>
  The companion fact for the distinguished coordinate \<open>r0\<close> itself, which \<open>exists_column\<close>
  does not cover (it only locates the other \<open>n-1\<close> coordinates): \<open>z$r0\<close> lies in some height
  cell \<open>j\<close>, directly from \<open>exists_containing_interval\<close> applied to the single real number
  \<open>z$r0\<close>.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma exists_height:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes z :: "(real, 'n::finite) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes "z $ r0 \<in> {a..b}"
  shows "\<exists>j. j \<in> {1..N} \<and> z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  using exists_containing_interval[OF a_lt_b N_pos h_def xs_def, of "z $ r0"] assms by blast

text \<open>
  Combining the two: every point of the box lies in some column \<open>k\<close> \<^emph>\<open>and\<close> some height \<open>j\<close>
  at once.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma exists_column_and_height:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes z_in_box: "\<forall>r. z $ r \<in> {a..b}"
  shows "\<exists>k j. k \<in> column_index r0 N \<and> j \<in> {1..N} \<and> in_column r0 xs k z \<and>
               z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
proof -
  obtain k where k_def: "k \<in> column_index r0 N" "in_column r0 xs k z"
    using exists_column[OF a_lt_b N_pos h_def xs_def z_in_box] by blast
  obtain j where j_def: "j \<in> {1..N}" "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
    using exists_height[OF a_lt_b N_pos h_def xs_def, of z r0] z_in_box by blast
  with k_def show ?thesis
    by blast
qed

text \<open>
  The first building block of Theorem 5.1's own \<open>H_2\<close> estimate (paper p.184, the local proxy
  \<open>L_{k\<mu>}\<close> "if \<open>\<mu>\<ge>2\<close>": \<open>L_{k\<mu>}(x,y):=\<Sum>_{j=1}^{\<mu>-1}(f(x_k,y_j)-f(x_k,y_{j-1}))+f(x_k,y_0)+
  (f(x_k,y_\<mu>)-f(x_k,y_{\<mu>-1}))\<sigma>(\<dots>)\<close>), generalized to an arbitrary distinguished coordinate
  \<open>r0\<close> and column \<open>k\<close>: the raw telescoping sum \<open>\<Sum>_{j=1}^{m}(f(gp_j)-f(gp_{j-1}))+f(gp_0)\<close>
  along \<open>r0\<close> (with every other coordinate held fixed at column \<open>k\<close>) collapses to \<open>f(gp_m)\<close>,
  exactly the identity the paper's own printed \<open>L_{k\<mu>}\<close> uses implicitly (via "\<open>=f(x_k,y_{\<mu>-1})\<close>",
  p.185, just above (5.2)) -- proved directly, mirroring \<open>forward_diff_telescope\<close>'s own
  induction, since it holds for any real-valued function of the grid point, not just \<open>f\<close> itself.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sample_point_telescope:
  fixes r0 :: "'n::finite" and xs :: "real list" and k :: "'n \<Rightarrow> nat"
  fixes f :: "(real, 'n) vec \<Rightarrow> real"
  shows "(\<Sum>j=1..m. f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
           + f (sample_point r0 xs k 0)
       = f (sample_point r0 xs k m)"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have insert_eq: "{1..Suc m} = insert (Suc m) {1..m}"
    by auto
  have "(\<Sum>j=1..Suc m. f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
      = (f (sample_point r0 xs k (Suc m)) - f (sample_point r0 xs k m))
        + (\<Sum>j=1..m. f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))"
    unfolding insert_eq by (subst sum.insert) simp_all
  then show ?case
    using Suc.IH by simp
qed

text \<open>
  The second building block for \<open>H_2\<close>: two grid points in the same column \<open>k\<close>, at consecutive
  heights \<open>j\<close> and \<open>j-1\<close> along \<open>r0\<close>, differ ONLY in their \<open>r0\<close>-coordinate (every other
  coordinate is the same midpoint, since both depend on \<open>k\<close> alone there). For \<open>j\<ge>2\<close> (both
  heights use the ordinary midpoint formula) that coordinate differs by exactly \<open>h\<close> --
  generalizing the paper's own implicit \<open>\<parallel>(t_xk,t_yj)-(t_xk,t_y(j-1))\<parallel>=h\<close> (used, e.g., via the
  node-distance argument leading to (5.2)). The \<open>j=1\<close> case is different (height \<open>0\<close> is now a
  real node, not a midpoint) and is handled separately below,
  \<open>grid_point_r0_step_boundary\<close>. Needs \<open>h\<close> as the fixed cell width (\<open>h=(b-a)/N\<close>) and
  \<open>j\<in>{2,...,N}\<close> so \<open>xs!(j-1)\<close>,\<open>xs!j\<close>,\<open>xs!(j+1)\<close> are valid partition nodes.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_r0_step:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {2..N}"
  shows "grid_point r0 xs k j - grid_point r0 xs k (j - 1) = h *\<^sub>R axis r0 1"
  unfolding vec_eq_iff
proof
  fix r :: 'n
  show "(grid_point r0 xs k j - grid_point r0 xs k (j - 1)) $ r = (h *\<^sub>R axis r0 1) $ r"
  proof (cases "r = r0")
    case True
    have j_eq: "j - 1 + 1 = j" using j_range by simp
    have jm1_pos: "j - 1 > 0" using j_range by simp
    have j_pos: "j > 0" using j_range by simp
    have "grid_point r0 xs k j $ r0 - grid_point r0 xs k (j - 1) $ r0
        = (xs ! j + xs ! (j + 1)) / 2 - (xs ! (j - 1) + xs ! j) / 2"
      unfolding grid_point_r0_pos[OF j_pos] grid_point_r0_pos[OF jm1_pos] using j_eq by simp
    also have "\<dots> = (xs ! (j + 1) - xs ! (j - 1)) / 2"
      by (simp add: field_simps)
    also have "\<dots> = h"
    proof -
      have s1: "xs ! j - xs ! (j - 1) = h"
        using difference_of_adj_terms[OF h_def xs_def] j_range by auto
      have s2: "xs ! (j + 1) - xs ! j = h"
        using difference_of_adj_terms[OF h_def xs_def, of "j + 1"] j_range by auto
      from s1 s2 show ?thesis by simp
    qed
    finally show ?thesis
      using True by simp
  next
    case False
    have e1: "grid_point r0 xs k j $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
      using grid_point_other[OF False, of xs k j] .
    have e2: "grid_point r0 xs k (j - 1) $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
      using grid_point_other[OF False, of xs k "j - 1"] .
    have diff0: "grid_point r0 xs k j $ r = grid_point r0 xs k (j - 1) $ r"
      using e1 e2 by simp
    have axis0: "(h *\<^sub>R axis r0 1) $ r = 0"
      using False by (simp add: axis_def)
    show ?thesis
      using diff0 axis0 by simp
  qed
qed

text \<open>
  The \<open>j=1\<close> boundary case of the same fact: height \<open>0\<close> is anchored at the real node \<open>xs!1\<close>, not
  a midpoint, so the step from height \<open>0\<close> to height \<open>1\<close> is only \<open>h/2\<close> (half the ordinary step),
  matching the paper's own \<open>\<mu>=1\<close> case of \<open>L_{k\<mu>}\<close> using \<open>\<sigma>(\<dots>\<parallel>(x,y)-(t_xk,t_y1)\<parallel>)\<close> directly
  against the real node \<open>y_0\<close> with no intervening midpoint gap on that side.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_r0_step_boundary:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "grid_point r0 xs k 1 - grid_point r0 xs k 0 = (h / 2) *\<^sub>R axis r0 1"
  unfolding vec_eq_iff
proof
  fix r :: 'n
  show "(grid_point r0 xs k 1 - grid_point r0 xs k 0) $ r = ((h / 2) *\<^sub>R axis r0 1) $ r"
  proof (cases "r = r0")
    case True
    have "grid_point r0 xs k 1 $ r0 - grid_point r0 xs k 0 $ r0
        = (xs ! 1 + xs ! 2) / 2 - xs ! 1"
      unfolding grid_point_r0_pos[OF zero_less_one] grid_point_r0_zero
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (xs ! 2 - xs ! 1) / 2"
      by (simp add: field_simps)
    also have "\<dots> = h / 2"
    proof -
      have s1: "xs ! 2 - xs ! 1 = h"
        using difference_of_adj_terms[OF h_def xs_def, of 2] N_pos by auto
      show ?thesis using s1 by simp
    qed
    finally show ?thesis
      using True by simp
  next
    case False
    have e1: "grid_point r0 xs k 1 $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
      using grid_point_other[OF False, of xs k 1] .
    have e2: "grid_point r0 xs k 0 $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
      using grid_point_other[OF False, of xs k 0] .
    have diff0: "grid_point r0 xs k 1 $ r = grid_point r0 xs k 0 $ r"
      using e1 e2 by simp
    have axis0: "((h / 2) *\<^sub>R axis r0 1) $ r = 0"
      using False by (simp add: axis_def)
    show ?thesis
      using diff0 axis0 by simp
  qed
qed

text \<open>
  The third building block for \<open>H_2\<close>: a point \<open>z\<close> in column \<open>k\<close> at height \<open>j\<close> is within
  \<open>h\<sqdot>(CARD('n)+2)/2\<close> of the anchor \<open>grid_point r0 xs k (j-1)\<close> -- the n-d analogue of the
  paper's own \<open>\<parallel>(x,y)-(x_k,y_{\<mu>-1})\<parallel>\<le>\<surd>2h\<close> (p.185, leading to (5.2)). Since this project's
  \<open>grid_point\<close> anchors at the MIDPOINT of each cell (not the paper's own raw node), the bound
  comes out looser and \<open>n\<close>-dependent rather than the paper's clean \<open>\<surd>2h\<close> -- via the L1 bound
  \<open>norm_le_l1_cart\<close> (simpler than an exact L2 computation, and sufficient for the
  existence-theorem shape Theorem 5.1 needs): every non-\<open>r0\<close> coordinate contributes \<open>\<le>h/2\<close>
  (half a cell width, from \<open>in_column\<close>), and the \<open>r0\<close>-coordinate contributes \<open>\<le>3h/2\<close> (since
  \<open>z$r0\<close> can be as far as the FAR end of cell \<open>j\<close> while the anchor sits at the midpoint of
  cell \<open>j-1\<close>, two cells away).
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma z_to_anchor_dist_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {1..N}"
  assumes k_range: "k \<in> column_index r0 N"
  assumes z_in_column: "in_column r0 xs k z"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  shows "norm (z - grid_point r0 xs k (j - 1)) \<le> h * (real CARD('n) + 2) / 2"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  text \<open>Per-component bound, \<open>r \<noteq> r0\<close>: half a cell width.\<close>
  have other_bound: "\<And>r. r \<noteq> r0 \<Longrightarrow> \<bar>(z - grid_point r0 xs k (j - 1)) $ r\<bar> \<le> h / 2"
  proof -
    fix r assume r_ne: "r \<noteq> r0"
    have kr_range: "k r \<in> {1..N}"
      using k_range r_ne unfolding column_index_def by (auto simp: PiE_def extensional_def)
    have z_r_cell: "in_cell xs (k r) (z $ r)"
      using z_in_column r_ne unfolding in_column_def by blast
    have z_r_lo: "xs ! (k r) \<le> z $ r" and z_r_hi: "z $ r \<le> xs ! (k r + 1)"
      using in_cell_lower[OF z_r_cell] in_cell_upper[OF z_r_cell] by auto
    have gp_r: "grid_point r0 xs k (j - 1) $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
      using grid_point_other[OF r_ne, of xs k "j - 1"] .
    have step: "xs ! (k r + 1) - xs ! (k r) = h"
      using difference_of_adj_terms[OF h_def xs_def, of "k r + 1"] kr_range by auto
    have eq: "(z - grid_point r0 xs k (j - 1)) $ r = z $ r - grid_point r0 xs k (j - 1) $ r"
      by simp
    have goal1: "z $ r - (xs ! (k r) + xs ! (k r + 1)) / 2 \<le> h / 2"
      using z_r_lo z_r_hi step by argo
    have goal2: "- (z $ r - (xs ! (k r) + xs ! (k r + 1)) / 2) \<le> h / 2"
      using z_r_lo z_r_hi step by argo
    have "\<bar>z $ r - grid_point r0 xs k (j - 1) $ r\<bar> \<le> h / 2"
      unfolding gp_r abs_le_iff using goal1 goal2 by blast
    then show "\<bar>(z - grid_point r0 xs k (j - 1)) $ r\<bar> \<le> h / 2"
      unfolding eq .
  qed
  text \<open>Per-component bound at \<open>r0\<close>: up to \<open>3h/2\<close>. The \<open>j=1\<close> case (anchor at the real node
    \<open>xs!1\<close>, not a midpoint) is actually tighter (\<open>\<le>h\<close>), but \<open>3h/2\<close> still holds uniformly, which
    keeps this lemma's conclusion the same for every \<open>j\<close>.\<close>
  have r0_bound: "\<bar>(z - grid_point r0 xs k (j - 1)) $ r0\<bar> \<le> 3 * h / 2"
  proof -
    have z_h_lo: "xs ! j \<le> z $ r0" and z_h_hi: "z $ r0 \<le> xs ! (j + 1)"
      using z_height by auto
    have s2: "xs ! (j + 1) - xs ! j = h"
      using difference_of_adj_terms[OF h_def xs_def, of "j + 1"] j_range by auto
    have eq: "(z - grid_point r0 xs k (j - 1)) $ r0 = z $ r0 - grid_point r0 xs k (j - 1) $ r0"
      by simp
    show ?thesis
    proof (cases "j = 1")
      case True
      have gp: "grid_point r0 xs k (j - 1) $ r0 = xs ! 1"
        unfolding True by (simp add: grid_point_r0_zero)
      have z_h_lo': "xs ! 1 \<le> z $ r0" and z_h_hi': "z $ r0 \<le> xs ! 2"
        using z_h_lo z_h_hi True by (simp_all add: eval_nat_numeral)
      have s2': "xs ! 2 - xs ! 1 = h"
        using s2 True by (simp add: eval_nat_numeral)
      have goal1: "z $ r0 - xs ! 1 \<le> 3 * h / 2"
        using z_h_lo' z_h_hi' s2' hpos by argo
      have goal2: "- (z $ r0 - xs ! 1) \<le> 3 * h / 2"
        using z_h_lo' z_h_hi' s2' hpos by argo
      have "\<bar>z $ r0 - grid_point r0 xs k (j - 1) $ r0\<bar> \<le> 3 * h / 2"
        unfolding gp abs_le_iff using goal1 goal2 by blast
      then show ?thesis unfolding eq .
    next
      case False
      then have jm1_pos: "j - 1 > 0" using j_range by simp
      have gp: "grid_point r0 xs k (j - 1) $ r0 = (xs ! (j - 1) + xs ! j) / 2"
      proof -
        have "j - 1 + 1 = j" using j_range by simp
        then show ?thesis unfolding grid_point_r0_pos[OF jm1_pos] by simp
      qed
      have s1: "xs ! j - xs ! (j - 1) = h"
        using difference_of_adj_terms[OF h_def xs_def] j_range by auto
      have goal1: "z $ r0 - (xs ! (j - 1) + xs ! j) / 2 \<le> 3 * h / 2"
        using z_h_lo z_h_hi s1 s2 by argo
      have goal2: "- (z $ r0 - (xs ! (j - 1) + xs ! j) / 2) \<le> 3 * h / 2"
        using z_h_lo z_h_hi s1 s2 by argo
      have "\<bar>z $ r0 - grid_point r0 xs k (j - 1) $ r0\<bar> \<le> 3 * h / 2"
        unfolding gp abs_le_iff using goal1 goal2 by blast
      then show ?thesis unfolding eq .
    qed
  qed
  text \<open>Aggregate via the L1 bound.\<close>
  have "norm (z - grid_point r0 xs k (j - 1))
      \<le> (\<Sum>r\<in>UNIV. \<bar>(z - grid_point r0 xs k (j - 1)) $ r\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> = \<bar>(z - grid_point r0 xs k (j - 1)) $ r0\<bar>
                 + (\<Sum>r\<in>UNIV - {r0}. \<bar>(z - grid_point r0 xs k (j - 1)) $ r\<bar>)"
    by (simp add: sum.remove)
  also have "\<dots> \<le> 3 * h / 2 + (\<Sum>r\<in>UNIV - {r0}. h / 2)"
    using r0_bound other_bound by (intro add_mono sum_mono) auto
  also have "\<dots> = 3 * h / 2 + real (CARD('n) - 1) * (h / 2)"
    by simp
  also have "\<dots> = h * (real CARD('n) + 2) / 2"
  proof -
    have card_pos: "CARD('n) \<ge> 1" by simp
    then have "real (CARD('n) - 1) = real CARD('n) - 1"
      by simp
    then show ?thesis by (simp add: field_simps)
  qed
  finally show ?thesis .
qed

text \<open>
  Every coordinate of every grid point lies in \<open>[a,b]\<close> -- needed so that a global
  uniform-continuity hypothesis on \<open>f\<close> (assumed only on the box \<open>Q=[a,b]^n\<close>, matching the
  paper's own \<open>f\<in>C(Q)\<close>) can be applied to \<open>f\<close> evaluated at grid points, including the height-\<open>0\<close>
  boundary node -- exactly the fact that motivated redefining \<open>grid_point\<close>'s height-\<open>0\<close> case
  above (with the OLD midpoint formula this would have been false at \<open>j=0\<close>).
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma grid_point_in_box:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {0..N}"
  assumes k_range: "k \<in> column_index r0 N"
  shows "\<forall>r. grid_point r0 xs k j $ r \<in> {a..b}"
proof
  fix r :: 'n
  show "grid_point r0 xs k j $ r \<in> {a..b}"
  proof (cases "r = r0")
    case True
    show ?thesis
    proof (cases "j = 0")
      case True': True
      have one_N1: "(1::nat) \<in> {1..N + 1}" using N_pos by simp
      have "xs ! 1 \<in> {a..b}"
        using els_in_ab[OF a_lt_b N_pos h_def xs_def] one_N1 by auto
      then show ?thesis
        using True True' by (simp add: grid_point_r0_zero)
    next
      case False
      then have j_pos: "j > 0" by simp
      have j_N1: "j \<in> {1..N + 1}" and jp1_N1: "j + 1 \<in> {1..N + 1}"
        using j_range j_pos by auto
      have xj: "xs ! j \<in> {a..b}" and xjp1: "xs ! (j + 1) \<in> {a..b}"
        using els_in_ab[OF a_lt_b N_pos h_def xs_def] j_N1 jp1_N1 by auto
      have gp_eq: "grid_point r0 xs k j $ r0 = (xs ! j + xs ! (j + 1)) / 2"
        using grid_point_r0_pos[OF j_pos, of r0 xs k] .
      then show ?thesis
        using True xj xjp1 by simp
    qed
  next
    case False
    have kr_range: "k r \<in> {1..N}"
      using k_range False unfolding column_index_def by (auto simp: PiE_def extensional_def)
    have kr_N1: "k r \<in> {1..N + 1}" and krp1_N1: "k r + 1 \<in> {1..N + 1}"
      using kr_range by auto
    have xk: "xs ! (k r) \<in> {a..b}" and xkp1: "xs ! (k r + 1) \<in> {a..b}"
      using els_in_ab[OF a_lt_b N_pos h_def xs_def] kr_N1 krp1_N1 by auto
    have gp_eq: "grid_point r0 xs k j $ r = (xs ! (k r) + xs ! (k r + 1)) / 2"
      using grid_point_other[OF False, of xs k j] .
    then show ?thesis
      using xk xkp1 by simp
  qed
qed

text \<open>
  The local proxy \<open>L_{k\<mu>}\<close>, generalized: matches the paper's own single closed formula (which
  reduces to the same expression for \<open>\<mu>=1\<close> and \<open>\<mu>\<ge>2\<close>, "(5.2) holds also in case \<open>\<mu>=1\<close>",
  p.185) -- an active \<open>\<sigma>\<close>-step from the anchor at height \<open>j-1\<close> to the value at height \<open>j\<close>.
\<close>
(* Auxiliary for Theorem 5.1: endpoint samples belong to the approximation box. *)
lemma sample_point_in_box:
  fixes r0 :: "'n::finite"
  assumes ab: "a < b" and N: "N > 0"
    and h: "h = (b-a)/N" and xs: "xs = unif_part a b N"
    and j: "j \<in> {0..N}" and k: "k \<in> column_index r0 N"
  shows "\<forall>r. sample_point r0 xs k j $ r \<in> {a..b}"
proof
  fix r
  have jr: "xs ! (j+1) \<in> {a..b}"
    using els_in_ab[OF ab N h xs, of "j+1"] j by auto
  have kr: "r \<noteq> r0 \<Longrightarrow> k r \<in> {1..N}"
    using k unfolding column_index_def by (auto simp: PiE_def)
  have rr: "r \<noteq> r0 \<Longrightarrow> xs ! (k r+1) \<in> {a..b}"
    using els_in_ab[OF ab N h xs, of "k r+1"] kr by auto
  show "sample_point r0 xs k j $ r \<in> {a..b}"
    using jr rr unfolding sample_point_def by simp
qed

(* Auxiliary for Theorems 5.1-5.2: consecutive endpoint samples are exactly one mesh apart. *)
lemma sample_point_step:
  fixes r0 :: "'n::finite"
  assumes h: "h = (b-a)/N" and xs: "xs = unif_part a b N"
    and j: "j \<in> {1..N}"
  shows "sample_point r0 xs k j - sample_point r0 xs k (j-1) = h *\<^sub>R axis r0 1"
proof -
  have diff: "xs ! (j+1) - xs ! j = h"
    using difference_of_adj_terms[OF h xs, of "j+1"] j by auto
  show ?thesis using j diff
    by (auto simp: vec_eq_iff sample_point_def axis_def)
qed

(* Auxiliary for Theorem 5.1: distance from a cell point to its preceding endpoint sample. *)
lemma z_to_sample_dist_bound:
  fixes r0 :: "'n::finite" and z :: "(real, 'n) vec"
  assumes ab: "a < b" and N: "N > 0"
    and h: "h = (b-a)/N" and xs: "xs = unif_part a b N"
    and j: "j \<in> {1..N}" and k: "k \<in> column_index r0 N"
    and col: "in_column r0 xs k z"
    and height: "z $ r0 \<in> {xs ! j .. xs ! (j+1)}"
  shows "norm (z - sample_point r0 xs k (j-1)) \<le> h * real CARD('n)"
proof -
  have coord: "\<And>r. \<bar>(z - sample_point r0 xs k (j-1)) $ r\<bar> \<le> h"
  proof -
    fix r
    show "\<bar>(z - sample_point r0 xs k (j-1)) $ r\<bar> \<le> h"
    proof (cases "r = r0")
      case True
      have diff: "xs ! (j+1) - xs ! j = h"
        using difference_of_adj_terms[OF h xs, of "j+1"] j by auto
      show ?thesis using height j diff True
        by (auto simp: sample_point_def abs_le_iff)
    next
      case False
      have kr: "k r \<in> {1..N}"
        using k False unfolding column_index_def by (auto simp: PiE_def extensional_def)
      have cell_mem: "in_cell xs (k r) (z $ r)"
        using col False unfolding in_column_def by blast
      have cell: "xs ! (k r) \<le> z $ r" "z $ r \<le> xs ! (k r+1)"
        using cell_mem unfolding in_cell_def by (auto simp: numeral_2_eq_2 split: if_splits)
      have diff: "xs ! (k r+1) - xs ! (k r) = h"
        using difference_of_adj_terms[OF h xs, of "k r+1"] kr by auto
      show ?thesis using cell diff False
        by (auto simp: sample_point_def abs_le_iff)
    qed
  qed
  have "norm (z - sample_point r0 xs k (j-1)) \<le>
        (\<Sum>r\<in>UNIV. \<bar>(z - sample_point r0 xs k (j-1)) $ r\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>r\<in>(UNIV :: 'n set). h)" by (intro sum_mono coord)
  also have "\<dots> = h * real CARD('n)" by simp
  finally show ?thesis .
qed

(* Equation (5.2), within the proof of Theorem 5.1: the active-cell local proxy. *)
definition local_proxy :: "'n::finite \<Rightarrow> real list \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> real)
  \<Rightarrow> ((real, 'n) vec \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> (real, 'n) vec \<Rightarrow> real" where
  "local_proxy r0 xs k j \<sigma> f w z =
     f (sample_point r0 xs k (j - 1))
     + (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
       * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))"

text \<open>
  Theorem 5.1's local-proxy estimate (5.2): endpoint samples in one cell are close to
  the target point. We use the dimension-independent estimate \<open>norm v \<le> \<Sum>r. \<bar>v$r\<bar>\<close>,
  giving the sufficient mesh condition \<open>h * real CARD('n) < \<delta>\<close>.
  This is a proof-side choice of mesh, not an additional assumption on the target.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_H2_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat
  fixes f :: "(real, 'n) vec \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real" and w :: real and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes \<eta>_pos: "\<eta> > 0" and \<delta>_pos: "\<delta> > 0"
  assumes f_cont: "\<And>p q. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> (\<forall>r. q $ r \<in> {a..b}) \<Longrightarrow> norm (p - q) < \<delta>
                     \<Longrightarrow> \<bar>f p - f q\<bar> < \<eta>"
  assumes h_lt: "h * real CARD('n) < \<delta>"
  assumes j_range: "j \<in> {1..N}"
  assumes k_range: "k \<in> column_index r0 N"
  assumes z_in_column: "in_column r0 xs k z"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  assumes z_in_box: "\<forall>r. z $ r \<in> {a..b}"
  defines "S \<equiv> Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  shows "\<bar>local_proxy r0 xs k j \<sigma> f w z - f z\<bar> < (1 + S) * \<eta>"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have h_lt_\<delta>: "h < \<delta>"
  proof -
    have card_ge: "1 \<le> real CARD('n)" by simp
    have "h \<le> h * real CARD('n)"
      using mult_left_mono[OF card_ge, of h] hpos by simp
    then show ?thesis using h_lt by linarith
  qed
  have S_nonneg: "S \<ge> 0"
    using bounded_sigmoidal unfolding S_def bounded_function_def
    by (meson UNIV_I abs_ge_zero cSUP_upper2)
  have S_bound: "\<bar>\<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))\<bar> \<le> S"
    unfolding S_def using bounded_sigmoidal unfolding bounded_function_def
    by (meson UNIV_I cSUP_upper2 order_refl)

  text \<open>Anchor term: \<open>|f(gp(j-1))-f(z)|<\<eta>\<close>, via \<open>z_to_sample_dist_bound\<close> and \<open>f_cont\<close>.\<close>
  have anchor_dist: "norm (z - sample_point r0 xs k (j - 1)) < \<delta>"
  proof -
    have "norm (z - sample_point r0 xs k (j - 1)) \<le> h * real CARD('n)"
      using z_to_sample_dist_bound[OF a_lt_b N_pos h_def xs_def j_range k_range z_in_column
        z_height] .
    then show ?thesis using h_lt by linarith
  qed
  have jm1_range: "j - 1 \<in> {0..N}" using j_range by auto
  have gp_jm1_box: "\<forall>r. sample_point r0 xs k (j - 1) $ r \<in> {a..b}"
    using sample_point_in_box[OF a_lt_b N_pos h_def xs_def jm1_range k_range] .
  have anchor_bound: "\<bar>f (sample_point r0 xs k (j - 1)) - f z\<bar> < \<eta>"
    using f_cont[OF gp_jm1_box z_in_box] anchor_dist by (simp add: norm_minus_commute)

  text \<open>Active-step term: \<open>|f(gp j)-f(gp(j-1))|<\<eta>\<close>, via \<open>sample_point_step\<close>.\<close>
  have j_range01: "j \<in> {0..N}" using j_range by auto
  have gp_j_box: "\<forall>r. sample_point r0 xs k j $ r \<in> {a..b}"
    using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j_range01 k_range] .
  have step_dist: "norm (sample_point r0 xs k j - sample_point r0 xs k (j - 1)) < \<delta>"
  proof -
    have "norm (sample_point r0 xs k j - sample_point r0 xs k (j - 1)) = h"
      using sample_point_step[OF h_def xs_def j_range, of r0 k] hpos by simp
    then show ?thesis using h_lt_\<delta> by simp
  qed
  have step_bound: "\<bar>f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1))\<bar> < \<eta>"
    using f_cont[OF gp_j_box gp_jm1_box] step_dist by simp

  text \<open>Combine.\<close>
  have "\<bar>local_proxy r0 xs k j \<sigma> f w z - f z\<bar>
      \<le> \<bar>f (sample_point r0 xs k (j - 1)) - f z\<bar>
        + \<bar>f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1))\<bar>
          * \<bar>\<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))\<bar>"
    unfolding local_proxy_def
  proof -
    have "f (sample_point r0 xs k (j - 1))
          + (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
            * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)) - f z
        = (f (sample_point r0 xs k (j - 1)) - f z)
          + (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
            * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))"
      by simp
    then show "\<bar>f (sample_point r0 xs k (j - 1))
          + (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
            * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)) - f z\<bar>
        \<le> \<bar>f (sample_point r0 xs k (j - 1)) - f z\<bar>
          + \<bar>f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1))\<bar>
            * \<bar>\<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))\<bar>"
      using abs_triangle_ineq abs_mult by (metis (no_types, lifting))
  qed
  also have "\<dots> < \<eta> + \<eta> * S"
  proof -
    have "\<bar>f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1))\<bar>
          * \<bar>\<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))\<bar>
        \<le> \<eta> * S"
      using mult_mono[OF less_imp_le[OF step_bound] S_bound less_imp_le[OF \<eta>_pos] abs_ge_zero] .
    then show ?thesis
      using anchor_bound by linarith
  qed
  also have "\<dots> = (1 + S) * \<eta>"
    by (simp add: algebra_simps)
  finally show ?thesis.
qed

text \<open>
  Deriving \<open>multivariate_H2_bound\<close>'s uniform-continuity hypothesis from the paper's own weaker
  \<open>f\<in>C(Q)\<close>: the box \<open>Q={z. \<forall>r. z$r\<in>[a,b]}\<close> is compact (closed as an intersection of preimages
  of \<open>[a,b]\<close> under the continuous coordinate projections, bounded via the same L1 bound used
  in \<open>z_to_anchor_dist_bound\<close>), so \<open>continuous_on Q f\<close> already gives uniform continuity there,
  exactly as \<open>uniform_continuity_interval\<close> does for the 1-d case.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma box_compact:
  fixes a b :: real
  shows "compact {z :: (real, 'n::finite) vec. \<forall>r. z $ r \<in> {a..b}}"
proof (rule compact_eq_bounded_closed[THEN iffD2], intro conjI)
  have bound_ex: "\<exists>M :: real. \<forall>z :: (real, 'n) vec. (\<forall>r. z $ r \<in> {a..b}) \<longrightarrow> norm z \<le> M"
  proof (intro exI[where x = "real CARD('n) * max \<bar>a\<bar> \<bar>b\<bar>"] allI impI)
    fix z :: "(real, 'n) vec" assume z_box: "\<forall>r. z $ r \<in> {a..b}"
    define M where M_def: "M = max \<bar>a\<bar> \<bar>b\<bar>"
    have bound1: "norm z \<le> (\<Sum>r\<in>(UNIV :: 'n set). \<bar>z $ r\<bar>)"
      by (rule norm_le_l1_cart)
    have bound2: "\<And>r. r \<in> (UNIV :: 'n set) \<Longrightarrow> \<bar>z $ r\<bar> \<le> M"
    proof -
      fix r :: 'n
      have zr_lo: "a \<le> z $ r" and zr_hi: "z $ r \<le> b" using z_box by auto
      have "z $ r \<le> M" using zr_hi unfolding M_def by auto
      moreover have "- z $ r \<le> M" using zr_lo unfolding M_def by auto
      ultimately show "\<bar>z $ r\<bar> \<le> M" by (simp add: abs_le_iff)
    qed
    have bound3: "(\<Sum>r\<in>(UNIV :: 'n set). \<bar>z $ r\<bar>) \<le> (\<Sum>r\<in>(UNIV :: 'n set). M)"
      by (intro sum_mono bound2)
    have bound4: "(\<Sum>r\<in>(UNIV :: 'n set). M) = real CARD('n) * M"
      by simp
    have "norm z \<le> real CARD('n) * M"
      using bound1 bound3 bound4 by linarith
    then show "norm z \<le> real CARD('n) * max \<bar>a\<bar> \<bar>b\<bar>"
      unfolding M_def .
  qed
  show "bounded {z :: (real, 'n::finite) vec. \<forall>r. z $ r \<in> {a..b}}"
    unfolding bounded_iff using bound_ex by blast
  show "closed {z :: (real, 'n::finite) vec. \<forall>r. z $ r \<in> {a..b}}"
  proof -
    have eq: "{z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}} = (\<Inter>r. {z. z $ r \<in> {a..b}})"
      by auto
    have "closed ((\<Inter>r. {z :: (real, 'n) vec. z $ r \<in> {a..b}}))"
    proof (intro closed_INT ballI)
      fix r :: 'n
      have vim_closed: "closed ((\<lambda>z :: (real, 'n) vec. z $ r) -` {a..b})"
        by (rule closed_vimage_vec_nth[OF closed_atLeastAtMost])
      have vim_eq: "(\<lambda>z :: (real, 'n) vec. z $ r) -` {a..b} = {z :: (real, 'n) vec. z $ r \<in> {a..b}}"
        by (simp add: vimage_def)
      show "closed {z :: (real, 'n) vec. z $ r \<in> {a..b}}"
        using vim_closed vim_eq by simp
    qed
    then show ?thesis unfolding eq .
  qed
qed

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_uniform_continuity_box:
  fixes a b :: real and f :: "(real, 'n::finite) vec \<Rightarrow> real"
  assumes f_cont_on: "continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"
  assumes eps_pos: "\<epsilon> > 0"
  shows "\<exists>\<delta>>0. \<forall>p q. (\<forall>r. p $ r \<in> {a..b}) \<longrightarrow> (\<forall>r. q $ r \<in> {a..b}) \<longrightarrow> norm (p - q) < \<delta>
           \<longrightarrow> \<bar>f p - f q\<bar> < \<epsilon>"
proof -
  have "uniformly_continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"
    using box_compact f_cont_on compact_uniformly_continuous by blast
  then obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and \<delta>_prop: "\<forall>p\<in>{z. \<forall>r. z $ r \<in> {a..b}}. \<forall>q\<in>{z. \<forall>r. z $ r \<in> {a..b}}.
                   dist q p < \<delta> \<longrightarrow> dist (f q) (f p) < \<epsilon>"
    unfolding uniformly_continuous_on_def using eps_pos by blast
  show ?thesis
  proof (intro exI[where x = \<delta>] conjI allI impI)
    show "\<delta> > 0" using \<delta>_pos .
  next
    fix p q :: "(real, 'n) vec"
    assume p_box: "\<forall>r. p $ r \<in> {a..b}" and q_box: "\<forall>r. q $ r \<in> {a..b}"
      and pq_close: "norm (p - q) < \<delta>"
    have p_mem: "p \<in> {z. \<forall>r. z $ r \<in> {a..b}}" using p_box by simp
    have q_mem: "q \<in> {z. \<forall>r. z $ r \<in> {a..b}}" using q_box by simp
    have "dist q p < \<delta>" using pq_close by (simp add: dist_norm norm_minus_commute)
    then have "dist (f q) (f p) < \<epsilon>" using \<delta>_prop p_mem q_mem by blast
    then show "\<bar>f p - f q\<bar> < \<epsilon>" by (simp add: dist_real_def abs_minus_commute)
  qed
qed

text \<open>
  \<open>f\<close> is bounded on the box, needed for \<open>H_1\<close>'s own \<open>f_bound\<close> hypothesis (\<open>multivariate_network_H1_bound\<close>):
  a continuous real-valued function on a compact set has a bounded, compact image
  (\<open>compact_continuous_image\<close>, \<open>compact_imp_bounded\<close>), giving an explicit sup bound \<open>M\<close>.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma f_bounded_on_box:
  fixes a b :: real and f :: "(real, 'n::finite) vec \<Rightarrow> real"
  assumes f_cont_on: "continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"
  shows "\<exists>M. \<forall>p. (\<forall>r. p $ r \<in> {a..b}) \<longrightarrow> \<bar>f p\<bar> \<le> M"
proof -
  have compact_img: "compact (f ` {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})"
    using compact_continuous_image[OF f_cont_on box_compact] .
  have bounded_img: "bounded (f ` {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})"
    using compact_img compact_imp_bounded by blast
  then obtain M where M_prop: "\<forall>y \<in> f ` {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}. \<bar>y\<bar> \<le> M"
    unfolding bounded_iff by auto
  show ?thesis
  proof (intro exI[where x = M] allI impI)
    fix p :: "(real, 'n) vec" assume p_box: "\<forall>r. p $ r \<in> {a..b}"
    then have "f p \<in> f ` {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}" by auto
    then show "\<bar>f p\<bar> \<le> M" using M_prop by auto
  qed
qed

text \<open>
  The first building block for \<open>H_1\<close> (paper p.184-185): every grid point outside the active
  column \<open>k\<close> is at distance at least \<open>h/2\<close> from \<open>z\<close> -- the "different column" half of the
  paper's own uniform distance claim (p.185, just before (5.2), for every node other than the
  one active node). Realized via a SINGLE differing coordinate: if column \<open>k'\<close> disagrees with
  the active column \<open>k\<close> at some axis other than \<open>r0\<close>, the distance in that one coordinate
  alone is already \<open>\<ge>h/2\<close> (adjacent cells' midpoints are \<open>h\<close> apart, and \<open>z\<close> can be at most
  \<open>h/2\<close> from its own cell's near boundary), which lower-bounds the full Euclidean norm via
  \<open>component_le_norm_cart\<close>. Holds for every height \<open>j'\<close> in that other column, uniformly.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma z_far_from_other_column:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k k' :: "'n \<Rightarrow> nat" and j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes k_range: "k \<in> column_index r0 N" and k'_range: "k' \<in> column_index r0 N"
  assumes k_diff: "r \<noteq> r0" "k' r \<noteq> k r"
  assumes z_in_column: "in_column r0 xs k z"
  shows "norm (z - grid_point r0 xs k' j') \<ge> h / 2"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have kr_range: "k r \<in> {1..N}"
    using k_range k_diff(1) unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have kr'_range: "k' r \<in> {1..N}"
    using k'_range k_diff(1) unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have zr_cell: "in_cell xs (k r) (z $ r)"
    using z_in_column k_diff(1) unfolding in_column_def by blast
  have zr_lo: "xs ! (k r) \<le> z $ r" and zr_hi: "z $ r \<le> xs ! (k r + 1)"
    using in_cell_lower[OF zr_cell] in_cell_upper[OF zr_cell] by auto
  have step_k: "xs ! (k r + 1) - xs ! (k r) = h"
    using difference_of_adj_terms[OF h_def xs_def, of "k r + 1"] kr_range by auto
  have gp'_r: "grid_point r0 xs k' j' $ r = (xs ! (k' r) + xs ! (k' r + 1)) / 2"
    using grid_point_other[OF k_diff(1), of xs k' j'] .
  have dist_ge: "\<bar>z $ r - grid_point r0 xs k' j' $ r\<bar> \<ge> h / 2"
  proof (cases "k' r < k r")
    case True
    then have le: "k' r + 1 \<le> k r" by simp
    have kp1_N1: "k' r + 1 \<in> {1..N + 1}" and k_N1: "k r \<in> {1..N + 1}"
      using kr_range kr'_range by auto
    have step_k': "xs ! (k' r + 1) - xs ! (k' r) = h"
      using difference_of_adj_terms[OF h_def xs_def, of "k' r + 1"] kr'_range by auto
    have mono: "xs ! (k' r + 1) \<le> xs ! (k r)"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] kp1_N1 k_N1 le by blast
    show ?thesis
      unfolding gp'_r using zr_lo zr_hi step_k step_k' mono by argo
  next
    case False
    then have k_lt: "k r < k' r" using k_diff(2) by simp
    then have le: "k r + 1 \<le> k' r" by simp
    have kp1_N1: "k r + 1 \<in> {1..N + 1}" and k'_N1: "k' r \<in> {1..N + 1}"
      using kr_range kr'_range by auto
    have step_k': "xs ! (k' r + 1) - xs ! (k' r) = h"
      using difference_of_adj_terms[OF h_def xs_def, of "k' r + 1"] kr'_range by auto
    have mono: "xs ! (k r + 1) \<le> xs ! (k' r)"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] kp1_N1 k'_N1 le by blast
    show ?thesis
      unfolding gp'_r using zr_lo zr_hi step_k step_k' mono by argo
  qed
  have "\<bar>(z - grid_point r0 xs k' j') $ r\<bar> \<ge> h / 2"
    using dist_ge by simp
  then show ?thesis
    using component_le_norm_cart[of "z - grid_point r0 xs k' j'" r] by linarith
qed

text \<open>
  The \<open>sigma_anchor\<close> analogue of \<open>z_far_from_other_column\<close>, needed for the boundary term
  (height \<open>0\<close>) of \<^const>\<open>multivariate_network\<close>'s "other column" sum: since \<open>sigma_anchor\<close> and
  \<^const>\<open>grid_point\<close> agree on every coordinate \<open>r\<noteq>r0\<close> (both are the plain cell-\<open>k' r\<close> midpoint
  there -- only the \<open>r0\<close>-coordinate at height \<open>0\<close> differs), the exact same single-coordinate
  argument applies verbatim.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_anchor_far_from_other_column:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k k' :: "'n \<Rightarrow> nat" and j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes k_range: "k \<in> column_index r0 N" and k'_range: "k' \<in> column_index r0 N"
  assumes k_diff: "r \<noteq> r0" "k' r \<noteq> k r"
  assumes z_in_column: "in_column r0 xs k z"
  shows "norm (z - sigma_anchor r0 xs k' j') \<ge> h / 2"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have kr_range: "k r \<in> {1..N}"
    using k_range k_diff(1) unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have kr'_range: "k' r \<in> {1..N}"
    using k'_range k_diff(1) unfolding column_index_def by (auto simp: PiE_def extensional_def)
  have zr_cell: "in_cell xs (k r) (z $ r)"
    using z_in_column k_diff(1) unfolding in_column_def by blast
  have zr_lo: "xs ! (k r) \<le> z $ r" and zr_hi: "z $ r \<le> xs ! (k r + 1)"
    using in_cell_lower[OF zr_cell] in_cell_upper[OF zr_cell] by auto
  have step_k: "xs ! (k r + 1) - xs ! (k r) = h"
    using difference_of_adj_terms[OF h_def xs_def, of "k r + 1"] kr_range by auto
  have gp'_r: "sigma_anchor r0 xs k' j' $ r = (xs ! (k' r) + xs ! (k' r + 1)) / 2"
    using sigma_anchor_other[OF k_diff(1), of xs k' j'] .
  have dist_ge: "\<bar>z $ r - sigma_anchor r0 xs k' j' $ r\<bar> \<ge> h / 2"
  proof (cases "k' r < k r")
    case True
    then have le: "k' r + 1 \<le> k r" by simp
    have kp1_N1: "k' r + 1 \<in> {1..N + 1}" and k_N1: "k r \<in> {1..N + 1}"
      using kr_range kr'_range by auto
    have step_k': "xs ! (k' r + 1) - xs ! (k' r) = h"
      using difference_of_adj_terms[OF h_def xs_def, of "k' r + 1"] kr'_range by auto
    have mono: "xs ! (k' r + 1) \<le> xs ! (k r)"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] kp1_N1 k_N1 le by blast
    show ?thesis
      unfolding gp'_r using zr_lo zr_hi step_k step_k' mono by argo
  next
    case False
    then have k_lt: "k r < k' r" using k_diff(2) by simp
    then have le: "k r + 1 \<le> k' r" by simp
    have kp1_N1: "k r + 1 \<in> {1..N + 1}" and k'_N1: "k' r \<in> {1..N + 1}"
      using kr_range kr'_range by auto
    have step_k': "xs ! (k' r + 1) - xs ! (k' r) = h"
      using difference_of_adj_terms[OF h_def xs_def, of "k' r + 1"] kr'_range by auto
    have mono: "xs ! (k r + 1) \<le> xs ! (k' r)"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] kp1_N1 k'_N1 le by blast
    show ?thesis
      unfolding gp'_r using zr_lo zr_hi step_k step_k' mono by argo
  qed
  have "\<bar>(z - sigma_anchor r0 xs k' j') $ r\<bar> \<ge> h / 2"
    using dist_ge by simp
  then show ?thesis
    using component_le_norm_cart[of "z - sigma_anchor r0 xs k' j'" r] by linarith
qed

text \<open>
  The companion fact for \<open>H_1\<close>: within the SAME column \<open>k\<close>, every \<open>\<sigma>\<close>-anchor at a height
  \<open>j'\<close> other than the active height \<open>j\<close> is also at distance \<open>\<ge>h/2\<close> from \<open>z\<close> -- the "same
  column, different height" half of the paper's own uniform distance claim (p.185, just before
  (5.2)). Unlike \<open>z_far_from_other_column\<close>, this needs \<open>sigma_anchor\<close> rather than
  \<open>grid_point\<close>: at \<open>j'=0\<close> the anchor is the deliberately out-of-domain phantom midpoint, whose
  whole purpose is to keep this distance guarantee \<open>\<ge>h/2\<close> even when \<open>z\<close> sits at the domain
  boundary \<open>xs!1\<close> (see \<open>sigma_anchor\<close>'s own comment above). Since both \<open>z\<close> and every
  \<open>sigma_anchor\<close> at column \<open>k\<close> agree on every coordinate \<open>r\<noteq>r0\<close>, the whole distance lives in
  the single \<open>r0\<close>-coordinate.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma z_far_same_column_diff_height:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {1..N}" and j'_range: "j' \<in> {0..N}"
  assumes j_diff: "j' \<noteq> j"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  shows "norm (z - sigma_anchor r0 xs k j') \<ge> h / 2"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have anchor_r0: "sigma_anchor r0 xs k j' $ r0 = (xs ! j' + xs ! (j' + 1)) / 2"
    using sigma_anchor_r0 .
  have step_j': "xs ! (j' + 1) - xs ! j' = h"
    using difference_of_adj_terms[OF h_def xs_def, of "j' + 1"] j'_range by auto
  have z_lo: "xs ! j \<le> z $ r0" and z_hi: "z $ r0 \<le> xs ! (j + 1)"
    using z_height by auto
  have dist_ge: "\<bar>z $ r0 - sigma_anchor r0 xs k j' $ r0\<bar> \<ge> h / 2"
  proof (cases "j' < j")
    case True
    then have le: "j' + 1 \<le> j" by simp
    have jp1_N1: "j' + 1 \<in> {1..N + 1}" and j_N1: "j \<in> {1..N + 1}"
      using j'_range j_range by auto
    have mono: "xs ! (j' + 1) \<le> xs ! j"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] jp1_N1 j_N1 le by blast
    show ?thesis
      unfolding anchor_r0 using z_lo z_hi step_j' mono hpos by argo
  next
    case False
    then have j_lt: "j < j'" using j_diff by simp
    then have le: "j + 1 \<le> j'" by simp
    have jp1_N1: "j + 1 \<in> {1..N + 1}" and j'_N1: "j' \<in> {1..N + 1}"
      using j_range j'_range le by auto
    have mono: "xs ! (j + 1) \<le> xs ! j'"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] jp1_N1 j'_N1 le by blast
    show ?thesis
      unfolding anchor_r0 using z_lo z_hi step_j' mono hpos by argo
  qed
  have "\<bar>(z - sigma_anchor r0 xs k j') $ r0\<bar> \<ge> h / 2"
    using dist_ge by simp
  then show ?thesis
    using component_le_norm_cart[of "z - sigma_anchor r0 xs k j'" r0] by linarith
qed

text \<open>
  The saturation bound \<open>H_1\<close> needs at every inactive node: for \<open>w\<close> large enough, \<open>\<sigma>\<close> evaluated
  at \<open>w\<sqdot>s\<sqdot>\<parallel>z-q\<parallel>\<close> is within \<open>\<epsilon>\<close> of its "target" value, \<open>1\<close> when the sign \<open>s=1\<close> and \<open>0\<close> when
  \<open>s=-1\<close> -- matching exactly the two values \<^const>\<open>column_sign\<close> ever takes
  (\<open>column_sign_cases\<close>), so this composes directly with it and with the two distance lemmas
  above (\<open>z_far_from_other_column\<close>/\<open>z_far_same_column_diff_height\<close>, both concluding
  \<open>\<parallel>z-\<dots>\<parallel>\<ge>h/2\<close>) at every call site. Proved by the same construction as
  \<open>sigmoidal_uniform_approximation_dist\<close> (whose own \<open>\<omega>\<close> depends only on \<open>\<sigma>\<close>, \<open>\<epsilon>\<close>, \<open>h\<close> -- never
  on the point list), specialized to a single point \<open>q\<close> and an explicit \<open>\<plusminus>1\<close> sign \<open>s\<close> rather
  than a node index \<open>k\<close>, since \<open>H_1\<close>'s nodes range over both \<^const>\<open>grid_point\<close> and
  \<^const>\<open>sigma_anchor\<close> rather than a single fixed list.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_inactive_node_bound:
  fixes \<sigma> :: "real \<Rightarrow> real" and h :: real
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes eps_pos: "(\<epsilon> :: real) > 0" and h_pos: "h > 0"
  shows "\<exists>(\<omega>::real)>0. \<forall>w\<ge>\<omega>. \<forall>z q :: (real, 'n::finite) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
           norm (z - q) \<ge> h \<longrightarrow>
           \<bar>\<sigma> (w * s * norm (z - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
proof -
  have lim_at_top: "(\<sigma> \<longlongrightarrow> 1) at_top"
    using sigmoidal_function unfolding sigmoidal_def by simp
  then obtain Ntop where Ntop_def: "\<forall>t \<ge> Ntop. \<bar>\<sigma> t - 1\<bar> < \<epsilon>"
    using eps_pos tendsto_at_top_epsilon_def by blast
  have lim_at_bot: "(\<sigma> \<longlongrightarrow> 0) at_bot"
    using sigmoidal_function unfolding sigmoidal_def by simp
  then obtain Nbot where Nbot_def: "\<forall>t \<le> Nbot. \<bar>\<sigma> t\<bar> < \<epsilon>"
    using eps_pos tendsto_at_bot_epsilon_def by fastforce
  obtain \<omega> where \<omega>_def: "\<omega> = max (max 1 (Ntop / h)) (-Nbot / h)"
    by blast
  then have \<omega>_pos: "0 < \<omega>"
    using h_pos by simp
  show ?thesis
  proof (intro exI[where x = \<omega>] allI impI conjI insert \<omega>_pos)
    fix w :: real and z q :: "(real, 'n) vec" and s :: real
    assume w_ge_\<omega>: "\<omega> \<le> w"
    assume s_cases: "s = 1 \<or> s = -1"
    assume d_ge_h: "norm (z - q) \<ge> h"
    have wh_ge_Ntop: "w * h \<ge> Ntop"
      using \<omega>_def h_pos pos_divide_le_eq w_ge_\<omega> by auto
    have wd_ge_wh: "w * norm (z - q) \<ge> w * h"
      using d_ge_h \<omega>_pos w_ge_\<omega> by (simp add: mult_left_mono)
    then have wd_ge_Ntop: "w * norm (z - q) \<ge> Ntop"
      using wh_ge_Ntop by linarith
    have neg_wh_le_Nbot: "- w * h \<le> Nbot"
    proof -
      have "- Nbot / h \<le> \<omega>"
        unfolding \<omega>_def by (rule max.cobounded2)
      then have "- Nbot / h \<le> w"
        using w_ge_\<omega> by linarith
      then have "- Nbot \<le> w * h"
        by (simp only: pos_divide_le_eq[OF h_pos])
      then have "- (w * h) \<le> Nbot"
        by linarith
      then show ?thesis
        by (simp only: mult_minus_left)
    qed
    then have neg_wd_le_Nbot: "- w * norm (z - q) \<le> Nbot"
      using wd_ge_wh by linarith
    from s_cases show "\<bar>\<sigma> (w * s * norm (z - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
    proof
      assume s1: "s = 1"
      then show ?thesis using Ntop_def wd_ge_Ntop by simp
    next
      assume sm1: "s = -1"
      then have "w * s * norm (z - q) = - w * norm (z - q)" by simp
      then show ?thesis using Nbot_def neg_wd_le_Nbot sm1 by simp
    qed
  qed
qed

text \<open>
  Composing the three \<open>H_1\<close> building blocks for the main sum's "other column" terms
  (\<open>k'\<noteq>k\<close>, any height \<open>j'\<close>, node \<^const>\<open>grid_point\<close>): \<open>column_sign_other_neg\<close> forces the sign
  to \<open>-1\<close>, \<open>z_far_from_other_column\<close> gives the \<open>\<ge>h/2\<close> distance \<open>sigma_inactive_node_bound\<close>
  needs, and the composed conclusion is exactly \<open>|\<sigma>(\<dots>)|<\<epsilon>\<close> -- no residual \<open>-1\<close>, since \<open>s=-1\<close>
  targets \<open>0\<close>.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_saturated_other_column_grid_point:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k k' :: "'n \<Rightarrow> nat" and j' :: nat and z :: "(real, 'n) vec"
  fixes \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  assumes k_range: "k \<in> column_index r0 N" and k'_range: "k' \<in> column_index r0 N"
  assumes k_diff: "r \<noteq> r0" "k' r \<noteq> k r"
  assumes z_in_column: "in_column r0 xs k z"
  shows "\<exists>(\<omega>::real)>0. \<forall>w\<ge>\<omega>. \<bar>\<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar> < \<epsilon>"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  obtain \<omega> where \<omega>_pos: "\<omega> > 0"
    and \<omega>_prop: "\<forall>w\<ge>\<omega>. \<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
    using sigma_inactive_node_bound[OF sigmoidal_function eps_pos, of "h / 2"] hpos by auto
  show ?thesis
  proof (intro exI[where x = \<omega>] conjI \<omega>_pos allI impI)
    fix w :: real assume w_ge: "\<omega> \<le> w"
    have dist: "norm (z - grid_point r0 xs k' j') \<ge> h / 2"
      using z_far_from_other_column[OF a_lt_b N_pos h_def xs_def k_range k'_range k_diff z_in_column] .
    have sign_neg: "column_sign r0 xs k' j' z = -1"
      using column_sign_other_neg[OF a_lt_b N_pos h_def xs_def k_range k'_range k_diff z_in_column] .
    have step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
      using \<omega>_prop[THEN spec[where x = w]] w_ge by simp
    have "\<bar>\<sigma> (w * (-1) * norm (z - grid_point r0 xs k' j')) - (if (-1::real) = 1 then 1 else 0)\<bar> < \<epsilon>"
      using step0[THEN spec[where x = z], THEN spec[where x = "grid_point r0 xs k' j'"],
                  THEN spec[where x = "-1 :: real"]] dist by simp
    then show "\<bar>\<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar> < \<epsilon>"
      using sign_neg by simp
  qed
qed

text \<open>
  The \<open>sigma_anchor\<close> analogue, for the boundary (height \<open>0\<close>) term of the "other column" sum.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_saturated_other_column_anchor:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k k' :: "'n \<Rightarrow> nat" and j' :: nat and z :: "(real, 'n) vec"
  fixes \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  assumes k_range: "k \<in> column_index r0 N" and k'_range: "k' \<in> column_index r0 N"
  assumes k_diff: "r \<noteq> r0" "k' r \<noteq> k r"
  assumes z_in_column: "in_column r0 xs k z"
  shows "\<exists>(\<omega>::real)>0. \<forall>w\<ge>\<omega>. \<bar>\<sigma> (w * column_sign r0 xs k' j' z * norm (z - sigma_anchor r0 xs k' j'))\<bar> < \<epsilon>"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  obtain \<omega> where \<omega>_pos: "\<omega> > 0"
    and \<omega>_prop: "\<forall>w\<ge>\<omega>. \<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
    using sigma_inactive_node_bound[OF sigmoidal_function eps_pos, of "h / 2"] hpos by auto
  show ?thesis
  proof (intro exI[where x = \<omega>] conjI \<omega>_pos allI impI)
    fix w :: real assume w_ge: "\<omega> \<le> w"
    have dist: "norm (z - sigma_anchor r0 xs k' j') \<ge> h / 2"
      using sigma_anchor_far_from_other_column[OF a_lt_b N_pos h_def xs_def k_range k'_range k_diff z_in_column] .
    have sign_neg: "column_sign r0 xs k' j' z = -1"
      using column_sign_other_neg[OF a_lt_b N_pos h_def xs_def k_range k'_range k_diff z_in_column] .
    have step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
      using \<omega>_prop[THEN spec[where x = w]] w_ge by simp
    have "\<bar>\<sigma> (w * (-1) * norm (z - sigma_anchor r0 xs k' j')) - (if (-1::real) = 1 then 1 else 0)\<bar> < \<epsilon>"
      using step0[THEN spec[where x = z], THEN spec[where x = "sigma_anchor r0 xs k' j'"],
                  THEN spec[where x = "-1 :: real"]] dist by simp
    then show "\<bar>\<sigma> (w * column_sign r0 xs k' j' z * norm (z - sigma_anchor r0 xs k' j'))\<bar> < \<epsilon>"
      using sign_neg by simp
  qed
qed

text \<open>
  The full "other column" sum bound for \<open>H_1\<close> (p.183-184's first two printed sums, the double
  and single sums over \<open>i\<noteq>k\<close>):
  assuming \<open>f\<close> is bounded by \<open>M\<close> everywhere (true for any \<open>f\<in>C(Q)\<close> on the compact box, via
  \<open>box_compact\<close>), every term of both the main double sum and the boundary sum is a
  product of a coefficient bounded by \<open>2M\<close> (a difference of two \<open>f\<close>-values, or \<open>M\<close> for the
  single boundary value) and a \<open>\<sigma>\<close>-factor bounded by \<open>\<epsilon>\<close> (\<open>sigma_saturated_other_column_grid_point\<close>/
  \<open>_anchor\<close>), summed over at most \<open>card(column_index r0 N)\<close> columns and \<open>N\<close> heights.
\<close>
text \<open>
  This lemma and its siblings (\<open>multivariate_network_same_column_bound\<close>,
  \<open>multivariate_network_H1_bound\<close>) take the \<open>\<sigma>\<close>-saturation fact \<open>step0\<close> (for a FIXED \<open>w\<close>) as
  an explicit hypothesis, rather than internally deriving an \<open>\<exists>\<omega>>0. \<forall>w\<ge>\<omega>.\<dots>\<close> wrapper via
  \<open>sigma_inactive_node_bound\<close>. This is not merely equivalent to the old shape: it is what lets
  the eventual Theorem 5.1 assembly pick ONE \<open>w\<close> before quantifying over \<open>z\<close> (matching the
  paper's own uniform-approximation claim), since \<open>\<omega>\<close> (hence \<open>step0\<close>) depends only on \<open>\<sigma>\<close>,
  \<open>\<epsilon>\<close>, \<open>h\<close> -- never on \<open>z\<close>/\<open>k\<close>/\<open>j\<close> -- and can therefore be obtained ONCE at the top level and
  reused for every \<open>z\<close>, rather than re-derived (via a fresh, not provably-identical Hilbert-choice
  witness) inside each per-\<open>z\<close> lemma invocation.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_network_other_columns_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and w :: real
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and z :: "(real, 'n) vec"
  fixes \<sigma> :: "real \<Rightarrow> real" and f :: "(real, 'n) vec \<Rightarrow> real" and M Df :: real
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  assumes f_bound: "\<And>p. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> \<bar>f p\<bar> \<le> M"
  assumes Df_nonneg: "0 \<le> Df"
  assumes df_bound: "\<And>k' j'. k' \<in> column_index r0 N \<Longrightarrow> j' \<in> {1..N} \<Longrightarrow>
      \<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> Df"
  assumes k_range: "k \<in> column_index r0 N"
  assumes z_in_column: "in_column r0 xs k z"
  assumes z_in_box: "\<forall>r. z $ r \<in> {a..b}"
  assumes step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
  shows
    "\<bar>(\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
        (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
          * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
     + (\<Sum>k' \<in> column_index r0 N - {k}.
        f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0)))\<bar>
    \<le> real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))
      + real (card (column_index r0 N)) * (M * \<epsilon>)"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have M_nonneg: "M \<ge> 0" using f_bound[OF z_in_box] by simp
  have fin: "finite (column_index r0 N)"
      using finite_column_index .
    text \<open>Per-term bound, main double sum.\<close>
    have main_term_bound: "\<And>k' j'. k' \<in> column_index r0 N \<Longrightarrow> k' \<noteq> k \<Longrightarrow> j' \<in> {1..N} \<Longrightarrow>
        \<bar>(f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
           * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar> \<le> Df * \<epsilon>"
    proof -
      fix k' j' assume k'_range: "k' \<in> column_index r0 N" and k'_neq: "k' \<noteq> k" and j'_range: "j' \<in> {1..N}"
      obtain r where r_ne: "r \<noteq> r0" and k_diff: "k' r \<noteq> k r"
        using column_index_neq_witness[OF k_range k'_range k'_neq] by blast
      have dist: "norm (z - grid_point r0 xs k' j') \<ge> h / 2"
        using z_far_from_other_column[OF a_lt_b N_pos h_def xs_def k_range k'_range r_ne k_diff z_in_column] .
      have sign_neg: "column_sign r0 xs k' j' z = -1"
        using column_sign_other_neg[OF a_lt_b N_pos h_def xs_def k_range k'_range r_ne k_diff z_in_column] .
      have sig_bound: "\<bar>\<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar> < \<epsilon>"
      proof -
        have "\<bar>\<sigma> (w * (-1) * norm (z - grid_point r0 xs k' j')) - (if (-1::real) = 1 then 1 else 0)\<bar> < \<epsilon>"
          using step0[THEN spec[where x = z], THEN spec[where x = "grid_point r0 xs k' j'"],
                      THEN spec[where x = "-1 :: real"]] dist by simp
        then show ?thesis using sign_neg by simp
      qed
      have j'_box_range: "j' \<in> {0..N}" and jm1_box_range: "j' - 1 \<in> {0..N}"
        using j'_range by auto
      have box1: "\<forall>r. sample_point r0 xs k' j' $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j'_box_range k'_range] .
      have box2: "\<forall>r. sample_point r0 xs k' (j' - 1) $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def jm1_box_range k'_range] .
      have coeff_bound: "\<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> Df"
        using df_bound[OF k'_range j'_range] .
      have "\<bar>(f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
               * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar>
          = \<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar>
            * \<bar>\<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> Df * \<epsilon>"
        using coeff_bound sig_bound Df_nonneg mult_mono[OF coeff_bound less_imp_le[OF sig_bound]] by simp
      finally show "\<bar>(f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
           * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar> \<le> Df * \<epsilon>" .
    qed
    text \<open>Per-term bound, boundary sum.\<close>
    have boundary_term_bound: "\<And>k'. k' \<in> column_index r0 N \<Longrightarrow> k' \<noteq> k \<Longrightarrow>
        \<bar>f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>
          \<le> M * \<epsilon>"
    proof -
      fix k' assume k'_range: "k' \<in> column_index r0 N" and k'_neq: "k' \<noteq> k"
      obtain r where r_ne: "r \<noteq> r0" and k_diff: "k' r \<noteq> k r"
        using column_index_neq_witness[OF k_range k'_range k'_neq] by blast
      have dist: "norm (z - sigma_anchor r0 xs k' 0) \<ge> h / 2"
        using sigma_anchor_far_from_other_column[OF a_lt_b N_pos h_def xs_def k_range k'_range r_ne k_diff z_in_column] .
      have sign_neg: "column_sign r0 xs k' 0 z = -1"
        using column_sign_other_neg[OF a_lt_b N_pos h_def xs_def k_range k'_range r_ne k_diff z_in_column] .
      have sig_bound: "\<bar>\<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar> < \<epsilon>"
      proof -
        have "\<bar>\<sigma> (w * (-1) * norm (z - sigma_anchor r0 xs k' 0)) - (if (-1::real) = 1 then 1 else 0)\<bar> < \<epsilon>"
          using step0[THEN spec[where x = z], THEN spec[where x = "sigma_anchor r0 xs k' 0"],
                      THEN spec[where x = "-1 :: real"]] dist by simp
        then show ?thesis using sign_neg by simp
      qed
      have zero_box_range: "(0::nat) \<in> {0..N}" by simp
      have box0: "\<forall>r. sample_point r0 xs k' 0 $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def zero_box_range k'_range] .
      have coeff_bound: "\<bar>f (sample_point r0 xs k' 0)\<bar> \<le> M"
        using f_bound[OF box0] .
      have "\<bar>f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>
          = \<bar>f (sample_point r0 xs k' 0)\<bar>
            * \<bar>\<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> M * \<epsilon>"
        using mult_mono[OF coeff_bound less_imp_le[OF sig_bound]] M_nonneg by simp
      finally show "\<bar>f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>
          \<le> M * \<epsilon>" .
    qed
    text \<open>Assemble via the triangle inequality and \<open>sum_mono\<close>.\<close>
    have main_sum_bound: "\<bar>\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
        (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
          * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar>
      \<le> real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))"
    proof -
      have "\<bar>\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
              (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
                * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar>
          \<le> (\<Sum>k' \<in> column_index r0 N - {k}. \<bar>\<Sum>j' \<in> {1..N}.
              (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
                * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar>)"
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>k' \<in> column_index r0 N - {k}. (\<Sum>j' \<in> {1..N}.
              \<bar>(f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
                * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))\<bar>))"
        by (intro sum_mono sum_abs)
      also have "\<dots> \<le> (\<Sum>k' \<in> column_index r0 N - {k}. (\<Sum>j' \<in> {1..N}. Df * \<epsilon>))"
        using main_term_bound by (intro sum_mono) auto
      also have "\<dots> = (\<Sum>k' \<in> column_index r0 N - {k}. real N * (Df * \<epsilon>))"
        by simp
      also have "\<dots> = real (card (column_index r0 N - {k})) * (real N * (Df * \<epsilon>))"
        by simp
      also have "\<dots> \<le> real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))"
        using fin Df_nonneg eps_pos
        by (intro mult_right_mono of_nat_mono card_mono) auto
      finally show ?thesis .
    qed
    have boundary_sum_bound: "\<bar>\<Sum>k' \<in> column_index r0 N - {k}.
        f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>
      \<le> real (card (column_index r0 N)) * (M * \<epsilon>)"
    proof -
      have "\<bar>\<Sum>k' \<in> column_index r0 N - {k}.
              f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>
          \<le> (\<Sum>k' \<in> column_index r0 N - {k}.
              \<bar>f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))\<bar>)"
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>k' \<in> column_index r0 N - {k}. M * \<epsilon>)"
        using boundary_term_bound by (intro sum_mono) auto
      also have "\<dots> = real (card (column_index r0 N - {k})) * (M * \<epsilon>)"
        by simp
      also have "\<dots> \<le> real (card (column_index r0 N)) * (M * \<epsilon>)"
        using fin M_nonneg eps_pos
        by (intro mult_right_mono of_nat_mono card_mono) auto
      finally show ?thesis .
    qed
    have "\<bar>(\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
        (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
          * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
     + (\<Sum>k' \<in> column_index r0 N - {k}.
        f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0)))\<bar>
      \<le> real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))
        + real (card (column_index r0 N)) * (M * \<epsilon>)"
      using main_sum_bound boundary_sum_bound by argo
    then show ?thesis .
qed

text \<open>
  The saturation composition needed for the SAME column's inactive heights (any height \<open>j'\<close>
  other than the active \<open>j\<close>): unlike
  \<open>sigma_saturated_other_column_grid_point\<close>/\<open>_anchor\<close>, \<open>column_sign\<close> is NOT forced to a fixed
  value here -- it genuinely varies with \<open>j'\<close> (\<open>+1\<close> when \<open>z\<close> is past height \<open>j'\<close>, \<open>-1\<close>
  otherwise), exactly matching the paper's own telescoping-weight selector \<open>\<chi>\<close> role. So the target
  \<open>\<sigma>\<close> saturates toward is whichever of \<open>0\<close>/\<open>1\<close> \<open>column_sign\<close> itself selects
  (\<open>column_sign_cases\<close>), not always \<open>0\<close> -- this is the exact fact the eventual telescoping
  identity (mirroring \<open>forward_diff_one_I1_generic_bound\<close>, Section 4) will need at each
  inactive height.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma sigma_saturated_same_column_diff_height:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j j' :: nat and z :: "(real, 'n) vec"
  fixes \<sigma> :: "real \<Rightarrow> real"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  assumes j_range: "j \<in> {1..N}" and j'_range: "j' \<in> {0..N}"
  assumes j_diff: "j' \<noteq> j"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  shows "\<exists>(\<omega>::real) > 0. \<forall>w \<ge> \<omega>.
    \<bar>\<sigma> (w * column_sign r0 xs k j' z * norm (z - sigma_anchor r0 xs k j'))
       - (if column_sign r0 xs k j' z = 1 then 1 else 0)\<bar> < \<epsilon>"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  obtain \<omega> where \<omega>_pos: "\<omega> > 0"
    and \<omega>_prop: "\<forall>w\<ge>\<omega>. \<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
    using sigma_inactive_node_bound[OF sigmoidal_function eps_pos, of "h / 2"] hpos by auto
  show ?thesis
  proof (intro exI[where x = \<omega>] conjI \<omega>_pos allI impI)
    fix w :: real assume w_ge: "\<omega> \<le> w"
    have dist: "norm (z - sigma_anchor r0 xs k j') \<ge> h / 2"
      using z_far_same_column_diff_height[OF a_lt_b N_pos h_def xs_def j_range j'_range j_diff z_height] .
    have sign_cases: "column_sign r0 xs k j' z = 1 \<or> column_sign r0 xs k j' z = -1"
      using column_sign_cases .
    have step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
      using \<omega>_prop[THEN spec[where x = w]] w_ge by simp
    show "\<bar>\<sigma> (w * column_sign r0 xs k j' z * norm (z - sigma_anchor r0 xs k j'))
             - (if column_sign r0 xs k j' z = 1 then 1 else 0)\<bar> < \<epsilon>"
      using step0[THEN spec[where x = z], THEN spec[where x = "sigma_anchor r0 xs k j'"],
                  THEN spec[where x = "column_sign r0 xs k j' z"]] sign_cases dist by simp
  qed
qed

text \<open>
  The same-column telescoping identity: mirroring \<open>forward_diff_one_I1_generic_bound\<close>
  (Section 4), but SIMPLER, since \<^const>\<open>local_proxy\<close> has only ONE active \<open>\<sigma>\<close>-step (not two --
  see its own comment), and \<open>sample_point_telescope\<close> already handles height \<open>0\<close> uniformly
  (no boundary-index complications like \<open>Gj_network\<close>'s missing \<open>\<Delta>\<^sup>1_{N+1}f\<close> term forced in
  Section 4). The \<open>f\<close>-coefficients always use \<^const>\<open>grid_point\<close> (matching
  \<^const>\<open>multivariate_network\<close>'s own literal syntax, height \<open>0\<close> included -- \<^const>\<open>sigma_anchor\<close>
  is never the point \<open>f\<close> is evaluated at); only the \<open>\<sigma>\<close>-distance argument at height \<open>0\<close> uses
  \<^const>\<open>sigma_anchor\<close> (elsewhere the two coincide, \<open>sigma_anchor_eq_grid_point\<close>, but writing
  \<^const>\<open>grid_point\<close> in the distance argument for \<open>j'\<ge>1\<close> keeps this an EXACT statement of
  \<^const>\<open>multivariate_network\<close>'s own main-sum term, not merely an equal one).
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_network_column_telescoping:
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat and z :: "(real, 'n) vec"
  fixes xs :: "real list" and \<sigma> :: "real \<Rightarrow> real" and f :: "(real, 'n) vec \<Rightarrow> real" and w :: real
  assumes j_range: "j \<in> {1..N}"
  shows "(\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
       + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
       - (f (sample_point r0 xs k (j - 1))
          + (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
            * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)))
     = (\<Sum>j' = 1..j - 1. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1))
     + f (sample_point r0 xs k 0)
         * (\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1)
     + (\<Sum>j' = j + 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))"
proof -
  define Df where "Df = (\<lambda>m. f (sample_point r0 xs k m))"
  define trm where "trm = (\<lambda>j'. (Df j' - Df (j' - 1))
                                     * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))"
  have j_pos: "j \<ge> 1" and j_leq: "j \<le> N" using j_range by auto
  text \<open>Telescoping: the raw sum up to \<open>j-1\<close>, plus \<open>Df 0\<close>, collapses to \<open>Df(j-1)\<close>.\<close>
  have telescope: "(\<Sum>j' = 1..j - 1. Df j' - Df (j' - 1)) + Df 0 = Df (j - 1)"
    unfolding Df_def using sample_point_telescope by simp
  text \<open>Split \<open>{1..N}\<close> into \<open>{1..j-1}\<close>, \<open>{j}\<close>, \<open>{j+1..N}\<close>.\<close>
  have split1: "{1..N} = {1..j - 1} \<union> {j..N}"
    using j_pos j_leq by auto
  have disjoint1: "{1..j - 1} \<inter> {j..N} = {}"
    by auto
  have fin1: "finite {1..j - 1}" and fin2: "finite {j..N}" by auto
  have sum_split: "(\<Sum>j' = 1..N. trm j') = (\<Sum>j' = 1..j - 1. trm j') + (\<Sum>j' = j..N. trm j')"
    using split1 sum.union_disjoint[OF fin1 fin2 disjoint1] by simp
  have peel_j: "(\<Sum>j' = j..N. trm j') = trm j + (\<Sum>j' = j + 1..N. trm j')"
    using j_leq by (subst sum.atLeast_Suc_atMost) auto
  have term_j_eq: "trm j = (Df j - Df (j - 1)) * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j))"
    unfolding trm_def by simp
  have step1: "(\<Sum>j' = 1..N. trm j') + Df 0 * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
      - (Df (j - 1) + (Df j - Df (j - 1)) * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)))
    = ((\<Sum>j' = 1..j - 1. trm j') - (\<Sum>j' = 1..j - 1. Df j' - Df (j' - 1)))
      + Df 0 * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - Df 0
      + (\<Sum>j' = j + 1..N. trm j')"
    unfolding sum_split peel_j term_j_eq telescope[symmetric] by simp
  have factor1: "(\<Sum>j' = 1..j - 1. trm j') - (\<Sum>j' = 1..j - 1. Df j' - Df (j' - 1))
      = (\<Sum>j' = 1..j - 1. (Df j' - Df (j' - 1))
           * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1))"
    unfolding trm_def by (simp add: sum_subtractf right_diff_distrib')
  have factor2: "Df 0 * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - Df 0
      = Df 0 * (\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1)"
    by (simp add: right_diff_distrib')
  have step2: "(\<Sum>j' = 1..N. trm j') + Df 0 * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
      - (Df (j - 1) + (Df j - Df (j - 1)) * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)))
    = (\<Sum>j' = 1..j - 1. (Df j' - Df (j' - 1)) * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1))
      + Df 0 * (\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1)
      + (\<Sum>j' = j + 1..N. trm j')"
    unfolding step1 factor1[symmetric] factor2[symmetric] by simp
  show ?thesis
    using step2 unfolding Df_def trm_def by simp
qed

text \<open>
  Unlike \<open>column_sign_other_neg\<close> (always \<open>-1\<close> for a different column), within the SAME column
  \<open>column_sign\<close> at a height \<open>j'\<close> below the active height \<open>j\<close> is always \<open>+1\<close> -- exactly the
  telescoping-weight-\<open>1\<close> role the paper's own \<open>\<chi>\<close> plays for already-summed heights.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_sign_same_column_below:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {1..N}" and j'_lt: "j' < j"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  assumes z_in_column: "in_column r0 xs k z"
  shows "column_sign r0 xs k j' z = 1"
proof -
  have le: "j' + 1 \<le> j" using j'_lt by simp
  have jp1_N1: "j' + 1 \<in> {1..N + 1}" and j_N1: "j \<in> {1..N + 1}"
    using j'_lt j_range by auto
  have mono: "xs ! (j' + 1) \<le> xs ! j"
    using list_increasing[OF a_lt_b N_pos h_def xs_def] jp1_N1 j_N1 le by blast
  have "z $ r0 \<ge> xs ! (j' + 1)"
    using z_height mono by auto
  then show ?thesis
    using z_in_column unfolding column_sign_def by simp
qed

text \<open>The companion fact: above the active height, \<open>column_sign\<close> is always \<open>-1\<close>.\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_sign_same_column_above:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {1..N}" and j'_range: "j' \<in> {j<..N}"
  shows "\<not> (z $ r0 \<ge> xs ! (j' + 1)) \<or> \<not> (z $ r0 \<in> {xs ! j .. xs ! (j + 1)})"
proof (rule ccontr)
  assume "\<not> (\<not> (z $ r0 \<ge> xs ! (j' + 1)) \<or> \<not> (z $ r0 \<in> {xs ! j .. xs ! (j + 1)}))"
  then have contra: "z $ r0 \<ge> xs ! (j' + 1)" "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}" by auto
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have j'_gt: "j' > j" and j'_leq: "j' \<le> N" using j'_range by auto
  have le: "j + 2 \<le> j' + 1" using j'_gt by simp
  have jp2_N1: "j + 2 \<in> {1..N + 1}" and jp1'_N1: "j' + 1 \<in> {1..N + 1}"
    using j_range j'_gt j'_leq by auto
  have mono: "xs ! (j + 2) \<le> xs ! (j' + 1)"
    using list_increasing[OF a_lt_b N_pos h_def xs_def] jp2_N1 jp1'_N1 le by blast
  have step: "xs ! (j + 2) - xs ! (j + 1) = h"
    using difference_of_adj_terms[OF h_def xs_def, of "j + 2"] jp2_N1 by auto
  have "z $ r0 \<le> xs ! (j + 1)" using contra(2) by simp
  moreover have "xs ! (j + 1) < xs ! (j + 2)" using step hpos by simp
  ultimately have "z $ r0 < xs ! (j' + 1)" using mono by simp
  then show False using contra(1) by simp
qed

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
corollary column_sign_same_column_above':
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j j' :: nat and z :: "(real, 'n) vec"
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes j_range: "j \<in> {1..N}" and j'_range: "j' \<in> {j<..N}"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  shows "column_sign r0 xs k j' z = -1"
  using column_sign_same_column_above[OF a_lt_b N_pos h_def xs_def j_range j'_range] z_height
  unfolding column_sign_def by auto

text \<open>
  The numeric same-column bound for \<open>H_1\<close>: combines the telescoping identity
  (\<open>multivariate_network_column_telescoping\<close>) with the determinate signs
  (\<open>column_sign_same_column_below\<close>/\<open>_above\<close>) and \<open>sigma_saturated_same_column_diff_height\<close>
  into a single \<open>M\<epsilon>\<close>-scale bound, mirroring \<open>forward_diff_one_I1_generic_eta_bound\<close> from
  Section 4.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_network_same_column_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and w :: real
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat and z :: "(real, 'n) vec"
  fixes \<sigma> :: "real \<Rightarrow> real" and f :: "(real, 'n) vec \<Rightarrow> real" and M Df :: real
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  assumes f_bound: "\<And>p. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> \<bar>f p\<bar> \<le> M"
  assumes Df_nonneg: "0 \<le> Df"
  assumes df_bound: "\<And>j'. j' \<in> {1..N} \<Longrightarrow>
      \<bar>f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1))\<bar> \<le> Df"
  assumes k_range: "k \<in> column_index r0 N"
  assumes j_range: "j \<in> {1..N}"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  assumes z_in_column: "in_column r0 xs k z"
  assumes z_in_box: "\<forall>r. z $ r \<in> {a..b}"
  assumes step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
  shows
    "\<bar>(\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
       + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
       - local_proxy r0 xs k j \<sigma> f w z\<bar>
    \<le> (real N - 1) * (Df * \<epsilon>) + M * \<epsilon>"
proof -
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
  have M_nonneg: "M \<ge> 0" using f_bound[OF z_in_box] by simp
  text \<open>Per-term bound below the active height.\<close>
    have below_bound: "\<And>j'. 0 < j' \<Longrightarrow> j' < j \<Longrightarrow>
        \<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1)\<bar> \<le> Df * \<epsilon>"
    proof -
      fix j' :: nat assume j'_pos: "0 < j'" and j'_lt: "j' < j"
      have j'_N: "j' \<in> {0..N}" using j'_lt j_range by auto
      have j_diff: "j' \<noteq> j" using j'_lt by simp
      have dist: "norm (z - sigma_anchor r0 xs k j') \<ge> h / 2"
        using z_far_same_column_diff_height[OF a_lt_b N_pos h_def xs_def j_range j'_N j_diff z_height] .
      have anchor_eq: "sigma_anchor r0 xs k j' = grid_point r0 xs k j'"
        using sigma_anchor_eq_grid_point[of j' r0 xs k] j'_pos by simp
      have sign1: "column_sign r0 xs k j' z = 1"
        using column_sign_same_column_below[OF a_lt_b N_pos h_def xs_def j_range j'_lt z_height z_in_column] .
      have sig_bound: "\<bar>\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1\<bar> < \<epsilon>"
        using step0[THEN spec[where x = z], THEN spec[where x = "sigma_anchor r0 xs k j'"],
                    THEN spec[where x = "1 :: real"]] dist sign1 anchor_eq by simp
      have jm1_N: "j' - 1 \<in> {0..N}" using j'_N by auto
      have box1: "\<forall>r. sample_point r0 xs k j' $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j'_N k_range] .
      have box2: "\<forall>r. sample_point r0 xs k (j' - 1) $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def jm1_N k_range] .
      have j'_1N: "j' \<in> {1..N}" using j'_N j'_pos by auto
      have coeff_bound: "\<bar>f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1))\<bar> \<le> Df"
        using df_bound[OF j'_1N] .
      have "\<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
               * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1)\<bar>
          = \<bar>f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1))\<bar>
            * \<bar>\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> Df * \<epsilon>"
        using mult_mono[OF coeff_bound less_imp_le[OF sig_bound]] M_nonneg Df_nonneg by simp
      finally show "\<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1)\<bar> \<le> Df * \<epsilon>" .
    qed
    text \<open>Boundary term (height \<open>0\<close>, always below the active height since \<open>j\<ge>1\<close>).\<close>
    have boundary_bound: "\<bar>f (sample_point r0 xs k 0)
        * (\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1)\<bar> \<le> M * \<epsilon>"
    proof -
      have j'_N: "(0::nat) \<in> {0..N}" by simp
      have j_diff: "(0::nat) \<noteq> j" using j_range by simp
      have dist: "norm (z - sigma_anchor r0 xs k 0) \<ge> h / 2"
        using z_far_same_column_diff_height[OF a_lt_b N_pos h_def xs_def j_range j'_N j_diff z_height] .
      have sign1: "column_sign r0 xs k 0 z = 1"
        using column_sign_same_column_below[OF a_lt_b N_pos h_def xs_def j_range _ z_height z_in_column]
              j_range by simp
      have sig_bound: "\<bar>\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1\<bar> < \<epsilon>"
        using step0[THEN spec[where x = z], THEN spec[where x = "sigma_anchor r0 xs k 0"],
                    THEN spec[where x = "1 :: real"]] dist sign1 by simp
      have box0: "\<forall>r. sample_point r0 xs k 0 $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j'_N k_range] .
      have coeff_bound: "\<bar>f (sample_point r0 xs k 0)\<bar> \<le> M"
        using f_bound[OF box0] .
      have "\<bar>f (sample_point r0 xs k 0)
               * (\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1)\<bar>
          = \<bar>f (sample_point r0 xs k 0)\<bar>
            * \<bar>\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> M * \<epsilon>"
        using mult_mono[OF coeff_bound less_imp_le[OF sig_bound]] M_nonneg Df_nonneg by simp
      finally show ?thesis .
    qed
    text \<open>Per-term bound above the active height.\<close>
    have above_bound: "\<And>j'. j' > j \<Longrightarrow> j' \<le> N \<Longrightarrow>
        \<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar> \<le> Df * \<epsilon>"
    proof -
      fix j' :: nat assume j'_gt: "j' > j" and j'_leq: "j' \<le> N"
      have j'_N: "j' \<in> {0..N}" using j'_gt j'_leq by auto
      have j'_range': "j' \<in> {j<..N}" using j'_gt j'_leq by auto
      have j_diff: "j' \<noteq> j" using j'_gt by simp
      have dist: "norm (z - sigma_anchor r0 xs k j') \<ge> h / 2"
        using z_far_same_column_diff_height[OF a_lt_b N_pos h_def xs_def j_range j'_N j_diff z_height] .
      have anchor_eq: "sigma_anchor r0 xs k j' = grid_point r0 xs k j'"
        using sigma_anchor_eq_grid_point[of j' r0 xs k] j'_gt j_range by simp
      have signm1: "column_sign r0 xs k j' z = -1"
        using column_sign_same_column_above'[OF a_lt_b N_pos h_def xs_def j_range j'_range' z_height] .
      have sig_bound: "\<bar>\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar> < \<epsilon>"
        using step0[THEN spec[where x = z], THEN spec[where x = "sigma_anchor r0 xs k j'"],
                    THEN spec[where x = "-1 :: real"]] dist signm1 anchor_eq by simp
      have jm1_N: "j' - 1 \<in> {0..N}" using j'_N by auto
      have box1: "\<forall>r. sample_point r0 xs k j' $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j'_N k_range] .
      have box2: "\<forall>r. sample_point r0 xs k (j' - 1) $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def jm1_N k_range] .
      have j'_1N: "j' \<in> {1..N}" using j'_N j'_gt j_range by auto
      have coeff_bound: "\<bar>f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1))\<bar> \<le> Df"
        using df_bound[OF j'_1N] .
      have "\<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
               * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar>
          = \<bar>f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1))\<bar>
            * \<bar>\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> Df * \<epsilon>"
        using mult_mono[OF coeff_bound less_imp_le[OF sig_bound]] M_nonneg Df_nonneg by simp
      finally show "\<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar> \<le> Df * \<epsilon>" .
    qed
    text \<open>Sum both ranges.\<close>
    have below_sum: "\<bar>\<Sum>j' = 1..j - 1. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
        * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1)\<bar>
      \<le> real (j - 1) * (Df * \<epsilon>)"
    proof -
      have "\<bar>\<Sum>j' = 1..j - 1. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1)\<bar>
          \<le> (\<Sum>j' = 1..j - 1. \<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1)\<bar>)"
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>j' = 1..j - 1. Df * \<epsilon>)"
        using below_bound by (intro sum_mono) auto
      also have "\<dots> = real (j - 1) * (Df * \<epsilon>)"
        by simp
      finally show ?thesis .
    qed
    have above_sum: "\<bar>\<Sum>j' = j + 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
        * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar>
      \<le> real (N - j) * (Df * \<epsilon>)"
    proof -
      have "\<bar>\<Sum>j' = j + 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar>
          \<le> (\<Sum>j' = j + 1..N. \<bar>(f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j'))\<bar>)"
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>j' = j + 1..N. Df * \<epsilon>)"
        using above_bound by (intro sum_mono) auto
      also have "\<dots> = real (N - j) * (Df * \<epsilon>)"
        by simp
      finally show ?thesis .
    qed
    text \<open>Combine via the telescoping identity.\<close>
    have telescoping: "(\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
       + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
       - local_proxy r0 xs k j \<sigma> f w z
     = (\<Sum>j' = 1..j - 1. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * (\<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')) - 1))
     + f (sample_point r0 xs k 0)
         * (\<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)) - 1)
     + (\<Sum>j' = j + 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
           * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))"
      using multivariate_network_column_telescoping[OF j_range] unfolding local_proxy_def by simp
    have "\<bar>(\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
       + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
       - local_proxy r0 xs k j \<sigma> f w z\<bar>
      \<le> real (j - 1) * (Df * \<epsilon>) + M * \<epsilon> + real (N - j) * (Df * \<epsilon>)"
      unfolding telescoping using below_sum boundary_bound above_sum by argo
    also have "\<dots> = (real N - 1) * (Df * \<epsilon>) + M * \<epsilon>"
    proof -
      have "real (j - 1) + real (N - j) = real N - 1"
        using j_range by simp
      then show ?thesis by (simp add: algebra_simps)
    qed
    finally show ?thesis .
qed

text \<open>
  The full \<open>H_1\<close> bound: \<^const>\<open>multivariate_network\<close>'s own two outer sums (over ALL of
  \<^const>\<open>column_index\<close>) split into the active column \<open>k\<close> (\<open>multivariate_network_same_column_bound\<close>,
  vs. \<^const>\<open>local_proxy\<close>) and every other column (\<open>multivariate_network_other_columns_bound\<close>),
  via \<open>sum.remove\<close>; combining both bounds by the triangle inequality closes \<open>H_1\<close> itself.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_network_H1_bound:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list" and w :: real
  fixes r0 :: "'n::finite" and k :: "'n \<Rightarrow> nat" and j :: nat and z :: "(real, 'n) vec"
  fixes \<sigma> :: "real \<Rightarrow> real" and f :: "(real, 'n) vec \<Rightarrow> real" and M Df :: real
  assumes a_lt_b: "a < b" and N_pos: "N > 0"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  assumes f_bound: "\<And>p. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> \<bar>f p\<bar> \<le> M"
  assumes Df_nonneg: "0 \<le> Df"
  assumes df_bound: "\<And>k' j'. k' \<in> column_index r0 N \<Longrightarrow> j' \<in> {1..N} \<Longrightarrow>
      \<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> Df"
  assumes k_range: "k \<in> column_index r0 N"
  assumes j_range: "j \<in> {1..N}"
  assumes z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
  assumes z_in_column: "in_column r0 xs k z"
  assumes z_in_box: "\<forall>r. z $ r \<in> {a..b}"
  assumes step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                   norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>"
  shows
    "\<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
    \<le> (real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))
          + real (card (column_index r0 N)) * (M * \<epsilon>))
        + ((real N - 1) * (Df * \<epsilon>) + M * \<epsilon>)"
proof -
  have \<omega>1_prop:
      "\<bar>(\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
          (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
       + (\<Sum>k' \<in> column_index r0 N - {k}.
          f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0)))\<bar>
      \<le> real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))
        + real (card (column_index r0 N)) * (M * \<epsilon>)"
    using multivariate_network_other_columns_bound[OF a_lt_b N_pos h_def xs_def
      eps_pos f_bound Df_nonneg df_bound k_range z_in_column z_in_box step0] .
  have \<omega>2_prop:
      "\<bar>(\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
         + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
         - local_proxy r0 xs k j \<sigma> f w z\<bar>
      \<le> (real N - 1) * (Df * \<epsilon>) + M * \<epsilon>"
    using multivariate_network_same_column_bound[OF a_lt_b N_pos h_def xs_def
      eps_pos f_bound Df_nonneg df_bound[OF k_range] k_range j_range z_height
      z_in_column z_in_box step0] .
    have fin: "finite (column_index r0 N)" using finite_column_index .
    have split_main: "(\<Sum>k' \<in> column_index r0 N. \<Sum>j' \<in> {1..N}.
          (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
        = (\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
              (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
                * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
          + (\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))"
      using sum.remove[OF fin k_range, of "\<lambda>k'. \<Sum>j' \<in> {1..N}.
          (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
            * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j'))"]
      by simp
    have split_boundary: "(\<Sum>k' \<in> column_index r0 N.
          f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0)))
        = (\<Sum>k' \<in> column_index r0 N - {k}.
              f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0)))
          + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))"
      using sum.remove[OF fin k_range, of "\<lambda>k'. f (sample_point r0 xs k' 0)
          * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))"]
      by simp
    have net_eq: "multivariate_network \<sigma> f r0 xs N w z
        = ((\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
              (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
                * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
           + (\<Sum>k' \<in> column_index r0 N - {k}.
              f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0))))
          + ((\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
           + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)))"
      unfolding multivariate_network_def split_main split_boundary by simp
    have "\<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
        \<le> \<bar>(\<Sum>k' \<in> column_index r0 N - {k}. \<Sum>j' \<in> {1..N}.
              (f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1)))
                * \<sigma> (w * column_sign r0 xs k' j' z * norm (z - grid_point r0 xs k' j')))
           + (\<Sum>k' \<in> column_index r0 N - {k}.
              f (sample_point r0 xs k' 0) * \<sigma> (w * column_sign r0 xs k' 0 z * norm (z - sigma_anchor r0 xs k' 0)))\<bar>
          + \<bar>(\<Sum>j' = 1..N. (f (sample_point r0 xs k j') - f (sample_point r0 xs k (j' - 1)))
              * \<sigma> (w * column_sign r0 xs k j' z * norm (z - grid_point r0 xs k j')))
             + f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0))
             - local_proxy r0 xs k j \<sigma> f w z\<bar>"
      unfolding net_eq by argo
    also have "\<dots> \<le> (real (card (column_index r0 N)) * (real N * (Df * \<epsilon>))
                        + real (card (column_index r0 N)) * (M * \<epsilon>))
                     + ((real N - 1) * (Df * \<epsilon>) + M * \<epsilon>)"
      using \<omega>1_prop \<omega>2_prop by (intro add_mono) auto
    finally show ?thesis .
qed

text \<open>
  Theorem 5.1 itself: choosing \<open>N\<close> and \<open>w\<close> so that the network approximates \<open>f\<close> to within
  \<open>\<epsilon>\<close> uniformly over the whole box. The preamble mirrors \<open>forward_diff_one_approximation_preamble\<close>
  (theory \<open>Simultaneous_Approximation\<close>): \<open>\<eta>\<close> chosen from \<open>\<epsilon>\<close> and \<open>S:=\<close>sup\<open>|\<sigma>|\<close> so that \<open>(1+S)\<eta><\<epsilon>/2\<close>
  (\<open>H_2\<close>'s own bound, \<open>multivariate_H2_bound\<close>), \<open>\<delta>\<close> from \<open>f\<close>'s uniform continuity on the box at
  \<open>\<eta>\<close>, \<open>N\<close> large enough for the mesh condition \<open>h*CARD('n)<\<delta>\<close> that \<open>H_2\<close> needs, \<open>M\<close> from
  \<open>f\<close>'s boundedness on the box, \<open>\<epsilon>'\<close> chosen so that \<open>H_1\<close>'s own bound (which does not depend on
  \<open>N\<close> having any particular closed-form column count -- \<open>multivariate_network_H1_bound\<close> is
  stated for an arbitrary \<open>N\<close>) is \<open><\<epsilon>/2\<close>, and finally \<open>w\<close> from the \<open>\<sigma>\<close>-saturation threshold at
  \<open>\<epsilon>'\<close> and \<open>h/2\<close> (\<open>sigma_inactive_node_bound\<close>). For each \<open>z\<close> in the box, \<open>exists_column_and_height\<close>
  locates the active column \<open>k\<close> and height \<open>j\<close>, and \<open>H_1\<close> + \<open>H_2\<close> combine via the triangle
  inequality to give \<open><\<epsilon>/2+\<epsilon>/2=\<epsilon>\<close>.
\<close>
(* Theorem 5.1: endpoint-sampling operator of equation (5.1). *)
theorem multivariate_uniform_approximation:
  fixes a b :: real and f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: "'n::finite"
  fixes \<sigma> :: "real \<Rightarrow> real"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes a_lt_b: "a < b"
  assumes f_cont_on: "continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"
  assumes eps_pos: "(\<epsilon> :: real) > 0"
  shows "\<exists>N w. N > 0 \<and> w > 0 \<and>
           (\<forall>z. (\<forall>r. z $ r \<in> {a..b}) \<longrightarrow>
              \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z\<bar> < \<epsilon>)"
proof -
  text \<open>\<open>S\<close>, the sup of \<open>|\<sigma>|\<close>, and \<open>\<eta>\<close> chosen so that \<open>(1+S)\<eta><\<epsilon>/2\<close> (\<open>H_2\<close>'s bound).\<close>
  define S where "S = Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV)"
  have S_nonneg: "S \<ge> 0"
    using bounded_sigmoidal unfolding S_def bounded_function_def
    by (meson UNIV_I abs_ge_zero cSUP_upper2)

  define \<eta> where "\<eta> = \<epsilon> / (2 * (S + 2))"
  have \<eta>_pos: "\<eta> > 0"
    unfolding \<eta>_def using eps_pos S_nonneg by simp

  text \<open>\<open>\<delta>\<close>, from \<open>f\<close>'s uniform continuity on the box at \<open>\<eta>\<close>.\<close>
  obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and \<delta>_prop: "\<forall>p q. (\<forall>r. p $ r \<in> {a..b}) \<longrightarrow> (\<forall>r. q $ r \<in> {a..b}) \<longrightarrow> norm (p - q) < \<delta>
                   \<longrightarrow> \<bar>f p - f q\<bar> < \<eta>"
    using multivariate_uniform_continuity_box[OF f_cont_on \<eta>_pos] by blast

  text \<open>\<open>N\<close>, large enough that \<open>h=(b-a)/N\<close> satisfies the mesh condition \<open>h*CARD('n)<\<delta>\<close>.\<close>
  define X where "X = (b - a) * real CARD('n) / \<delta>"
  define N where "N = nat \<lfloor>X\<rfloor> + 1"
  have X_nonneg: "X \<ge> 0"
    unfolding X_def using a_lt_b \<delta>_pos by simp
  have N_gt_X: "real N > X"
  proof -
    have "real (nat \<lfloor>X\<rfloor>) = real_of_int \<lfloor>X\<rfloor>"
      using X_nonneg by simp
    then have "real N = real_of_int \<lfloor>X\<rfloor> + 1"
      unfolding N_def by simp
    then show ?thesis
      using floor_correct[of X] by linarith
  qed
  have N_pos: "N > 0" unfolding N_def by simp

  define xs where "xs = unif_part a b N"
  define h where "h = (b - a) / N"
  have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .

  have h_lt: "h * real CARD('n) < \<delta>"
    using N_gt_X N_pos \<delta>_pos unfolding X_def h_def
    by (simp add: pos_divide_less_eq field_simps)

  text \<open>\<open>M\<close>, a bound on \<open>|f|\<close> over the box.\<close>
  obtain M where M_prop: "\<forall>p. (\<forall>r. p $ r \<in> {a..b}) \<longrightarrow> \<bar>f p\<bar> \<le> M"
    using f_bounded_on_box[OF f_cont_on] by blast
  define z0 :: "(real, 'n) vec" where "z0 = (\<chi> r. a)"
  have z0_in_box: "\<forall>r. z0 $ r \<in> {a..b}"
    unfolding z0_def using a_lt_b by simp
  have M_nonneg: "M \<ge> 0"
    using M_prop z0_in_box by fastforce

  text \<open>\<open>\<epsilon>'\<close>, chosen so that \<open>H_1\<close>'s bound \<open>M\<epsilon>'D<\<epsilon>/2\<close>, where \<open>D\<close> collects \<open>H_1\<close>'s own \<open>N\<close>-
    and column-count-dependent factors.\<close>
  define Nc where "Nc = real (card (column_index r0 N))"
  define D where "D = Nc * (2 * real N + 1) + (2 * real N - 1)"
  have N_ge_1: "real N \<ge> 1" using N_pos by simp
  have D_nonneg: "D \<ge> 0"
    unfolding D_def Nc_def using N_ge_1 by simp

  define \<epsilon>' where "\<epsilon>' = \<epsilon> / (2 * (M + 1) * (D + 1))"
  have denom_pos: "2 * (M + 1) * (D + 1) > 0"
    using M_nonneg D_nonneg by simp
  have \<epsilon>'_pos: "\<epsilon>' > 0"
    unfolding \<epsilon>'_def using eps_pos denom_pos by simp

  text \<open>\<open>w\<close>, from the \<open>\<sigma>\<close>-saturation threshold at \<open>\<epsilon>'\<close> and \<open>h/2\<close>.\<close>
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
  define w where "w = \<omega>"
  have w_pos: "w > 0" unfolding w_def using \<omega>_pos .
  have step0: "\<forall>z' q :: (real, 'n) vec. \<forall>s::real. s = 1 \<or> s = -1 \<longrightarrow>
                 norm (z' - q) \<ge> h / 2 \<longrightarrow> \<bar>\<sigma> (w * s * norm (z' - q)) - (if s = 1 then 1 else 0)\<bar> < \<epsilon>'"
    using \<omega>_prop unfolding w_def by simp

  have f_bound: "\<And>p. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> \<bar>f p\<bar> \<le> M"
    using M_prop by blast
  have f_cont: "\<And>p q. (\<forall>r. p $ r \<in> {a..b}) \<Longrightarrow> (\<forall>r. q $ r \<in> {a..b}) \<Longrightarrow> norm (p - q) < \<delta>
                   \<Longrightarrow> \<bar>f p - f q\<bar> < \<eta>"
    using \<delta>_prop by blast

  text \<open>\<open>(1+S)\<eta><\<epsilon>/2\<close>, from \<open>1+S<S+2\<close>.\<close>
  have H2_lt: "(1 + S) * \<eta> < \<epsilon> / 2"
  proof -
    have "1 + S < S + 2" by simp
    then have "(1 + S) * \<epsilon> < (S + 2) * \<epsilon>" using eps_pos by simp
    then have "(1 + S) * \<epsilon> / (2 * (S + 2)) < (S + 2) * \<epsilon> / (2 * (S + 2))"
      using S_nonneg by (simp add: divide_strict_right_mono)
    also have "(S + 2) * \<epsilon> / (2 * (S + 2)) = \<epsilon> / 2"
      using S_nonneg by (simp add: field_simps)
    finally show ?thesis
      unfolding \<eta>_def by (simp add: algebra_simps)
  qed

  text \<open>\<open>M\<epsilon>'D<\<epsilon>/2\<close>, from \<open>MD<(M+1)(D+1)\<close> (since \<open>M,D\<ge>0\<close>).\<close>
  have H1_lt: "Nc * M * \<epsilon>' * (2 * real N + 1) + M * \<epsilon>' * (2 * real N - 1) < \<epsilon> / 2"
  proof -
    have eq1: "Nc * M * \<epsilon>' * (2 * real N + 1) + M * \<epsilon>' * (2 * real N - 1) = M * \<epsilon>' * D"
      unfolding D_def by (simp add: algebra_simps)
    have expand: "(M + 1) * (D + 1) = M * D + M + D + 1"
      by (simp add: algebra_simps)
    have "M * D < (M + 1) * (D + 1)"
      unfolding expand using M_nonneg D_nonneg by simp
    then have "M * D * \<epsilon> < (M + 1) * (D + 1) * \<epsilon>"
      using eps_pos by simp
    then have "M * D * \<epsilon> / (2 * (M + 1) * (D + 1)) < (M + 1) * (D + 1) * \<epsilon> / (2 * (M + 1) * (D + 1))"
      using denom_pos by (rule divide_strict_right_mono)
    also have "(M + 1) * (D + 1) * \<epsilon> / (2 * (M + 1) * (D + 1)) = \<epsilon> / 2"
      using denom_pos by (simp add: field_simps)
    finally have "M * D * \<epsilon> / (2 * (M + 1) * (D + 1)) < \<epsilon> / 2" .
    then have "M * \<epsilon>' * D < \<epsilon> / 2"
      unfolding \<epsilon>'_def by (simp add: algebra_simps)
    then show ?thesis unfolding eq1 .
  qed

  show ?thesis
  proof (intro exI[where x = N] exI[where x = w] conjI N_pos w_pos allI impI)
    fix z :: "(real, 'n) vec"
    assume z_in_box: "\<forall>r. z $ r \<in> {a..b}"
    obtain k j where k_range: "k \<in> column_index r0 N" and j_range: "j \<in> {1..N}"
      and z_in_column: "in_column r0 xs k z" and z_height: "z $ r0 \<in> {xs ! j .. xs ! (j + 1)}"
      using exists_column_and_height[OF a_lt_b N_pos h_def xs_def z_in_box] by blast

    \<comment> \<open>\<open>H\<^sub>1\<close> is now parameterised by a bound \<open>Df\<close> on adjacent-node differences of \<open>f\<close>;
        Theorem 5.1 only needs the crude \<open>Df = 2M\<close> (Theorem 5.2 supplies the Hoelder bound
        instead), and the old numeric form follows by \<open>algebra_simps\<close>.\<close>
    have twoM_nonneg: "0 \<le> 2 * M" using M_nonneg by simp
    have df2M: "\<And>k' j'. k' \<in> column_index r0 N \<Longrightarrow> j' \<in> {1..N} \<Longrightarrow>
        \<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> 2 * M"
    proof -
      fix k' j' assume k'r: "k' \<in> column_index r0 N" and j'r: "j' \<in> {1..N}"
      have j'_box: "j' \<in> {0..N}" and jm1_box: "j' - 1 \<in> {0..N}" using j'r by auto
      have b1: "\<forall>r. sample_point r0 xs k' j' $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def j'_box k'r] .
      have b2: "\<forall>r. sample_point r0 xs k' (j' - 1) $ r \<in> {a..b}"
        using sample_point_in_box[OF a_lt_b N_pos h_def xs_def jm1_box k'r] .
      show "\<bar>f (sample_point r0 xs k' j') - f (sample_point r0 xs k' (j' - 1))\<bar> \<le> 2 * M"
        using f_bound[OF b1] f_bound[OF b2] by argo
    qed
    have H1: "\<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
        \<le> Nc * M * \<epsilon>' * (2 * real N + 1) + M * \<epsilon>' * (2 * real N - 1)"
    proof -
      have raw: "\<bar>multivariate_network \<sigma> f r0 xs N w z - local_proxy r0 xs k j \<sigma> f w z\<bar>
          \<le> (real (card (column_index r0 N)) * (real N * (2 * M * \<epsilon>'))
                + real (card (column_index r0 N)) * (M * \<epsilon>'))
              + ((real N - 1) * (2 * M * \<epsilon>') + M * \<epsilon>')"
        using multivariate_network_H1_bound[OF a_lt_b N_pos h_def xs_def \<epsilon>'_pos f_bound
          twoM_nonneg df2M k_range j_range z_height z_in_column z_in_box step0] .
      show ?thesis using raw unfolding Nc_def by (simp add: algebra_simps)
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
      then show ?thesis using abs_triangle_ineq by (metis (no_types, lifting))
    qed

    have final: "\<bar>multivariate_network \<sigma> f r0 xs N w z - f z\<bar> < \<epsilon>"
      using triangle H1 H1_lt H2 H2_lt by linarith

    show "\<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z\<bar> < \<epsilon>"
      unfolding xs_def[symmetric] using final .
  qed
qed

text \<open>
  Towards Theorem 5.3 (the multivariate \<open>L^p\<close> analogue of Theorem 5.1, in theory
  \<open>Lp_Approximation\<close> for the 1-d case): unlike the 1-d network, \<open>multivariate_network\<close> is NOT
  continuous in \<open>z\<close> (\<open>column_sign\<close> is a \<open>\<plusminus>1\<close>-valued step function of \<open>z\<close>, jumping at
  \<open>in_cell\<close>/height-cell boundaries), so the 1-d \<open>L^p\<close> proof's continuity-to-Henstock-Kurzweil
  bridge (\<open>Lp_norm_continuous_eq\<close>) is unavailable here. The route instead is Borel
  MEASURABILITY: \<open>column_sign\<close> is built from finitely many \<open>in_cell\<close> membership tests, each a
  Borel set (\<open>atLeastAtMost_borel\<close>/\<open>greaterThanAtMost_borel\<close>), composed with the continuous
  coordinate projections \<open>z$r\<close>, so \<open>multivariate_network\<close> is measurable even though it is not
  continuous -- enough to make the Lebesgue \<open>L^p\<close> integral well-defined and, combined with the
  EVERYWHERE (not just a.e.) bound from \<open>multivariate_uniform_approximation\<close>, integrable.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma coord_measurable: "(\<lambda>z::(real, 'n::finite) vec. z $ r) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_on_component continuous_on_id)

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma in_cell_set_borel: "{x :: real. in_cell xs m x} \<in> sets borel"
  unfolding in_cell_def by (simp add: atLeastAtMost_borel greaterThanAtMost_borel)

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma in_column_set_borel:
  fixes r0 :: "'n::finite" and xs :: "real list" and k :: "'n \<Rightarrow> nat"
  shows "{z :: (real, 'n) vec. in_column r0 xs k z} \<in> sets borel"
proof -
  have eq: "{z :: (real, 'n) vec. in_column r0 xs k z}
      = (\<Inter>r \<in> {r. r \<noteq> r0}. {z. in_cell xs (k r) (z $ r)})"
    unfolding in_column_def by auto
  have each: "\<And>r. {z :: (real, 'n) vec. in_cell xs (k r) (z $ r)} \<in> sets borel"
  proof -
    fix r
    have "{z :: (real, 'n) vec. in_cell xs (k r) (z $ r)}
        = (\<lambda>z. z $ r) -` {x. in_cell xs (k r) x} \<inter> space borel"
      by simp
    then show "{z :: (real, 'n) vec. in_cell xs (k r) (z $ r)} \<in> sets borel"
      using measurable_sets[OF coord_measurable in_cell_set_borel] by simp
  qed
  show ?thesis
    unfolding eq by (intro sets.countable_INT'') (auto intro: each)
qed

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma column_sign_measurable:
  fixes r0 :: "'n::finite" and xs :: "real list" and k :: "'n \<Rightarrow> nat" and j :: nat
  shows "(\<lambda>z :: (real, 'n) vec. column_sign r0 xs k j z) \<in> borel_measurable borel"
proof -
  define P where "P = (\<lambda>z :: (real, 'n) vec. in_column r0 xs k z \<and> z $ r0 \<ge> xs ! (j + 1))"
  have P_eq: "\<And>z. column_sign r0 xs k j z = (if P z then 1 else -1)"
    unfolding column_sign_def P_def by simp
  have zr0_measurable: "(\<lambda>z :: (real, 'n) vec. z $ r0) \<in> borel_measurable borel"
    using coord_measurable .
  have half_space: "{z :: (real, 'n) vec. z $ r0 \<ge> xs ! (j + 1)} \<in> sets borel"
  proof -
    have "{z :: (real, 'n) vec. z $ r0 \<ge> xs ! (j + 1)}
        = (\<lambda>z. z $ r0) -` {xs ! (j + 1) ..} \<inter> space borel"
      by (auto simp: vimage_def)
    then show ?thesis
      using measurable_sets[OF zr0_measurable] by simp
  qed
  have P_set: "{z :: (real, 'n) vec. P z} \<in> sets borel"
    unfolding P_def using in_column_set_borel[of r0 xs k] half_space
    by (simp add: Collect_conj_eq)
  have ind_measurable: "indicator {z :: (real, 'n) vec. P z} \<in> borel_measurable borel"
    using P_set by (rule borel_measurable_indicator)
  have eq2: "\<And>z. column_sign r0 xs k j z = 2 * indicator {z. P z} z - 1"
    unfolding P_eq by (simp add: indicator_def)
  show ?thesis
    unfolding eq2 using ind_measurable by measurable
qed

(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_network_measurable:
  fixes r0 :: "'n::finite" and xs :: "real list" and N :: nat and w :: real
  fixes f :: "(real, 'n) vec \<Rightarrow> real" and \<sigma> :: "real \<Rightarrow> real"
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  shows "(\<lambda>z. multivariate_network \<sigma> f r0 xs N w z) \<in> borel_measurable borel"
proof -
  have \<sigma>_measurable: "\<sigma> \<in> borel_measurable borel"
    using meas_sigmoidal .
  have norm_measurable: "\<And>p :: (real, 'n) vec. (\<lambda>z. norm (z - p)) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have term_measurable: "\<And>k j. (\<lambda>z :: (real, 'n) vec.
        \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)))
      \<in> borel_measurable borel"
    using column_sign_measurable norm_measurable \<sigma>_measurable by measurable
  have boundary_term_measurable: "\<And>k. (\<lambda>z :: (real, 'n) vec.
        \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)))
      \<in> borel_measurable borel"
    using column_sign_measurable norm_measurable \<sigma>_measurable by measurable
  have main_sum_measurable: "(\<lambda>z. \<Sum>k \<in> column_index r0 N. \<Sum>j \<in> {1..N}.
        (f (sample_point r0 xs k j) - f (sample_point r0 xs k (j - 1)))
          * \<sigma> (w * column_sign r0 xs k j z * norm (z - grid_point r0 xs k j)))
      \<in> borel_measurable borel"
    using term_measurable by measurable
  have boundary_sum_measurable: "(\<lambda>z. \<Sum>k \<in> column_index r0 N.
        f (sample_point r0 xs k 0) * \<sigma> (w * column_sign r0 xs k 0 z * norm (z - sigma_anchor r0 xs k 0)))
      \<in> borel_measurable borel"
    using boundary_term_measurable by measurable
  show ?thesis
    unfolding multivariate_network_def
    using main_sum_measurable boundary_sum_measurable by measurable
qed

text \<open>
  Theorem 5.3, generalized: the multivariate \<open>L^p\<close> analogue of Theorem 5.1, mirroring Theorem 3.1
  (\<open>sigmoidal_Lp_approximation_theorem\<close>, theory \<open>Lp_Approximation\<close>) but via Lebesgue
  measurability (\<open>multivariate_network_measurable\<close> above) rather than continuity, since
  \<open>multivariate_network\<close> is not continuous in \<open>z\<close> (see the scoping note above). \<open>multivariate_Lp_norm\<close>
  is defined directly as a Bochner integral over \<open>lebesgue_on Q\<close>, \<open>Q\<close> the box, mirroring
  \<open>Lp_norm\<close>'s own measure-theoretic definition in \<open>Lp_Approximation.thy\<close> -- including its
  integrability guard, for the same reason: without it a non-integrable argument would make
  the Bochner integral collapse to the junk value \<open>0\<close> and \<open>multivariate_Lp_norm p a b g < \<epsilon>\<close>
  hold vacuously.  See the discussion at \<open>Lp_norm\<close>.
\<close>
definition multivariate_Lp_norm :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((real, 'n::finite) vec \<Rightarrow> real) \<Rightarrow> real" where
  "multivariate_Lp_norm p a b g =
     (if integrable (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}) (\<lambda>z. \<bar>g z\<bar> powr p)
      then (\<integral>z. \<bar>g z\<bar> powr p \<partial>(lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})) powr (1 / p)
      else undefined)"

text \<open>The computation rule, as for \<open>Lp_norm\<close>.\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma multivariate_Lp_norm_integrable_eq:
  fixes g :: "(real, 'n::finite) vec \<Rightarrow> real"
  assumes g_int: "integrable (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})
                    (\<lambda>z. \<bar>g z\<bar> powr p)"
  shows "multivariate_Lp_norm p a b g
       = (\<integral>z. \<bar>g z\<bar> powr p \<partial>(lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})) powr (1 / p)"
  using g_int unfolding multivariate_Lp_norm_def by simp

text \<open>
  The extended-real norm \<open>Lp_enorm\<close> (\<^file>\<open>Lp_Inequalities.thy\<close>) agrees with this one on
  integrable arguments, which is what lets Theorems 5.3 and 5.4 be stated in \<open>[0,\<infinity>]\<close> while
  their proofs run in \<^typ>\<open>real\<close>.
\<close>
(* Auxiliary for Theorems 5.1-5.4; not separately numbered. *)
lemma Lp_enorm_eq_multivariate_Lp_norm:
  fixes h :: "(real, 'n::finite) vec \<Rightarrow> real"
  assumes h_int: "integrable (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})
                    (\<lambda>z. \<bar>h z\<bar> powr p)"
  shows "Lp_enorm p (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}) h
       = ennreal (multivariate_Lp_norm p a b h)"
  unfolding Lp_enorm_eq_seminorm[OF h_int] Lp_seminorm_def
            multivariate_Lp_norm_integrable_eq[OF h_int]
  by (rule refl)

(* Theorem 5.3: endpoint-sampling operator; measurable activation. *)
theorem multivariate_sigmoidal_Lp_approximation_theorem:
  fixes a b :: real and f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: "'n::finite"
  fixes \<sigma> :: "real \<Rightarrow> real"
  assumes sigmoidal_function: "sigmoidal \<sigma>"
  assumes bounded_sigmoidal: "bounded_function \<sigma>"
  assumes meas_sigmoidal: "\<sigma> \<in> borel_measurable borel"
  assumes a_lt_b: "a < b"
  assumes contin_f: "continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"
  assumes p_geq_1: "p \<ge> (1 :: real)"
  assumes eps_pos: "0 < \<epsilon>"
  shows "\<exists>N :: nat. \<exists>(w :: real) > 0. N > 0 \<and>
           Lp_enorm p (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})
             (\<lambda>z. multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z) < ennreal \<epsilon>"
proof -
  define Q where "Q = {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}"
  have Q_eq_cbox: "Q = cbox (\<chi> r. a) (\<chi> r. b)"
    unfolding Q_def by (auto simp: mem_box_cart)
  have witness_in_box: "(\<chi> r. a :: (real, 'n) vec) \<in> Q"
    unfolding Q_def using a_lt_b by simp
  have Q_nonempty: "Q \<noteq> {}"
    using witness_in_box by blast

  text \<open>Written as \<open>measure lborel Q\<close> rather than \<open>content Q\<close> throughout: this theory's
    ambient session also brings in \<open>Polynomial.content\<close>, and the two overloaded names resolve
    ambiguously here (bare \<open>content\<close> parses as the polynomial one) -- \<open>content\<close> is definitionally
    \<open>measure lborel\<close> (\<^file>\<open>~~/src/HOL/Analysis/Henstock_Kurzweil_Integration.thy\<close>), so this is not
    a loss of generality, just a name-clash workaround.\<close>
  have content_Q: "measure lborel Q = (b - a) ^ CARD('n)"
  proof -
    have "measure lborel (cbox (\<chi> r. a :: (real, 'n) vec) (\<chi> r. b))
        = prod (\<lambda>i. (\<chi> r. b :: (real, 'n) vec) $ i - (\<chi> r. a) $ i) UNIV"
      using content_cbox_cart[of "\<chi> r. a :: (real, 'n) vec" "\<chi> r. b"] Q_nonempty
      unfolding Q_eq_cbox by simp
    also have "\<dots> = prod (\<lambda>i :: 'n. b - a) UNIV"
      by simp
    also have "\<dots> = (b - a) ^ CARD('n)"
      by (simp only: prod_constant)
    finally show ?thesis
      unfolding Q_eq_cbox .
  qed
  have content_Q_pos: "measure lborel Q > 0"
    unfolding content_Q using a_lt_b by simp

  have Q_borel: "Q \<in> sets borel"
    unfolding Q_eq_cbox using cbox_borel .
  have Q_lborel: "Q \<in> sets lborel"
    using Q_borel by (simp only: sets_lborel)
  have Q_lebesgue: "Q \<in> sets lebesgue"
    using Q_lborel by (intro sets_completionI_sets)
  have Q_lmeasurable: "Q \<in> lmeasurable"
    unfolding Q_eq_cbox by (rule lmeasurable_cbox)
  have Q_finite_measure: "finite_measure (lebesgue_on Q)"
    using finite_measure_lebesgue_on[OF Q_lmeasurable] .

  have measure_Q_eq: "measure (lebesgue_on Q) Q = measure lborel Q"
  proof -
    have "measure (lebesgue_on Q) Q = measure (completion lborel) Q"
      using measure_restrict_space[of Q "completion lborel" Q] Q_lebesgue by simp
    also have "\<dots> = measure lborel Q"
      using measure_completion[OF Q_lborel] .
    finally show ?thesis
      by simp
  qed

  obtain \<epsilon>' where \<epsilon>'_def: "\<epsilon>' = \<epsilon> / 2" by blast
  have \<epsilon>'_pos: "\<epsilon>' > 0" using \<epsilon>'_def eps_pos by simp

  have content_Q_powr_pos: "measure lborel Q powr (1 / p) > 0"
    using content_Q_pos by simp

  obtain \<eta> where \<eta>_def: "\<eta> = \<epsilon>' / measure lborel Q powr (1 / p)"
    by blast
  have \<eta>_pos: "\<eta> > 0"
    unfolding \<eta>_def using \<epsilon>'_pos content_Q_powr_pos by simp

  from multivariate_uniform_approximation[OF sigmoidal_function bounded_sigmoidal a_lt_b contin_f \<eta>_pos]
  obtain N w where N_pos: "N > 0" and w_pos: "w > 0"
    and sup_bound: "\<forall>z. (\<forall>r. z $ r \<in> {a..b}) \<longrightarrow>
         \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z\<bar> < \<eta>"
    by blast

  define G_Nf where "G_Nf = (\<lambda>z. multivariate_network \<sigma> f r0 (unif_part a b N) N w z)"
  define g where "g = (\<lambda>z. G_Nf z - f z)"

  have sup_bound': "\<And>z. z \<in> Q \<Longrightarrow> \<bar>g z\<bar> < \<eta>"
    unfolding g_def G_Nf_def Q_def using sup_bound by blast

  have net_measurable: "G_Nf \<in> borel_measurable borel"
    unfolding G_Nf_def using multivariate_network_measurable[OF meas_sigmoidal] .
  have net_measurable_lebesgue: "G_Nf \<in> borel_measurable lebesgue"
  proof (rule borel_measurable_subalgebra[of borel lebesgue])
    show "sets borel \<subseteq> sets lebesgue"
      using sets_completionI_sets by auto 
    show "space borel = space lebesgue" by simp
    show "G_Nf \<in> borel_measurable borel" using net_measurable .
  qed
  have net_measurable_Q: "G_Nf \<in> borel_measurable (lebesgue_on Q)"
    using measurable_restrict_space1[OF net_measurable_lebesgue] .

  have f_measurable_Q: "f \<in> borel_measurable (lebesgue_on Q)"
    using continuous_imp_measurable_on_sets_lebesgue[OF _ Q_lebesgue]
    unfolding Q_def using contin_f by blast

  have g_measurable: "g \<in> borel_measurable (lebesgue_on Q)"
    unfolding g_def using net_measurable_Q f_measurable_Q by measurable

  have integrand_measurable: "(\<lambda>z. \<bar>g z\<bar> powr p) \<in> borel_measurable (lebesgue_on Q)"
    using g_measurable by measurable

  have pointwise_bound_ae: "AE z in (lebesgue_on Q). \<bar>g z\<bar> powr p \<le> \<eta> powr p"
  proof (rule AE_I2)
    fix z assume "z \<in> space (lebesgue_on Q)"
    then have z_in_Q: "z \<in> Q" by simp
    then have "\<bar>g z\<bar> \<le> \<eta>" using sup_bound' by (simp only: less_imp_le)
    then show "\<bar>g z\<bar> powr p \<le> \<eta> powr p"
      using p_geq_1 powr_mono2 by auto
  qed

  have integrand_integrable: "integrable (lebesgue_on Q) (\<lambda>z. \<bar>g z\<bar> powr p)"
  proof (rule finite_measure.integrable_const_bound[OF Q_finite_measure, where B = "\<eta> powr p"])
    show "AE z in (lebesgue_on Q). norm (\<bar>g z\<bar> powr p) \<le> \<eta> powr p"
      using pointwise_bound_ae by simp
    show "(\<lambda>z. \<bar>g z\<bar> powr p) \<in> borel_measurable (lebesgue_on Q)"
      using integrand_measurable .
  qed

  have const_integrable: "integrable (lebesgue_on Q) (\<lambda>z :: (real, 'n) vec. \<eta> powr p)"
    using finite_measure.integrable_const[OF Q_finite_measure] .

  have integral_le_const:
    "(\<integral>z. \<bar>g z\<bar> powr p \<partial>(lebesgue_on Q)) \<le> (\<integral>z. \<eta> powr p \<partial>(lebesgue_on Q))"
    using integral_mono_AE[OF integrand_integrable const_integrable pointwise_bound_ae] .

  have integral_const_val:
    "(\<integral>z. \<eta> powr p \<partial>(lebesgue_on Q)) = measure lborel Q * \<eta> powr p"
    using measure_Q_eq by simp

  have integral_nonneg_le: "0 \<le> (\<integral>z. \<bar>g z\<bar> powr p \<partial>(lebesgue_on Q))"
    by (rule Bochner_Integration.integral_nonneg) simp

  have powr_le: "(\<integral>z. \<bar>g z\<bar> powr p \<partial>(lebesgue_on Q)) powr (1 / p)
      \<le> (measure lborel Q * \<eta> powr p) powr (1 / p)"
    by (rule powr_mono2, use p_geq_1 integral_nonneg_le integral_le_const integral_const_val in auto)

  have simplify_rhs: "(measure lborel Q * \<eta> powr p) powr (1 / p) = measure lborel Q powr (1 / p) * \<eta>"
  proof -
    have "(measure lborel Q * \<eta> powr p) powr (1 / p)
        = measure lborel Q powr (1 / p) * (\<eta> powr p) powr (1 / p)"
      using content_Q_pos \<eta>_pos by (simp only: powr_mult)
    also have "(\<eta> powr p) powr (1 / p) = \<eta> powr (p * (1 / p))"
      by (rule powr_powr)
    also have "p * (1 / p) = 1"
      using p_geq_1 by simp
    also have "\<eta> powr 1 = \<eta>"
      using \<eta>_pos by simp
    finally show ?thesis
      by simp
  qed

  have final_eq: "measure lborel Q powr (1 / p) * \<eta> = \<epsilon>'"
    unfolding \<eta>_def using content_Q_powr_pos by simp

  have "multivariate_Lp_norm p a b g \<le> \<epsilon>'"
    unfolding multivariate_Lp_norm_integrable_eq[OF integrand_integrable[unfolded Q_def]]
              Q_def[symmetric]
    using powr_le simplify_rhs final_eq by simp
  also have "\<epsilon>' < \<epsilon>"
    using \<epsilon>'_def eps_pos by simp
  finally have Lp_bound: "multivariate_Lp_norm p a b g < \<epsilon>" .

  \<comment> \<open>transfer to the extended reals via the bridge, using the integrability already
      established above for the integrand \<open>g\<close>\<close>
  have Lp_bound_e: "Lp_enorm p (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}}) g
                      < ennreal \<epsilon>"
    unfolding Lp_enorm_eq_multivariate_Lp_norm[OF integrand_integrable[unfolded Q_def]]
    by (rule ennreal_lessI[OF eps_pos Lp_bound])

  show ?thesis
  proof (intro exI[where x = N] exI[where x = w] conjI)
    show "w > 0" by (rule w_pos)
    show "N > 0" by (rule N_pos)
    show "Lp_enorm p (lebesgue_on {z :: (real, 'n) vec. \<forall>r. z $ r \<in> {a..b}})
            (\<lambda>z. multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z) < ennreal \<epsilon>"
      using Lp_bound_e unfolding g_def G_Nf_def by simp
  qed
qed


subsection \<open>Theorem 5.1 in the printed strict-supremum form, and on translated boxes\<close>

(* Theorem 5.1: strict supremum formulation for the endpoint-sampling operator. *)
theorem multivariate_uniform_approximation_sup:
  fixes f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: 'n
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and ab: "a < b" and fc: "continuous_on {z. \<forall>r. z$r \<in> {a..b}} f"
    and e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Sup ((\<lambda>z. \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar>)
      ` {z. \<forall>r. z$r \<in> {a..b}}) < e"
proof -
  have e2: "0 < e/2" using e by simp
  obtain N w where N: "0 < N" and w: "0 < w"
    and bd: "\<forall>z. (\<forall>r. z$r \<in> {a..b}) \<longrightarrow>
      \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar> < e/2"
    using multivariate_uniform_approximation[OF sig bnd ab fc e2] by blast
  have ne: "{z :: (real, 'n) vec. \<forall>r. z$r \<in> {a..b}} \<noteq> {}"
    using ab by (auto intro!: exI[where x="\<chi> r. a"])
  have sup: "Sup ((\<lambda>z. \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar>)
      ` {z. \<forall>r. z$r \<in> {a..b}}) < e"
    by (rule strict_sup_from_half_bound[OF ne e]) (use bd in auto)
  show ?thesis by (intro exI[where x=N] exI[where x=w]) (use N w sup in simp)
qed

(* Equation (5.1), translated coordinates: each coordinate interval has its own origin. *)
definition translated_multivariate_network where
  "translated_multivariate_network \<sigma> f v r0 a b N w z =
    multivariate_network \<sigma> (\<lambda>y. f (v+y)) r0 (unif_part a b N) N w (z-v)"

(* Theorem 5.1: independently translated equal-length coordinate intervals; includes [a,b] x [c,d]. *)
theorem translated_multivariate_uniform_approximation:
  fixes f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: 'n and v :: "(real, 'n) vec"
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>" and ab: "a < b"
    and fc: "continuous_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}} f" and e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Sup ((\<lambda>z. \<bar>translated_multivariate_network \<sigma> f v r0 a b N w z-f z\<bar>)
      ` {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}}) < e"
proof -
  let ?Q = "{z :: (real, 'n) vec. \<forall>r. z$r \<in> {a..b}}"
  let ?T = "{z :: (real, 'n) vec. \<forall>r. z$r \<in> {v$r+a..v$r+b}}"
  have image_eq: "(\<lambda>z. v+z) ` ?Q = ?T"
  proof
    show "(\<lambda>z. v+z) ` ?Q \<subseteq> ?T" by auto
    show "?T \<subseteq> (\<lambda>z. v+z) ` ?Q"
      by (intro subsetI, rule image_eqI[where x="x-v" for x]) (auto simp: le_diff_eq diff_le_eq add.commute)
  qed
  have fci: "continuous_on ((\<lambda>z. v+z) ` ?Q) f"
    using fc by (simp only: image_eq)
  have vc: "continuous_on ?Q (\<lambda>z. v+z)" by (intro continuous_intros)
  have cont: "continuous_on ?Q (\<lambda>z. f (v+z))"
    using continuous_on_compose[OF vc fci] by (simp only: o_def)
  have e2: "0 < e/2" using e by simp
  obtain N w where N: "0 < N" and w: "0 < w"
    and bd: "\<forall>z. (\<forall>r. z$r \<in> {a..b}) \<longrightarrow>
      \<bar>multivariate_network \<sigma> (\<lambda>y. f (v+y)) r0 (unif_part a b N) N w z-f (v+z)\<bar> < e/2"
    using multivariate_uniform_approximation[OF sig bnd ab cont e2] by blast
  have point: "\<And>z. z \<in> ?T \<Longrightarrow>
      \<bar>translated_multivariate_network \<sigma> f v r0 a b N w z-f z\<bar> < e/2"
  proof -
    fix z assume z: "z \<in> ?T"
    have "z-v \<in> ?Q" using z by (auto simp: le_diff_eq diff_le_eq add.commute)
    then show "\<bar>translated_multivariate_network \<sigma> f v r0 a b N w z-f z\<bar> < e/2"
      using bd[rule_format, of "z-v"] unfolding translated_multivariate_network_def by simp
  qed
  have ne: "?T \<noteq> {}" using ab by (auto intro!: exI[where x="v + (\<chi> r. a)"])
  have sup: "Sup ((\<lambda>z. \<bar>translated_multivariate_network \<sigma> f v r0 a b N w z-f z\<bar>) ` ?T) < e"
    by (rule strict_sup_from_half_bound[OF ne e point])
  show ?thesis by (intro exI[where x=N] exI[where x=w]) (use N w sup in simp)
qed

end
