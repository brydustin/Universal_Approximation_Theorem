section \<open>Reusable Facts about the Uniform Partition\<close>

theory Partition_Facts
  imports Asymptotic_Qualitative_Properties
begin

text \<open>
  The partition arithmetic used to prove Theorem 2.1 (in \<^file>\<open>Universal_Approximation_1d.thy\<close>)
  does not depend on \<open>f\<close> or \<open>\<sigma>\<close> at all -- only on \<open>a\<close>, \<open>b\<close>, \<open>N\<close>.  It was proved inline there as
  part of one long proof; we re-derive it here as standalone, reusable lemmas so that Theorem 4.1
  in \<^file>\<open>Derivative_Approximation.thy\<close> does not have to re-derive the same partition geometry
  from scratch. Each lemma takes \<open>a\<close>, \<open>b\<close>, \<open>N\<close> (and, where needed, \<open>h\<close> and \<open>xs\<close>) as explicit
  parameters with explicit hypotheses, rather than via a \<open>locale\<close>.
\<close>

(* Theorem 2.1: uniform nodes, with the paper index shifted by one. *)
definition unif_part :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real list" where
  "unif_part a b N =
     map (\<lambda>k. a + (real k -1 ) * ((b - a) / real N )) [0..<N+2]"

(* For example, unif_part 0 1 4 = [-0.25, 0, 0.25, 0.5, 0.75, 1] :: real list.
   Index 0 holds the exterior node x\<^sub>-\<^sub>1, so paper index k is list index k+1. *)

(* Auxiliary for equation (2.2): the endpoint list includes the exterior node. *)
lemma length_unif_part [simp]: "length (unif_part a b N) = N+2"
  unfolding unif_part_def by simp

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma h_pos:
  fixes a b :: real and N :: nat and h :: real
  assumes a_lt_b: "a < b" and N_pos: "N > 0" and h_def: "h = (b - a) / N"
  shows "h > 0"
  unfolding h_def using a_lt_b N_pos by simp

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma xs_els:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "\<And>k. k \<in> {0..N+1} \<longrightarrow> xs ! k = a + (real k - 1) * h"
  unfolding xs_def h_def unif_part_def
  by (metis (no_types, lifting) Suc_1 add_0 add_Suc_right atLeastAtMost_iff diff_zero
      linorder_not_le not_less_eq_eq nth_map_upt)

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma zeroth_element:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "xs ! 0 = a - h"
  using xs_els[OF h_def xs_def] by simp

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma first_element:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "xs ! 1 = a"
  using xs_els[OF h_def xs_def] by simp

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma last_element:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes N_pos: "N > 0" and h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "xs ! (N + 1) = b"
proof -
  have "xs ! (N + 1) = a + N * h"
    using xs_els[OF h_def xs_def] by force
  then show ?thesis
    by (simp add: h_def N_pos)
qed

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma difference_of_terms:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "\<And>j k. j \<in> {1..N+1} \<and> k \<in> {1..N+1} \<and> j \<le> k \<longrightarrow> xs ! k - xs ! j = h * (real k - j)"
proof (clarify)
  fix j k
  assume j_type: "j \<in> {1..N + 1}" and k_type: "k \<in> {1..N + 1}" and j_leq_k: "j \<le> k"
  have j_th_el: "xs ! j = a + (real j - 1) * h"
    using j_type xs_els[OF h_def xs_def] by auto
  have k_th_el: "xs ! k = a + (real k - 1) * h"
    using k_type xs_els[OF h_def xs_def] by auto
  then show "xs ! k - xs ! j = h * (real k - j)"
    by (smt (verit, del_insts) j_th_el left_diff_distrib' mult.commute)
qed

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma list_increasing:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes a_lt_b: "a < b" and N_pos: "N > 0" and h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "\<And>j k. j \<in> {1..N+1} \<and> k \<in> {1..N+1} \<and> j \<le> k \<longrightarrow> xs ! j \<le> xs ! k"
  using difference_of_terms[OF h_def xs_def] h_pos[OF a_lt_b N_pos h_def]
  by (smt (verit, ccfv_SIG) of_nat_eq_iff of_nat_mono zero_less_mult_iff)

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma els_in_ab:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes a_lt_b: "a < b" and N_pos: "N > 0" and h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "\<And>k. k \<in> {1..N+1} \<longrightarrow> xs ! k \<in> {a..b}"
  using first_element[OF h_def xs_def] last_element[OF N_pos h_def xs_def]
        list_increasing[OF a_lt_b N_pos h_def xs_def]
  by force

text \<open>Every cell of the partition has exactly width \<open>h\<close>.\<close>
(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma difference_of_adj_terms:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  shows "\<And>k. k \<in> {1..N+1} \<longrightarrow> xs ! k - xs ! (k - 1) = h"
proof -
  fix k :: nat
  have "k = 1 \<longrightarrow> k \<in> {1..N + 1} \<longrightarrow> xs ! k - xs ! (k - 1) = h"
    using first_element[OF h_def xs_def] zeroth_element[OF h_def xs_def] by auto
  then show "k \<in> {1..N + 1} \<longrightarrow> xs ! k - xs ! (k - 1) = h"
    using difference_of_terms[OF h_def xs_def] le_diff_conv by fastforce
qed

text \<open>
  The interval-covering fact used to open the case split in the proof of Theorem 2.1: every
  \<open>x \<in> [a,b]\<close> lies in exactly one of the \<open>N\<close> cells \<open>[x_i,x_{i+1}]\<close>.
\<close>
(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma exists_containing_interval:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes a_lt_b: "a < b" and N_pos: "N > 0" and h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes x_in_ab: "x \<in> {a..b}"
  shows "\<exists>i. i \<in> {1..N} \<and> x \<in> {xs ! i .. xs ! (i + 1)}"
proof -
  note first_element = first_element[OF h_def xs_def]
  note last_element = last_element[OF N_pos h_def xs_def]
  note list_increasing = list_increasing[OF a_lt_b N_pos h_def xs_def]
  have intervals_cover: "{xs ! 1 .. xs ! (N+1)} \<subseteq> (\<Union>i\<in>{1..N}. {xs ! i .. xs ! (i+1)})"
  proof
    fix x :: real
    assume x_def: "x \<in> {xs ! 1 .. xs ! (N+1)}"
    then have lower_bound: "x \<ge> xs ! 1"
      by simp
    from x_def have upper_bound: "x \<le> xs ! (N+1)"
      by simp

    obtain j where j_def: "j = (GREATEST j. xs ! j \<le> x \<and> j \<in> {1..N+1})"
      by blast
    have nonempty_definition: "{j \<in> {1..N+1}. xs ! j \<le> x} \<noteq> {}"
      using lower_bound by force
    then have j_exists: "\<exists>j \<in> {1..N+1}. xs ! j \<le> x"
      by blast
    have j_greatest: "xs ! j \<le> x \<and> j \<in> {1..N+1}"
      unfolding j_def
    proof (rule GreatestI_ex_nat[of "\<lambda>j. xs ! j \<le> x \<and> j \<in> {1..N+1}" "N+1"])
      show "\<exists>k. xs ! k \<le> x \<and> k \<in> {1..N+1}"
        using j_exists by blast
      show "\<And>y. xs ! y \<le> x \<and> y \<in> {1..N+1} \<Longrightarrow> y \<le> N + 1"
        by simp
    qed
    have j_bounds: "j \<in> {1..N+1}"
      using j_greatest by blast
    have xs_j_leq_x: "xs ! j \<le> x"
      by (metis (no_types, lifting) GreatestI_ex_nat atLeastAtMost_iff j_def j_exists)

    show "x \<in> (\<Union>i \<in> {1..N}. {xs ! i..xs ! (i + 1)})"
    proof (cases "j = N+1")
      show "j = N + 1 \<Longrightarrow> x \<in> (\<Union>i \<in> {1..N}. {xs ! i..xs ! (i + 1)})"
      proof -
        assume j_eq: "j = N + 1"
        have x_eq_b: "x = b"
          using xs_j_leq_x upper_bound j_eq last_element by simp
        have N_in: "N \<in> {1..N}"
          using N_pos by simp
        have le1: "xs ! N \<le> xs ! (N + 1)"
          using list_increasing N_pos by simp
        have "x \<in> {xs ! N .. xs ! (N + 1)}"
          using x_eq_b last_element le1 by simp
        then show ?thesis
          using N_in by blast
      qed
    next
      assume j_not_SucN: "j \<noteq> N + 1"
      then have j_type: "j \<in> {1..N}"
        by (metis Suc_eq_plus1 atLeastAtMost_iff j_bounds le_Suc_eq)
      then have Suc_j_type: "j + 1 \<in> {2..N+1}"
        by (metis Suc_1 Suc_eq_plus1 atLeastAtMost_iff diff_Suc_Suc diff_is_0_eq)
      have equal_sets: "{j \<in> {1..N+1}. xs ! j \<le> x} = {j \<in> {1..N}. xs ! j \<le> x}"
      proof
        show "{j \<in> {1..N}. xs ! j \<le> x} \<subseteq> {j \<in> {1..N + 1}. xs ! j \<le> x}"
          by auto
        show "{j \<in> {1..N + 1}. xs ! j \<le> x} \<subseteq> {j \<in> {1..N}. xs ! j \<le> x}"
          by (safe, metis (no_types, lifting) Greatest_equality Suc_eq_plus1 j_not_SucN
              atLeastAtMost_iff j_def le_Suc_eq)
      qed

      have xs_j1_not_le_x: "\<not> (xs ! (j+1) \<le> x)"
      proof (rule ccontr)
        assume BWOC: "\<not> \<not> xs ! (j + 1) \<le> x"
        then have Suc_j_type': "j+1 \<in> {1..N}"
          using Suc_j_type equal_sets add.commute by auto
        from j_def show False
          using equal_sets
          by (smt (verit, del_insts) BWOC Greatest_le_nat One_nat_def Suc_eq_plus1 Suc_j_type'
              Suc_n_not_le_n atLeastAtMost_iff mem_Collect_eq)
      qed
      then have "x \<in> {xs ! j .. xs ! (j+1)}"
        by (simp add: xs_j_leq_x)
      then show ?thesis
        using j_type by blast
    qed
  qed
  then show ?thesis
    using first_element last_element x_in_ab by fastforce
qed

text \<open>
  \<open>exists_containing_interval\<close>'s closed cells \<open>[x_i,x_{i+1}]\<close> deliberately let a point on a
  shared boundary belong to two adjacent cells at once -- harmless for existence, but Theorem
  5.1's own \<open>H_1\<close> argument (\<^file>\<open>Multivariate_Approximation.thy\<close>) needs the OPPOSITE property:
  a UNIQUE cell per point, exactly matching the paper's own \<open>\<chi>_{ij}\<close> convention, \<open>x\<in>(x_{i-1},x_i]\<close>
  for \<open>i\<ge>2\<close> (half-open, right-closed) but \<open>x\<in>[x_0,x_1]\<close> for \<open>i=1\<close> (closed, no cell \<open>0\<close> to
  conflict with). \<open>in_cell\<close> is this convention, shifted to this project's own unshifted
  \<open>k\<close>-indexing (cell \<open>m\<close> is \<open>(xs!m,xs!(m+1)]\<close> for \<open>m>1\<close>, \<open>[xs!1,xs!2]\<close> for \<open>m=1\<close>).
\<close>
definition in_cell :: "real list \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool" where
  "in_cell xs m x \<longleftrightarrow> (if m = 1 then x \<in> {xs ! 1 .. xs ! 2} else x \<in> {xs ! m <.. xs ! (m + 1)})"

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma in_cell_upper: "in_cell xs m x \<Longrightarrow> x \<le> xs ! (m + 1)"
  unfolding in_cell_def by (auto split: if_splits simp: eval_nat_numeral)

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma in_cell_lower: "in_cell xs m x \<Longrightarrow> xs ! m \<le> x"
  unfolding in_cell_def by (auto split: if_splits simp: eval_nat_numeral)

(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma in_cell_lower_strict: "m > 1 \<Longrightarrow> in_cell xs m x \<Longrightarrow> xs ! m < x"
  unfolding in_cell_def by auto

text \<open>Uniqueness: a point lies in at most one \<open>in_cell\<close> cell.\<close>
(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma in_cell_unique:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes a_lt_b: "a < b" and N_pos: "N > 0" and h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes m1_range: "m1 \<in> {1..N}" and m2_range: "m2 \<in> {1..N}"
  assumes c1: "in_cell xs m1 x" and c2: "in_cell xs m2 x"
  shows "m1 = m2"
proof -
  have key: "\<And>p q. p \<in> {1..N} \<Longrightarrow> q \<in> {1..N} \<Longrightarrow> p < q \<Longrightarrow> in_cell xs p x \<Longrightarrow> in_cell xs q x \<Longrightarrow> False"
  proof -
    fix p q :: nat
    assume p_range: "p \<in> {1..N}" and q_range: "q \<in> {1..N}" and p_lt_q: "p < q"
    assume cp: "in_cell xs p x" and cq: "in_cell xs q x"
    have step: "p + 1 \<le> q" using p_lt_q by simp
    have pp1_N1: "p + 1 \<in> {1..N + 1}" and q_N1: "q \<in> {1..N + 1}"
      using p_range q_range by auto
    have mono: "xs ! (p + 1) \<le> xs ! q"
      using list_increasing[OF a_lt_b N_pos h_def xs_def] pp1_N1 q_N1 step by blast
    have x_le: "x \<le> xs ! (p + 1)"
      using in_cell_upper[OF cp] .
    have q_gt1: "q > 1" using p_range q_range p_lt_q by simp
    have x_gt: "xs ! q < x"
      using in_cell_lower_strict[OF q_gt1 cq] .
    show False
      using x_le mono x_gt by linarith
  qed
  show ?thesis
  proof (rule ccontr)
    assume neq: "m1 \<noteq> m2"
    then consider (lt) "m1 < m2" | (gt) "m2 < m1" by linarith
    then show False
    proof cases
      case lt show False using key[OF m1_range m2_range lt c1 c2] .
    next
      case gt show False using key[OF m2_range m1_range gt c2 c1] .
    qed
  qed
qed

text \<open>Existence: every point of \<open>[a,b]\<close> lies in some \<open>in_cell\<close> cell, derived from
  \<open>exists_containing_interval\<close>'s closed-cell witness by shifting down by one whenever that
  witness's LEFT endpoint happens to equal \<open>x\<close> (in which case \<open>x\<close> is instead the RIGHT endpoint
  of the previous cell, which \<open>in_cell\<close> always includes).\<close>
(* Auxiliary partition fact for Theorems 2.1, 4.1 and 5.1; not separately numbered. *)
lemma exists_in_cell:
  fixes a b :: real and N :: nat and h :: real and xs :: "real list"
  assumes a_lt_b: "a < b" and N_pos: "N > 0" and h_def: "h = (b - a) / N" and xs_def: "xs = unif_part a b N"
  assumes x_in_ab: "x \<in> {a..b}"
  shows "\<exists>m. m \<in> {1..N} \<and> in_cell xs m x"
proof -
  obtain i where i_range: "i \<in> {1..N}" and x_i: "x \<in> {xs ! i .. xs ! (i + 1)}"
    using exists_containing_interval[OF a_lt_b N_pos h_def xs_def x_in_ab] by blast
  show ?thesis
  proof (cases "i > 1 \<and> x = xs ! i")
    case True
    then have im1_range: "i - 1 \<in> {1..N}" using i_range by auto
    have eq: "i - 1 + 1 = i" using True by simp
    have "in_cell xs (i - 1) x"
    proof (cases "i - 1 = 1")
      case True': True
      have i_eq: "i = 2" using True' True by simp
      have mono2: "xs ! 1 \<le> xs ! 2"
        using list_increasing[OF a_lt_b N_pos h_def xs_def] i_range i_eq by auto
      show ?thesis
        unfolding in_cell_def using True' True i_eq mono2 by simp
    next
      case False
      then have im1_gt1: "i - 1 > 1" using im1_range by simp
      have step: "xs ! i - xs ! (i - 1) = h"
        using difference_of_adj_terms[OF h_def xs_def] i_range by auto
      have hpos: "h > 0" using h_pos[OF a_lt_b N_pos h_def] .
      then show ?thesis
        unfolding in_cell_def using im1_gt1 True eq step by simp
    qed
    then show ?thesis using im1_range by blast
  next
    case False
    have "in_cell xs i x"
    proof (cases "i = 1")
      case True
      then show ?thesis unfolding in_cell_def using x_i by (simp add: eval_nat_numeral)
    next
      case False': False
      then have i_gt1: "i > 1" using i_range by simp
      have x_ne: "x \<noteq> xs ! i" using False i_gt1 by simp
      have x_gt: "xs ! i < x" using x_i x_ne by simp
      then show ?thesis unfolding in_cell_def using i_gt1 x_i by simp
    qed
    then show ?thesis using i_range by blast
  qed
qed

end
