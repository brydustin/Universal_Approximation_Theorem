section \<open>A strict supremum bound from a halved pointwise bound\<close>

theory Sup_Estimates
  imports "HOL-Analysis.Analysis"
begin

text \<open>
  Several results of the paper are stated with a strict supremum, \<open>\<bar>\<bar>G\<^sub>N f - f\<bar>\<bar>\<^sub>\<infinity> < \<epsilon>\<close>,
  while the constructions that establish them naturally deliver a pointwise bound at every
  point of the interval.  A pointwise strict bound does not give a strict supremum bound --
  the supremum of values all \<open>< \<epsilon>\<close> can equal \<open>\<epsilon>\<close> -- so the estimate is run at \<open>\<epsilon>/2\<close> and the
  supremum is then bounded by \<open>\<epsilon>/2 < \<epsilon>\<close>.

  This is the only content of that step, it involves nothing from this development, and it is
  needed at four different places in the import order (Theorems 2.1, 4.1, 5.1 and 5.2), which
  is why it sits here at the bottom rather than beside any one of them.
\<close>

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

end
