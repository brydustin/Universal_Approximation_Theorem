section \<open>Theorem 2.1 read as density\<close>

theory Sigmoidal_Span_Density
  imports Universal_Approximation_1d
begin

text \<open>
  Theorem 2.1 (\<^file>\<open>Universal_Approximation_1d.thy\<close>) is quantitative, which makes it
  harder to recognize as the Universal Approximation Theorem in its familiar form.  This
  theory adds the classical reading alongside it: the functions built from a bounded
  sigmoidal activation are dense in \<open>C[a,b]\<close> for the supremum norm, which is the shape of
  Cybenko's statement~\cite{Cybenko}.  Nothing here is a numbered result of
  Costarelli and Spigler; it is a restatement of their Theorem 2.1, recorded because what
  their theorem adds over density is precisely that the witness is written down.
\<close>

text \<open>
  The set of finite linear combinations of affinely reparametrized copies of an
  activation \<open>\<sigma>\<close> -- Cybenko's \<open>\<Sigma>(\<sigma>)\<close>.  The network \<^const>\<open>G_network\<close> of equation (2.2)
  is already of this shape, with a common slope \<open>w\<^sub>k \<equiv> w\<close> and shifts \<open>\<theta>\<^sub>k = -w x\<^sub>k\<close>.
\<close>
(* Density reading of Theorem 2.1; not a separately numbered paper result. *)
definition sigmoidal_span :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) set" where
  "sigmoidal_span \<sigma> =
     {g. \<exists>(n::nat) c w \<theta>. \<forall>x. g x = (\<Sum>k<n. c k * \<sigma> (w k * x + \<theta> k))}"

text \<open>
  Equation (2.2) as an element of the span: index \<open>0\<close> carries the boundary term
  \<open>f a \<cdot> \<sigma>(w(x - x\<^sub>0))\<close> and index \<open>j \<in> {1..N}\<close> carries the paper's index \<open>k = j+1\<close>.
\<close>
text \<open>
  The two coefficient families of equation (2.2), written as functions of a single index
  \<open>k \<in> {0..N}\<close>: index \<open>0\<close> carries the boundary term and index \<open>k > 0\<close> carries the paper's
  index \<open>k+1\<close>.  Naming them makes the network's weights first-class, which is what any
  structural (as opposed to functional) presentation of the network needs.
\<close>
(* Equation (2.2): the output weights, as a function of the hidden-unit index. *)
definition cs_coeff :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "cs_coeff f a b N k =
     (if k = 0 then f a
      else f (unif_part a b N ! (k+1)) - f (unif_part a b N ! k))"

(* Equation (2.2): the hidden-unit biases, as a function of the hidden-unit index. *)
definition cs_bias :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "cs_bias w a b N k =
     (if k = 0 then - w * (unif_part a b N ! 0)
      else - w * (unif_part a b N ! (k+1)))"

text \<open>
  Equation (2.2) as a single sum of affinely reparametrized copies of \<open>\<sigma>\<close>, with a common
  slope \<open>w\<close>.  This is the form every structural reading of the network goes through.
\<close>
(* Equation (2.2), reindexed: one sum over the hidden units. *)
lemma G_network_as_sum:
  "G_network \<sigma> f a b N w x =
     (\<Sum>k<N+1. cs_coeff f a b N k * \<sigma> (w * x + cs_bias w a b N k))"
proof -
  define xs where "xs = unif_part a b N"
  have split: "{..<N+1} = insert 0 {1..N}" by auto
  have "(\<Sum>k<N+1. cs_coeff f a b N k * \<sigma> (w * x + cs_bias w a b N k))
      = cs_coeff f a b N 0 * \<sigma> (w * x + cs_bias w a b N 0)
        + (\<Sum>k\<in>{1..N}. cs_coeff f a b N k * \<sigma> (w * x + cs_bias w a b N k))"
    by (simp only: split, subst sum.insert) auto
  also have "(\<Sum>k\<in>{1..N}. cs_coeff f a b N k * \<sigma> (w * x + cs_bias w a b N k))
           = (\<Sum>k\<in>{2..N+1}. (f (xs ! k) - f (xs ! (k-1))) * \<sigma> (w * (x - xs ! k)))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>k. k - 1" and j = "\<lambda>k. k + 1"])
       (auto simp: cs_coeff_def cs_bias_def xs_def algebra_simps)
  also have "cs_coeff f a b N 0 * \<sigma> (w * x + cs_bias w a b N 0)
           = f a * \<sigma> (w * (x - xs ! 0))"
    by (simp add: cs_coeff_def cs_bias_def xs_def algebra_simps)
  finally show ?thesis
    unfolding G_network_def xs_def by simp
qed

text \<open>
  Equation (2.2) as an element of the span: read off \<open>G_network_as_sum\<close>, with the common
  slope \<open>w\<^sub>k \<equiv> w\<close>.
\<close>
(* Auxiliary for the density reading of Theorem 2.1. *)
lemma G_network_in_span:
  "G_network \<sigma> f a b N w \<in> sigmoidal_span \<sigma>"
  unfolding sigmoidal_span_def mem_Collect_eq
  by (intro exI[where x="N+1"] exI[where x="cs_coeff f a b N"]
            exI[where x="\<lambda>_::nat. w"] exI[where x="cs_bias w a b N"])
     (simp add: G_network_as_sum)

text \<open>
  Theorem 2.1, read as density: \<open>\<Sigma>(\<sigma>)\<close> is dense in \<open>C[a,b]\<close> for the supremum norm.
  This is the classical Cybenko-style statement; what Theorem 2.1 adds over it is
  that the witness is written down.
\<close>
(* Density reading of Theorem 2.1. *)
theorem sigmoidal_span_dense:
  fixes \<sigma> f :: "real \<Rightarrow> real"
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and ab: "a < b" and fc: "continuous_on {a..b} f" and e: "0 < e"
  shows "\<exists>g \<in> sigmoidal_span \<sigma>. Sup ((\<lambda>x. \<bar>g x - f x\<bar>) ` {a..b}) < e"
proof -
  obtain N w where Nw: "0 < N" "0 < w"
    and bd: "Sup ((\<lambda>x. \<bar>G_network \<sigma> f a b N w x - f x\<bar>) ` {a..b}) < e"
    using sigmoidal_uniform_approximation_sup[OF sig bnd ab fc e] by blast
  show ?thesis using G_network_in_span bd by blast
qed

end
