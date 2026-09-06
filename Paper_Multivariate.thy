theory Paper_Multivariate
  imports Multivariate_Holder_Rate Paper_Corollaries
begin

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

(* Theorem 5.2, corrected bound: endpoint operator, all sufficiently large weights, strict supremum. *)
theorem multivariate_holder_rate_sup:
  fixes f :: "(real, 'n::finite) vec \<Rightarrow> real" and r0 :: 'n
  assumes sig: "sigmoidal \<sigma>" and bnd: "bounded_function \<sigma>"
    and ab: "a < b" and N: "0 < N" and L: "0 < L"
    and alpha: "0 < alpha" and alpha1: "alpha \<le> 1"
    and fc: "continuous_on {z. \<forall>r. z$r \<in> {a..b}} f"
    and holder: "\<And>x y. (\<forall>r. x$r \<in> {a..b}) \<Longrightarrow> (\<forall>r. y$r \<in> {a..b})
      \<Longrightarrow> \<bar>f x-f y\<bar> \<le> L*norm (x-y) powr alpha"
  shows "\<exists>w0>0. \<forall>w\<ge>w0.
    Sup ((\<lambda>z. \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar>)
      ` {z. \<forall>r. z$r \<in> {a..b}}) <
    (2 + (1 + Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV))*L*
      ((b-a)*(real CARD('n)+2)) powr alpha) / real N powr alpha"
proof -
  let ?A = "(1 + Sup ((\<lambda>t. \<bar>\<sigma> t\<bar>) ` UNIV))*L*((b-a)*(real CARD('n)+2)) powr alpha"
  obtain w0 where w0: "0 < w0" and bd: "\<forall>w\<ge>w0. \<forall>z. (\<forall>r. z$r \<in> {a..b}) \<longrightarrow>
      \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar> <
      (1+?A) / real N powr alpha"
    using multivariate_holder_rate[OF sig bnd ab N L alpha alpha1 fc holder] by blast
  have ne: "{z :: (real, 'n) vec. \<forall>r. z$r \<in> {a..b}} \<noteq> {}"
    using ab by (auto intro!: exI[where x="\<chi> r. a"])
  show ?thesis
  proof (intro exI[where x=w0] conjI w0 allI impI)
    fix w assume w: "w0 \<le> w"
    have sup: "Sup ((\<lambda>z. \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar>)
      ` {z. \<forall>r. z$r \<in> {a..b}}) \<le> (1+?A) / real N powr alpha"
      by (rule cSup_least) (use ne in simp, use bd w in fastforce)
    have "(1+?A) / real N powr alpha < (2+?A) / real N powr alpha"
      using N by (intro divide_strict_right_mono) auto
    then show "Sup ((\<lambda>z. \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z-f z\<bar>)
      ` {z. \<forall>r. z$r \<in> {a..b}}) < (2+?A) / real N powr alpha"
      using sup by linarith
  qed
qed

end
