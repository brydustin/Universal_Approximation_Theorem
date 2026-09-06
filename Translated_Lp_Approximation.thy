section \<open>\<open>L\<^sup>p\<close> approximation on translated boxes\<close>

theory Translated_Lp_Approximation
  imports Mollifier_Networks
begin

text \<open>
  Theorems 5.3 and 5.4 are stated on the normalized cube \<open>[a,b]\<^sup>d\<close>.  The paper's own domain is
  a product of independently translated equal-length coordinate intervals -- in two dimensions
  the square \<open>[a,b] \<times> [c,d]\<close>.  Translation is a measure isomorphism of the completed Lebesgue
  measure, so both the \<open>L\<^sup>p\<close> error and the mollifier coefficients transport exactly; this
  theory carries the two \<open>L\<^sup>p\<close> theorems, in their existential and their constructive forms,
  across that transport, and specializes them to the paper's square.
\<close>

(* Auxiliary for Theorems 5.3-5.4 on Q: translation is measurable for completed Lebesgue measure. *)
lemma translation_measurable:
  fixes v :: "'a::euclidean_space"
  shows "(\<lambda>x. v+x) \<in> measurable lebesgue lebesgue"
proof (rule measurableI)
  fix A :: "'a set" assume A: "A \<in> sets lebesgue"
  have eq: "(\<lambda>x. v+x) -` A = (\<lambda>x. -v+x) ` A" by force
  show "(\<lambda>x. v+x) -` A \<inter> space lebesgue \<in> sets lebesgue"
    using lebesgue_sets_translation[OF A, of "-v"] by (simp add: eq)
qed simp

(* Auxiliary for Theorems 5.3-5.4: the restricted completed-Lebesgue translation map. *)
lemma translation_on_measurable:
  fixes v :: "'a::euclidean_space"
  shows "(\<lambda>x. v+x) \<in> measurable (lebesgue_on S) (lebesgue_on ((+) v ` S))"
  by (rule measurable_restrict_space2)
     (auto intro: measurable_restrict_space1[OF translation_measurable])

(* Auxiliary for Theorems 5.3-5.4: exact measure transport, with no Jacobian factor for translation. *)
lemma translation_distr:
  fixes v :: "'a::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
  shows "distr (lebesgue_on S) (lebesgue_on ((+) v ` S)) ((+) v) =
    lebesgue_on ((+) v ` S)"
proof (rule measure_eqI)
  let ?T = "(+) v ` S"
  have T: "?T \<in> sets lebesgue" by (rule lebesgue_sets_translation[OF S])
  fix A assume A: "A \<in> sets (distr (lebesgue_on S) (lebesgue_on ?T) ((+) v))"
  have Asub: "A \<subseteq> ?T" using sets.sets_into_space[OF A] by simp
  have pre: "(+) v -` A \<subseteq> S" using Asub by auto
  have im: "(+) v ` ((+) v -` A) = A" by force
  have im': "(\<lambda>x. x+v) ` ((+) v -` A) = A"
    by (subst add.commute) (rule im)
  have eq: "emeasure lebesgue ((+) v -` A) = emeasure lebesgue A"
    using emeasure_lebesgue_affine[of 1 v "(+) v -` A"]
    by (simp add: im')
  show "emeasure (distr (lebesgue_on S) (lebesgue_on ?T) ((+) v)) A =
      emeasure (lebesgue_on ?T) A"
    using A S T pre Asub eq
    by (simp add: emeasure_distr[OF translation_on_measurable]
        Int_absorb2 emeasure_restrict_space)
qed simp

(* Auxiliary for Theorems 5.3-5.4: local measurability of a translated target. *)
lemma translation_target_measurable:
  fixes v :: "'a::euclidean_space"
  assumes fm: "f \<in> borel_measurable (lebesgue_on ((+) v ` S))"
  shows "(\<lambda>x. f (v+x)) \<in> borel_measurable (lebesgue_on S)"
  by (rule measurable_compose[OF translation_on_measurable fm])

(* Auxiliary for Theorems 5.3-5.4: integrability is preserved under the domain translation. *)
lemma translation_integrable:
  fixes v :: "'a::euclidean_space" and f :: "'a \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and fm: "f \<in> borel_measurable (lebesgue_on ((+) v ` S))"
  shows "integrable (lebesgue_on ((+) v ` S)) f \<longleftrightarrow>
    integrable (lebesgue_on S) (\<lambda>x. f (v+x))"
  using integrable_distr_eq[OF translation_on_measurable fm]
  by (simp only: translation_distr[OF S])

(* Auxiliary for Theorem 5.4, integral coefficients: change of variables on the original completed-Lebesgue target. *)
lemma translation_integral:
  fixes v :: "'a::euclidean_space" and f :: "'a \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and fm: "f \<in> borel_measurable (lebesgue_on ((+) v ` S))"
  shows "(\<integral>x. f x \<partial>(lebesgue_on ((+) v ` S))) =
    (\<integral>x. f (v+x) \<partial>(lebesgue_on S))"
  using integral_distr[OF translation_on_measurable fm]
  by (simp only: translation_distr[OF S])

(* Auxiliary for Theorems 5.3-5.4: equality of the actual extended-real Lp errors, not just real-valued integrals. *)
lemma translation_Lp_enorm:
  fixes v :: "'a::euclidean_space" and f :: "'a \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and fm: "f \<in> borel_measurable (lebesgue_on ((+) v ` S))"
  shows "Lp_enorm p (lebesgue_on ((+) v ` S)) f =
    Lp_enorm p (lebesgue_on S) (\<lambda>x. f (v+x))"
proof -
  have gm: "(\<lambda>x. f (v+x)) \<in> borel_measurable (lebesgue_on S)"
    by (rule translation_target_measurable[OF fm])
  have fp: "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> borel_measurable (lebesgue_on ((+) v ` S))"
    using fm by measurable
  have gp: "(\<lambda>x. \<bar>f (v+x)\<bar> powr p) \<in> borel_measurable (lebesgue_on S)"
    using gm by measurable
  have ep: "(\<lambda>x. ennreal (\<bar>f x\<bar> powr p)) \<in> borel_measurable (lebesgue_on ((+) v ` S))"
    using fm by measurable
  have epd: "(\<lambda>x. ennreal (\<bar>f x\<bar> powr p)) \<in>
      borel_measurable (distr (lebesgue_on S) (lebesgue_on ((+) v ` S)) ((+) v))"
    using ep by (simp only: translation_distr[OF S])
  have nn: "(\<integral>\<^sup>+x. ennreal (\<bar>f x\<bar> powr p) \<partial>(lebesgue_on ((+) v ` S))) =
      (\<integral>\<^sup>+x. ennreal (\<bar>f (v+x)\<bar> powr p) \<partial>(lebesgue_on S))"
    using nn_integral_distr[OF translation_on_measurable epd]
    by (simp only: translation_distr[OF S])
  show ?thesis unfolding Lp_enorm_measurable_eq[OF fp] Lp_enorm_measurable_eq[OF gp]
    by (simp only: nn)
qed

(* Auxiliary for Theorems 5.1 and 5.3-5.4: normalized and independently translated coordinate boxes. *)
lemma translated_box:
  fixes v :: "(real,'n::finite) vec"
  shows "(+) v ` {z. \<forall>r. z$r \<in> {a..b}} =
    {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}}"
proof
  show "(+) v ` {z. \<forall>r. z$r \<in> {a..b}} \<subseteq>
    {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}}" by auto
  show "{z. \<forall>r. z$r \<in> {v$r+a..v$r+b}} \<subseteq>
    (+) v ` {z. \<forall>r. z$r \<in> {a..b}}"
    by (intro subsetI, rule image_eqI[where x="x-v" for x])
       (auto simp: le_diff_eq diff_le_eq add.commute)
qed


(* Auxiliary for Theorems 5.3-5.4: measurability of the translated equation (5.1) operator. *)
lemma translated_multivariate_network_measurable:
  assumes sm: "act \<in> borel_measurable borel"
  shows "translated_multivariate_network act f v r0 a b N w \<in> borel_measurable borel"
  unfolding translated_multivariate_network_def
  by (rule measurable_compose[OF _ multivariate_network_measurable[OF sm]]) measurable

(* Theorem 5.3: ordinary Lp approximation on independently translated equal-length coordinate intervals. *)
theorem translated_multivariate_Lp_approximation:
  fixes f :: "(real,'n::finite) vec \<Rightarrow> real" and v :: "(real,'n) vec" and r0 :: 'n
  assumes sig: "sigmoidal act" and bnd: "bounded_function act"
    and sm: "act \<in> borel_measurable borel" and ab: "a < b"
    and fc: "continuous_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}} f"
    and p: "1 \<le> p" and e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}})
      (\<lambda>z. translated_multivariate_network act f v r0 a b N w z-f z) < ennreal e"
proof -
  let ?Q = "{z::(real,'n) vec. \<forall>r. z$r \<in> {a..b}}"
  let ?T = "{z::(real,'n) vec. \<forall>r. z$r \<in> {v$r+a..v$r+b}}"
  have Q: "?Q = cbox (\<chi> r. a) (\<chi> r. b)" by (auto simp: mem_box_cart)
  have T: "?T = cbox (v+(\<chi> r. a)) (v+(\<chi> r. b))" by (auto simp: mem_box_cart)
  have Qm: "?Q \<in> sets lebesgue" unfolding Q by simp
  have Tm: "?T \<in> sets lebesgue" unfolding T by simp
  have fm: "f \<in> borel_measurable (lebesgue_on ?T)"
    by (rule continuous_imp_measurable_on_sets_lebesgue[OF fc Tm])
  have vc: "continuous_on ?Q ((+) v)" by (intro continuous_intros)
  have fci: "continuous_on ((+) v ` ?Q) f" using fc by (simp only: translated_box)
  have gc: "continuous_on ?Q (\<lambda>y. f (v+y))"
    using continuous_on_compose[OF vc fci] by (simp only: o_def)
  obtain N w where N: "0 < N" and w: "0 < w" and bd:
    "Lp_enorm p (lebesgue_on ?Q)
      (\<lambda>z. multivariate_network act (\<lambda>y. f (v+y)) r0 (unif_part a b N) N w z-f (v+z)) < ennreal e"
    using multivariate_sigmoidal_Lp_approximation_theorem[OF sig bnd sm ab gc p e] by blast
  have Am: "translated_multivariate_network act f v r0 a b N w \<in> borel_measurable (lebesgue_on ?T)"
    by (rule borel_measurable_lebesgue_onI[OF translated_multivariate_network_measurable[OF sm]])
  have err: "(\<lambda>z. translated_multivariate_network act f v r0 a b N w z-f z)
      \<in> borel_measurable (lebesgue_on ((+) v ` ?Q))"
    unfolding translated_box using Am fm by measurable
  have eq: "Lp_enorm p (lebesgue_on ?T)
      (\<lambda>z. translated_multivariate_network act f v r0 a b N w z-f z) =
      Lp_enorm p (lebesgue_on ?Q)
      (\<lambda>z. multivariate_network act (\<lambda>y. f (v+y)) r0 (unif_part a b N) N w z-f (v+z))"
    using translation_Lp_enorm[OF Qm err, where p=p, unfolded translated_box]
    by (simp add: translated_multivariate_network_def)
  show ?thesis by (intro exI[where x=N] exI[where x=w]) (use N w bd eq in simp)
qed

(* Theorem 5.4, unnumbered convolution construction: translating the domain commutes with the exact mollifier. *)
lemma mollified_target_translation:
  fixes v :: "'a::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
    and fm: "f \<in> borel_measurable (lebesgue_on ((+) v ` S))"
  shows "mollified_target ((+) v ` S) f k (v+x) =
    mollified_target S (\<lambda>y. f (v+y)) k x"
proof -
  have km: "(\<lambda>y. mollifier k (v+x-y)) \<in> borel_measurable (lebesgue_on ((+) v ` S))"
    by (rule borel_measurable_lebesgue_onI) measurable
  have im: "(\<lambda>y. mollifier k (v+x-y)*f y) \<in> borel_measurable (lebesgue_on ((+) v ` S))"
    using km fm by measurable
  show ?thesis unfolding mollified_target_def
    using translation_integral[OF S im] by simp
qed

(* Theorem 5.4, coefficient construction: exact integral differences at translated sample points. *)
lemma mollifier_coefficient_translation:
  fixes v :: "'a::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
    and fm: "f \<in> borel_measurable (lebesgue_on ((+) v ` S))"
  shows "mollifier_coefficient ((+) v ` S) f k (v+x) (v+y) =
    mollifier_coefficient S (\<lambda>z. f (v+z)) k x y"
  unfolding mollifier_coefficient_def mollified_target_def[symmetric]
  by (simp only: mollified_target_translation[OF S fm])

(* Theorem 5.4, constructive proof using (5.1): integral coefficients on the original translated domain.
   Endpoint samples and midpoint/exterior radial centers are all translated by v. *)
definition translated_mollifier_network where
  "translated_mollifier_network act f v r0 a b k N w z =
    (\<Sum>c\<in>column_index r0 N. \<Sum>j\<in>{1..N}.
      mollifier_coefficient {y. \<forall>r. y$r \<in> {v$r+a..v$r+b}} f k
        (v+sample_point r0 (unif_part a b N) c j)
        (v+sample_point r0 (unif_part a b N) c (j-1)) *
      act (w * column_sign r0 (unif_part a b N) c j (z-v) *
        norm (z-(v+grid_point r0 (unif_part a b N) c j)))) +
    (\<Sum>c\<in>column_index r0 N.
      (\<integral>y. mollifier k (v+sample_point r0 (unif_part a b N) c 0-y)*f y
        \<partial>(lebesgue_on {y. \<forall>r. y$r \<in> {v$r+a..v$r+b}})) *
      act (w * column_sign r0 (unif_part a b N) c 0 (z-v) *
        norm (z-(v+sigma_anchor r0 (unif_part a b N) c 0))))"

(* Theorem 5.4, constructive proof: the displayed coefficients give precisely the translated operator on rho_k * f-tilde. *)
lemma translated_mollifier_network_eq:
  "translated_mollifier_network act f v r0 a b k N w =
    translated_multivariate_network act
      (mollified_target {y. \<forall>r. y$r \<in> {v$r+a..v$r+b}} f k) v r0 a b N w"
  by (rule ext) (simp add: translated_mollifier_network_def translated_multivariate_network_def
      multivariate_network_def mollifier_coefficient_def mollified_target_def
      algebra_simps)

(* Theorem 5.4: general completed-Lebesgue Lp targets on the paper's independently translated coordinate intervals,
   using the original target's explicit mollifier-integral coefficients for every sufficiently large k. *)
theorem translated_mollifier_approximation:
  fixes f :: "(real,'n::finite) vec \<Rightarrow> real" and v :: "(real,'n) vec" and r0 :: 'n
  assumes sig: "sigmoidal act" and bnd: "bounded_function act"
    and sm: "act \<in> borel_measurable borel" and ab: "a < b" and p: "1 \<le> p"
    and fm: "f \<in> borel_measurable (lebesgue_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}})"
    and fpi: "integrable (lebesgue_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}}) (\<lambda>x. \<bar>f x\<bar> powr p)"
    and e: "0 < e"
  shows "\<exists>K>0. \<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}})
      (\<lambda>x. translated_mollifier_network act f v r0 a b k N w x-f x) < ennreal e"
proof -
  let ?T = "{z::(real,'n) vec. \<forall>r. z$r \<in> {v$r+a..v$r+b}}"
  let ?A = "\<lambda>g N w. translated_multivariate_network act g v r0 a b N w"
  have T: "?T = cbox (v+(\<chi> r. a)) (v+(\<chi> r. b))" by (auto simp: mem_box_cart)
  have Tb: "bounded ?T" unfolding T by (rule bounded_cbox)
  have Tm: "?T \<in> sets borel" unfolding T by simp
  have approx: "\<And>g d. continuous_on ?T g \<Longrightarrow> 0 < d \<Longrightarrow>
      \<exists>N w. 0 < N \<and> 0 < w \<and> Lp_enorm p (lebesgue_on ?T) (\<lambda>x. ?A g N w x-g x) < ennreal d"
    by (rule translated_multivariate_Lp_approximation[OF sig bnd sm ab _ p])
  have Am: "\<And>g N w. ?A g N w \<in> borel_measurable (lebesgue_on ?T)"
    by (rule borel_measurable_lebesgue_onI[OF translated_multivariate_network_measurable[OF sm]])
  show ?thesis unfolding translated_mollifier_network_eq
    by (rule mollified_network_approximation[OF p Tb Tm fm fpi e approx Am])
qed


(* Theorem 5.4, construction: translating the explicit coefficient network agrees with normalization of the original target. *)
lemma translated_mollifier_network_translation:
  fixes f :: "(real,'n::finite) vec \<Rightarrow> real" and v :: "(real,'n) vec"
  assumes fm: "f \<in> borel_measurable (lebesgue_on {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}})"
  shows "translated_mollifier_network act f v r0 a b k N w z =
    multivariate_mollifier_network act (\<lambda>y. f (v+y)) r0 a b k N w (z-v)"
proof -
  let ?Q = "{z::(real,'n) vec. \<forall>r. z$r \<in> {a..b}}"
  have Q: "?Q = cbox (\<chi> r. a) (\<chi> r. b)" by (auto simp: mem_box_cart)
  have Qm: "?Q \<in> sets lebesgue" unfolding Q by simp
  have fm': "f \<in> borel_measurable (lebesgue_on ((+) v ` ?Q))"
    using fm by (simp only: translated_box)
  have eq: "(\<lambda>x. mollified_target {z. \<forall>r. z$r \<in> {v$r+a..v$r+b}} f k (v+x)) =
      mollified_target ?Q (\<lambda>y. f (v+y)) k"
    by (rule ext) (use mollified_target_translation[OF Qm fm'] in
        \<open>simp only: translated_box\<close>)
  show ?thesis unfolding translated_mollifier_network_eq
      translated_multivariate_network_def multivariate_mollifier_network_eq
    by (simp only: eq)
qed

(* Auxiliary domain identity for Theorems 5.1 and 5.3-5.4: the paper's literal square [a,b] x [c,d].
   False denotes the first coordinate and True the second; the side lengths are equal. *)
lemma square_translated_box:
  assumes sides: "b-a = d-c"
  shows "{z::(real,bool) vec. \<forall>r.
      z$r \<in> {(\<chi> s. if s then c-a else 0)$r+a..(\<chi> s. if s then c-a else 0)$r+b}} =
    {z. z$False \<in> {a..b} \<and> z$True \<in> {c..d}}"
proof -
  have hi: "c-a+b = d" using sides by linarith
  show ?thesis by (auto simp: all_bool_eq hi)
qed

(* Theorem 5.3: literal two-dimensional square [a,b] x [c,d], b-a = d-c, with the translated equation (5.1) operator. *)
corollary square_Lp_approximation:
  fixes f :: "(real,bool) vec \<Rightarrow> real"
  assumes sig: "sigmoidal act" and bnd: "bounded_function act"
    and sm: "act \<in> borel_measurable borel" and ab: "a < b" and sides: "b-a = d-c"
    and fc: "continuous_on {z. z$False \<in> {a..b} \<and> z$True \<in> {c..d}} f"
    and p: "1 \<le> p" and e: "0 < e"
  shows "\<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {z. z$False \<in> {a..b} \<and> z$True \<in> {c..d}})
      (\<lambda>z. translated_multivariate_network act f (\<chi> r. if r then c-a else 0)
        True a b N w z-f z) < ennreal e"
proof -
  have fc': "continuous_on {z::(real,bool) vec. \<forall>r.
      z$r \<in> {(\<chi> s. if s then c-a else 0)$r+a..(\<chi> s. if s then c-a else 0)$r+b}} f"
    using fc by (simp only: square_translated_box[OF sides])
  show ?thesis using translated_multivariate_Lp_approximation[OF sig bnd sm ab fc' p e]
    by (simp only: square_translated_box[OF sides])
qed

(* Theorem 5.4: literal two-dimensional square [a,b] x [c,d], with general Lp targets and the explicit integral coefficients. *)
corollary square_mollifier_approximation:
  fixes f :: "(real,bool) vec \<Rightarrow> real"
  assumes sig: "sigmoidal act" and bnd: "bounded_function act"
    and sm: "act \<in> borel_measurable borel" and ab: "a < b" and sides: "b-a = d-c" and p: "1 \<le> p"
    and fm: "f \<in> borel_measurable (lebesgue_on {z. z$False \<in> {a..b} \<and> z$True \<in> {c..d}})"
    and fpi: "integrable (lebesgue_on {z. z$False \<in> {a..b} \<and> z$True \<in> {c..d}}) (\<lambda>x. \<bar>f x\<bar> powr p)"
    and e: "0 < e"
  shows "\<exists>K>0. \<forall>k\<ge>K. \<exists>N w. 0 < N \<and> 0 < w \<and>
    Lp_enorm p (lebesgue_on {z. z$False \<in> {a..b} \<and> z$True \<in> {c..d}})
      (\<lambda>z. translated_mollifier_network act f (\<chi> r. if r then c-a else 0)
        True a b k N w z-f z) < ennreal e"
proof -
  let ?T = "{z::(real,bool) vec. \<forall>r.
    z$r \<in> {(\<chi> s. if s then c-a else 0)$r+a..(\<chi> s. if s then c-a else 0)$r+b}}"
  have fm': "f \<in> borel_measurable (lebesgue_on ?T)"
    using fm by (simp only: square_translated_box[OF sides])
  have fpi': "integrable (lebesgue_on ?T) (\<lambda>x. \<bar>f x\<bar> powr p)"
    using fpi by (simp only: square_translated_box[OF sides])
  show ?thesis using translated_mollifier_approximation[OF sig bnd sm ab p fm' fpi' e]
    by (simp only: square_translated_box[OF sides])
qed

end
