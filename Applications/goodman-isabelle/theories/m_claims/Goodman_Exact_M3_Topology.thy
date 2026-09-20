theory Goodman_Exact_M3_Topology
  imports Goodman_Exact_M3_Extreme_Views
begin

section \<open>M3: finite cylinders in the product space of propositions\<close>

text \<open>
  This reconstructs the finite-cylinder argument in the historical
  Bacon_PP_Goodman_M3_Complete theory, without importing its unrelated M6
  comparison-model chain. Its final premise is now discharged by the
  extreme-view theorem for the complete exact closed-logical stock.

  A proposition is a subset of pp_word = nat list. The product topology on
  2^(nat list) has basic cylinders fixing finitely many truth coordinates.
  We use the explicit basis definitions of nowhere density and meagerness
  below, not a new Isabelle topological-space instance. Every cylinder is
  nonempty: its defining proposition is itself a member. Thus the refinement
  condition cannot be satisfied by choosing an empty basic open set.
\<close>

definition gi_M3_cylinder :: "pp_word set \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "gi_M3_cylinder F p = {q. \<forall>w \<in> F. (w \<in> q) = (w \<in> p)}"

definition gi_M3_product_nowhere_dense :: "pp_sem_prop set \<Rightarrow> bool" where
  "gi_M3_product_nowhere_dense A \<longleftrightarrow>
    (\<forall>F p. finite F \<longrightarrow>
      (\<exists>G q. finite G \<and> gi_M3_cylinder G q \<subseteq> gi_M3_cylinder F p \<and>
        gi_M3_cylinder G q \<inter> A = {}))"

definition gi_M3_product_meager :: "pp_sem_prop set \<Rightarrow> bool" where
  "gi_M3_product_meager A \<longleftrightarrow>
    (\<exists>N :: nat \<Rightarrow> pp_sem_prop set.
      (\<forall>n. gi_M3_product_nowhere_dense (N n)) \<and> A \<subseteq> \<Union>(range N))"

lemma gi_M3_cylinder_self:
  "p \<in> gi_M3_cylinder F p"
  by (simp add: gi_M3_cylinder_def)

lemma gi_M3_cylinder_nonempty:
  "gi_M3_cylinder F p \<noteq> {}"
  using gi_M3_cylinder_self by blast

lemma gi_M3_product_meager_mono:
  "gi_M3_product_meager B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> gi_M3_product_meager A"
  unfolding gi_M3_product_meager_def by blast

definition gi_M3_necessary_cone :: "pp_word \<Rightarrow> pp_sem_prop set" where
  "gi_M3_necessary_cone i = {p. pp_view i p = UNIV}"

lemma gi_M3_fresh_cone_point:
  fixes F :: "pp_word set" and i :: pp_word
  assumes finite: "finite F"
  obtains x where "x \<notin> F" "\<exists>u. x = u @ i"
proof -
  let ?L = "insert 0 (length ` F)"
  let ?n = "Suc (Max ?L)"
  let ?x = "replicate ?n 0 @ i"
  have finite_lengths: "finite ?L" using finite by simp
  have bound: "length y \<le> Max ?L" if "y \<in> F" for y
  proof -
    have "length y \<in> ?L" using that by blast
    then show ?thesis by (rule Max_ge[OF finite_lengths])
  qed
  have outside: "?x \<notin> F"
  proof
    assume member: "?x \<in> F"
    have "length ?x \<le> Max ?L" by (rule bound[OF member])
    then show False by simp
  qed
  have suffix: "\<exists>u. ?x = u @ i" by blast
  show thesis using outside suffix by (rule that)
qed

lemma gi_M3_necessary_cone_nowhere_dense:
  "gi_M3_product_nowhere_dense (gi_M3_necessary_cone i)"
  unfolding gi_M3_product_nowhere_dense_def
proof (intro allI impI)
  fix F :: "pp_word set" and p :: pp_sem_prop
  assume finite: "finite F"
  obtain x :: pp_word where outside: "x \<notin> F" and suffix: "\<exists>u. x = u @ i"
    by (rule gi_M3_fresh_cone_point[OF finite])
  obtain u where shape: "x = u @ i" using suffix by blast
  let ?G = "insert x F"
  let ?q = "p - {x}"
  have refinement: "gi_M3_cylinder ?G ?q \<subseteq> gi_M3_cylinder F p"
    unfolding gi_M3_cylinder_def using outside by auto
  have disjoint: "gi_M3_cylinder ?G ?q \<inter> gi_M3_necessary_cone i = {}"
  proof (rule equals0I)
    fix a
    assume member: "a \<in> gi_M3_cylinder ?G ?q \<inter> gi_M3_necessary_cone i"
    have false_at_x: "x \<notin> a" using member unfolding gi_M3_cylinder_def by simp
    have top: "pp_view i a = UNIV" using member unfolding gi_M3_necessary_cone_def by simp
    have "u \<in> pp_view i a" using top by simp
    then have "x \<in> a" unfolding pp_view_def using shape by simp
    then show False using false_at_x by contradiction
  qed
  show "\<exists>G q. finite G \<and> gi_M3_cylinder G q \<subseteq> gi_M3_cylinder F p \<and>
    gi_M3_cylinder G q \<inter> gi_M3_necessary_cone i = {}"
    using finite refinement disjoint by (intro exI[of _ ?G] exI[of _ ?q]) simp
qed

definition gi_M3_word_enum :: "nat \<Rightarrow> pp_word" where
  "gi_M3_word_enum = from_nat_into (UNIV :: pp_word set)"

lemma gi_M3_word_enum_surjective:
  "range gi_M3_word_enum = (UNIV :: pp_word set)"
  unfolding gi_M3_word_enum_def by (rule range_from_nat_into) simp_all

theorem gi_M3_top_view_class_is_product_meager:
  assumes top_view: "\<And>p. p \<in> A \<Longrightarrow> UNIV \<in> pp_orbit p"
  shows "gi_M3_product_meager A"
proof -
  let ?N = "\<lambda>n. gi_M3_necessary_cone (gi_M3_word_enum n)"
  have nowhere: "\<forall>n. gi_M3_product_nowhere_dense (?N n)"
    using gi_M3_necessary_cone_nowhere_dense by blast
  have cover: "A \<subseteq> \<Union>(range ?N)"
  proof
    fix p assume member: "p \<in> A"
    have top: "UNIV \<in> pp_orbit p" by (rule top_view[OF member])
    then obtain i where view: "pp_view i p = UNIV" unfolding pp_orbit_def by blast
    have "i \<in> range gi_M3_word_enum" using gi_M3_word_enum_surjective by simp
    then obtain n where index: "gi_M3_word_enum n = i" by blast
    have "p \<in> ?N n" unfolding gi_M3_necessary_cone_def using view index by simp
    then show "p \<in> \<Union>(range ?N)" by blast
  qed
  show ?thesis unfolding gi_M3_product_meager_def
    using nowhere cover by (intro exI[of _ ?N]) blast
qed

section \<open>Instantiation for the complete exact stock\<close>

theorem gi_exact_M3_fun_prime_class_is_product_meager:
  "gi_M3_product_meager {p. pp_e_exact_fun_prime p}"
proof (rule gi_M3_top_view_class_is_product_meager)
  fix p assume "p \<in> {p. pp_e_exact_fun_prime p}"
  then have fp: "pp_e_exact_fun_prime p" by simp
  show "UNIV \<in> pp_orbit p" using gi_exact_M3_fun_prime_has_extreme_views[OF fp] by blast
qed

corollary gi_native_M3_fun_prime_class_is_product_meager:
  assumes rich: "sg_rich G"
  shows "gi_M3_product_meager {p. gi_stock_fun_prime (gi_exact_native_operator_stock G) p}"
  by (simp only: gi_exact_native_fun_prime_iff[OF rich];
    rule gi_exact_M3_fun_prime_class_is_product_meager)

corollary gi_native_M3_free_generator_class_is_product_meager:
  assumes rich: "sg_rich G"
  shows "gi_M3_product_meager {p. gi_M3_free_for_stock (gi_exact_native_operator_stock G) p}"
  using gi_native_M3_fun_prime_class_is_product_meager[OF rich]
  by (simp only: gi_native_M3_fun_prime_iff_free[OF rich])

text \<open>
  Every exact-stock fun′ proposition has a necessary view. For each fixed
  view, the necessary-view class is nowhere dense: a finite specification
  can always be refined by falsifying one as-yet-unfixed coordinate in that
  cone. Countably many words therefore give the required countable cover.
  Only the necessary-view half of the extreme-view theorem is needed here.

  The conclusion concerns the COMPLETE exact logical stock and, by the
  checked denotational correspondence, its native named-language version.
  It is not a theorem about arbitrary Pure enlargements. Algebraic freeness
  is not topological genericity: this particular free-generator class is
  meager in the explicitly defined product topology. We identify no
  particular Theorem-10.1 glued fundamental proposition with that class and
  assert no PP model. The exact-carrier instantiation retains HOL–ZF scope.
\<close>

end
