theory Goodman_Exact_M7_Transfer
  imports Goodman_Exact_M2_Transfer Goodman_Exact_Generic_Fun_Prime
    Goodman_Exact_M3_Extreme_Views
    Goodman_Integration_Exact_L2.Goodman_Exact_Kind_Root
begin

section \<open>The branch-complement diagonal for the complete exact logical stock\<close>

definition gi_exact_M7_operator_enum :: "nat \<Rightarrow> pp_e_operator" where
  "gi_exact_M7_operator_enum = from_nat_into pp_e_exact_operator_stock"

lemma gi_exact_M7_operator_enum_range:
  "range gi_exact_M7_operator_enum = pp_e_exact_operator_stock"
proof -
  have nonempty: "pp_e_exact_operator_stock \<noteq> {}" using pp_e_exact_identity_in_stock by blast
  show ?thesis unfolding gi_exact_M7_operator_enum_def
    by (rule range_from_nat_into[OF nonempty pp_e_exact_operator_stock_countable])
qed

lemma gi_exact_M7_operator_enum_member:
  "gi_exact_M7_operator_enum n \<in> pp_e_exact_operator_stock"
proof -
  have "gi_exact_M7_operator_enum n \<in> range gi_exact_M7_operator_enum" by (rule rangeI)
  then show ?thesis by (simp only: gi_exact_M7_operator_enum_range)
qed

definition gi_exact_M7_diagonal :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_exact_M7_diagonal r =
    pp_glued_witness (\<lambda>n. - pp_view [n] (gi_exact_M7_operator_enum n r))"

lemma gi_exact_M7_diagonal_view:
  "pp_view [n] (gi_exact_M7_diagonal r) = - pp_view [n] (gi_exact_M7_operator_enum n r)"
  unfolding gi_exact_M7_diagonal_def by (rule pp_view_glued_witness)

theorem gi_exact_M7_diagonal_differs:
  "gi_exact_M7_diagonal r \<noteq> gi_exact_M7_operator_enum n r"
proof
  assume same: "gi_exact_M7_diagonal r = gi_exact_M7_operator_enum n r"
  have opposite: "[] \<in> pp_view [n] (gi_exact_M7_diagonal r) \<longleftrightarrow>
    [] \<notin> pp_view [n] (gi_exact_M7_operator_enum n r)"
    by (simp only: gi_exact_M7_diagonal_view Compl_iff)
  have impossible: "[] \<in> pp_view [n] (gi_exact_M7_operator_enum n r) \<longleftrightarrow>
    [] \<notin> pp_view [n] (gi_exact_M7_operator_enum n r)"
    using opposite by (simp only: same)
  show False using impossible by blast
qed

theorem gi_exact_M7_diagonal_outside_logical_range:
  assumes stock: "F \<in> pp_e_exact_operator_stock"
  shows "F r \<noteq> gi_exact_M7_diagonal r"
proof -
  have "F \<in> range gi_exact_M7_operator_enum" using stock by (simp only: gi_exact_M7_operator_enum_range)
  then obtain n where fn: "gi_exact_M7_operator_enum n = F" by blast
  show ?thesis using gi_exact_M7_diagonal_differs[of r n] by (simp only: fn; blast)
qed

definition gi_exact_M7_diagonal_value :: "ZF \<Rightarrow> ZF" where
  "gi_exact_M7_diagonal_value R = pp_n_bacon_embed (gi_exact_M7_diagonal (pp_n_bacon_extract R))"

lemma gi_exact_M7_diagonal_value_member:
  "gi_exact_M7_diagonal_value R \<in> gi_exact_domain Prop"
  unfolding gi_exact_M7_diagonal_value_def
  using pp_n_bacon_embed_in_domain by (simp add: gi_exact_domain_member)

theorem gi_exact_M7_diagonal_value_unreachable:
  assumes rm: "R \<in> gi_exact_domain Prop"
    and pure: "pp_e_closed_logical_stock gb_unary [] F"
  shows "F \<acute> R \<noteq> gi_exact_M7_diagonal_value R"
proof
  assume reaches: "F \<acute> R = gi_exact_M7_diagonal_value R"
  have fm: "Elem F (pp_e_domain gb_unary)" using pure unfolding pp_e_closed_logical_stock_def by blast
  have r: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have fs: "pp_e_raw_operator F \<in> pp_e_exact_operator_stock"
    using pure by (simp only: gi_exact_raw_stock_iff[OF fm])
  have raw: "pp_e_raw_operator F (pp_n_bacon_extract R) = gi_exact_M7_diagonal (pp_n_bacon_extract R)"
    by (simp only: gi_exact_raw_at_extract[OF r] reaches gi_exact_M7_diagonal_value_def pp_n_bacon_extract_embed)
  show False using raw gi_exact_M7_diagonal_outside_logical_range[OF fs, of "pp_n_bacon_extract R"] by contradiction
qed

theorem gi_native_M7_logical_unary_completeness_fails:
  assumes rich: "sg_rich G" and rm: "R \<in> gi_exact_domain Prop"
  shows "\<exists>Q\<in>gi_exact_domain Prop. \<forall>F.
    gi_exact_native_logical_stock G gb_unary [] F \<longrightarrow> F \<acute> R \<noteq> Q"
proof (rule bexI[where x="gi_exact_M7_diagonal_value R"])
  show "\<forall>F. gi_exact_native_logical_stock G gb_unary [] F \<longrightarrow>
    F \<acute> R \<noteq> gi_exact_M7_diagonal_value R"
  proof (intro allI impI)
    fix F assume pure: "gi_exact_native_logical_stock G gb_unary [] F"
    have old: "pp_e_closed_logical_stock gb_unary [] F"
      using pure by (simp only: gi_exact_native_stock_iff_original[OF rich])
    show "F \<acute> R \<noteq> gi_exact_M7_diagonal_value R" by (rule gi_exact_M7_diagonal_value_unreachable[OF rm old])
  qed
  show "gi_exact_M7_diagonal_value R \<in> gi_exact_domain Prop" by (rule gi_exact_M7_diagonal_value_member)
qed

lemma gi_exact_M7_pure_proposition_constant_realization:
  assumes rm: "R \<in> gi_exact_domain Prop" and pure: "pp_e_closed_logical_stock Prop [] Q"
  shows "\<exists>F. pp_e_closed_logical_stock gb_unary [] F \<and> F \<acute> R = Q"
proof -
  obtain M where mt: "[] \<turnstile> M : Prop" and ml: "pp_logical_vocabulary M"
    and denotation: "Q = pp_e_closed_den M"
    using pure by (simp only: gi_exact_root_logical_stock; blast)
  let ?K = "Lam Prop (shift M)"
  have kt: "[] \<turnstile> ?K : gb_unary" by (rule has_type.Lam[OF typed_shift_ctx[OF mt]])
  have kl: "pp_logical_vocabulary ?K"
    using ml by (simp add: pp_logical_vocabulary_def shift_def consts_of_rename)
  have stock: "pp_e_closed_logical_stock gb_unary [] (pp_e_closed_den ?K)"
    by (rule pp_e_closed_logical_stockI[OF kt kl])
  have r: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have r_power: "Elem R (Power Nat)" using r by (simp only: pp_b_domain.simps)
  have application: "pp_e_closed_den ?K \<acute> R = Q"
    by (simp add: pp_e_closed_den_def denotation Lambda_app[OF r_power] pp_e_eval_shift)
  show ?thesis by (rule exI[where x="pp_e_closed_den ?K"], rule conjI[OF stock application])
qed

theorem gi_exact_M7_diagonal_not_pure_proposition:
  assumes rm: "R \<in> gi_exact_domain Prop"
  shows "\<not> pp_e_closed_logical_stock Prop [] (gi_exact_M7_diagonal_value R)"
proof
  assume pure: "pp_e_closed_logical_stock Prop [] (gi_exact_M7_diagonal_value R)"
  obtain F where fs: "pp_e_closed_logical_stock gb_unary [] F"
    and reaches: "F \<acute> R = gi_exact_M7_diagonal_value R"
    using gi_exact_M7_pure_proposition_constant_realization[OF rm pure] by blast
  show False using reaches gi_exact_M7_diagonal_value_unreachable[OF rm fs] by contradiction
qed

theorem gi_native_M7_zeroary_unary_completeness_fails:
  assumes rich: "sg_rich G" and rm: "R \<in> gi_exact_domain Prop"
  shows "\<exists>Q\<in>gi_exact_domain Prop. \<not> gi_exact_native_logical_stock G Prop [] Q \<and>
    (\<forall>F. gi_exact_native_logical_stock G gb_unary [] F \<longrightarrow> F \<acute> R \<noteq> Q)"
proof -
  have not_pure: "\<not> gi_exact_native_logical_stock G Prop [] (gi_exact_M7_diagonal_value R)"
    by (simp only: gi_exact_native_stock_iff_original[OF rich]; rule gi_exact_M7_diagonal_not_pure_proposition[OF rm])
  have no_image: "F \<acute> R \<noteq> gi_exact_M7_diagonal_value R"
    if fs: "gi_exact_native_logical_stock G gb_unary [] F" for F
  proof -
    have old: "pp_e_closed_logical_stock gb_unary [] F"
      using fs by (simp only: gi_exact_native_stock_iff_original[OF rich])
    show ?thesis by (rule gi_exact_M7_diagonal_value_unreachable[OF rm old])
  qed
  show ?thesis
  proof (rule bexI[where x="gi_exact_M7_diagonal_value R"])
    show "\<not> gi_exact_native_logical_stock G Prop [] (gi_exact_M7_diagonal_value R) \<and>
      (\<forall>F. gi_exact_native_logical_stock G gb_unary [] F \<longrightarrow> F \<acute> R \<noteq> gi_exact_M7_diagonal_value R)"
      using not_pure no_image by blast
    show "gi_exact_M7_diagonal_value R \<in> gi_exact_domain Prop"
      by (rule gi_exact_M7_diagonal_value_member)
  qed
qed

section \<open>All invariant targets are reachable exactly when the orbit map is injective\<close>

definition gi_exact_M7_invariant_reachable :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "gi_exact_M7_invariant_reachable R Q \<longleftrightarrow>
    (\<exists>F\<in>gi_exact_M2_invariant_stock. F \<acute> R = Q)"

lemma gi_exact_M7_invariant_raw_equivariant:
  assumes stock: "F \<in> gi_exact_M2_invariant_stock"
  shows "pp_equivariant_operator (pp_e_raw_operator F)"
proof -
  have fm: "Elem F (pp_e_domain gb_unary)" and invariant: "\<And>i. pp_b_action gb_unary i F = F"
    using stock unfolding gi_exact_M2_invariant_stock_def by blast+
  show ?thesis by (rule pp_e_raw_operator_equivariant[OF fm invariant])
qed

lemma gi_exact_M7_invariant_reachable_iff_classifier:
  assumes rm: "R \<in> gi_exact_domain Prop" and qm: "Q \<in> gi_exact_domain Prop"
  shows "gi_exact_M7_invariant_reachable R Q \<longleftrightarrow>
    (\<exists>S. pp_classifier S (pp_n_bacon_extract R) = pp_n_bacon_extract Q)"
proof
  assume reachable: "gi_exact_M7_invariant_reachable R Q"
  then obtain F where fs: "F \<in> gi_exact_M2_invariant_stock" and reaches: "F \<acute> R = Q"
    unfolding gi_exact_M7_invariant_reachable_def by blast
  have r: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have raw: "pp_e_raw_operator F = pp_classifier (pp_operator_index (pp_e_raw_operator F))"
    by (rule pp_equivariant_operator_is_classifier[OF gi_exact_M7_invariant_raw_equivariant[OF fs]])
  have image: "pp_classifier (pp_operator_index (pp_e_raw_operator F)) (pp_n_bacon_extract R) = pp_n_bacon_extract Q"
    by (simp only: raw[symmetric] gi_exact_raw_at_extract[OF r] reaches)
  show "\<exists>S. pp_classifier S (pp_n_bacon_extract R) = pp_n_bacon_extract Q"
    by (rule exI[where x="pp_operator_index (pp_e_raw_operator F)"], rule image)
next
  assume represented: "\<exists>S. pp_classifier S (pp_n_bacon_extract R) = pp_n_bacon_extract Q"
  then obtain S where image: "pp_classifier S (pp_n_bacon_extract R) = pp_n_bacon_extract Q" by blast
  let ?F = "gi_exact_M2_classifier S"
  have r: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have fm: "Elem ?F (pp_e_domain gb_unary)" by (rule gi_exact_M2_classifier_member)
  have fr: "Elem (?F \<acute> R) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF fm r])
  have fr_power: "Elem (?F \<acute> R) (Power Nat)" using fr by (simp only: pp_b_domain.simps)
  have q_power: "Elem Q (Power Nat)" using qm by (simp only: gi_exact_domain_member pp_b_domain.simps)
  have same: "pp_n_bacon_extract (?F \<acute> R) = pp_n_bacon_extract Q"
    using image by (simp only: gi_exact_M2_classifier_raw[symmetric] gi_exact_raw_at_extract[OF r])
  have reaches: "?F \<acute> R = Q" by (rule pp_n_bacon_extract_injective_on_domain[OF fr_power q_power same])
  show "gi_exact_M7_invariant_reachable R Q" unfolding gi_exact_M7_invariant_reachable_def
    using gi_exact_M2_classifier_in_stock[of S] reaches by blast
qed

lemma gi_exact_M7_orbit_image_classifier:
  assumes injective: "inj (\<lambda>i. pp_view i r)"
  shows "pp_classifier ((\<lambda>i. pp_view i r) ` P) r = P"
proof (rule set_eqI)
  fix i
  show "i \<in> pp_classifier ((\<lambda>i. pp_view i r) ` P) r \<longleftrightarrow> i \<in> P"
  proof
    assume member: "i \<in> pp_classifier ((\<lambda>i. pp_view i r) ` P) r"
    then obtain j where jp: "j \<in> P" and same: "pp_view i r = pp_view j r"
      unfolding pp_classifier_def by blast
    have ij: "i = j" by (rule injD[OF injective same])
    show "i \<in> P" using jp by (simp only: ij)
  next
    assume "i \<in> P"
    then show "i \<in> pp_classifier ((\<lambda>i. pp_view i r) ` P) r"
      unfolding pp_classifier_def by (auto intro: imageI)
  qed
qed

theorem gi_exact_M7_all_invariant_reachable_iff_orbit_injective:
  assumes rm: "R \<in> gi_exact_domain Prop"
  shows "(\<forall>Q\<in>gi_exact_domain Prop. gi_exact_M7_invariant_reachable R Q)
    \<longleftrightarrow> inj (\<lambda>i. pp_view i (pp_n_bacon_extract R))"
proof
  assume all: "\<forall>Q\<in>gi_exact_domain Prop. gi_exact_M7_invariant_reachable R Q"
  show "inj (\<lambda>i. pp_view i (pp_n_bacon_extract R))"
  proof (rule injI)
    fix i j assume same: "pp_view i (pp_n_bacon_extract R) = pp_view j (pp_n_bacon_extract R)"
    have qm: "pp_n_bacon_embed {i} \<in> gi_exact_domain Prop"
      using pp_n_bacon_embed_in_domain[of "{i}"] by (simp add: gi_exact_domain_member)
    have reached: "gi_exact_M7_invariant_reachable R (pp_n_bacon_embed {i})" using all qm by blast
    obtain S where singleton: "pp_classifier S (pp_n_bacon_extract R) = {i}"
      using reached gi_exact_M7_invariant_reachable_iff_classifier[OF rm qm] by auto
    have i_mem: "pp_view i (pp_n_bacon_extract R) \<in> S"
      using singleton by (metis pp_classifier_def mem_Collect_eq singletonI)
    have j_mem: "j \<in> pp_classifier S (pp_n_bacon_extract R)"
      using i_mem by (simp only: pp_classifier_def mem_Collect_eq same)
    show "i = j" using j_mem by (simp only: singleton singleton_iff; blast)
  qed
next
  assume injective: "inj (\<lambda>i. pp_view i (pp_n_bacon_extract R))"
  show "\<forall>Q\<in>gi_exact_domain Prop. gi_exact_M7_invariant_reachable R Q"
  proof (intro ballI)
    fix Q assume qm: "Q \<in> gi_exact_domain Prop"
    have classifier: "pp_classifier ((\<lambda>i. pp_view i (pp_n_bacon_extract R)) ` pp_n_bacon_extract Q)
      (pp_n_bacon_extract R) = pp_n_bacon_extract Q"
      by (rule gi_exact_M7_orbit_image_classifier[OF injective])
    have exists: "\<exists>S. pp_classifier S (pp_n_bacon_extract R) = pp_n_bacon_extract Q"
      by (rule exI[where x="(\<lambda>i. pp_view i (pp_n_bacon_extract R)) ` pp_n_bacon_extract Q"], rule classifier)
    show "gi_exact_M7_invariant_reachable R Q" using exists
      by (simp only: gi_exact_M7_invariant_reachable_iff_classifier[OF rm qm])
  qed
qed

section \<open>Every fun′ seed has an explicitly noninjective orbit map\<close>

theorem gi_exact_M7_fun_prime_orbit_collision:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "\<exists>i j. i \<noteq> j \<and> pp_view i r = pp_view j r"
proof -
  have top_orbit: "UNIV \<in> pp_orbit r"
    using gi_exact_M3_fun_prime_has_extreme_views[OF fp] by blast
  obtain i where top: "pp_view i r = UNIV" using top_orbit unfolding pp_orbit_def by blast
  have next_view: "pp_view (0 # i) r = UNIV"
  proof -
    have "pp_view (0 # i) r = pp_view [0] (pp_view i r)" by (simp add: pp_view_compose)
    also have "... = UNIV" by (simp only: top; simp add: pp_view_def)
    finally show ?thesis .
  qed
  have distinct: "i \<noteq> 0 # i"
  proof
    assume same: "i = 0 # i"
    have "length i = Suc (length i)" using arg_cong[OF same, of length] by simp
    then show False by simp
  qed
  show ?thesis by (rule exI[where x=i], rule exI[where x="0 # i"])
    (use distinct top next_view in blast)
qed

corollary gi_exact_M7_fun_prime_orbit_not_injective:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "\<not> inj (\<lambda>i. pp_view i r)"
proof
  assume injective: "inj (\<lambda>i. pp_view i r)"
  obtain i j where distinct: "i \<noteq> j" and same: "pp_view i r = pp_view j r"
    using gi_exact_M7_fun_prime_orbit_collision[OF fp] by blast
  have "i = j" by (rule injD[OF injective same])
  then show False using distinct by contradiction
qed

lemma gi_exact_M7_collision_blocks_singleton:
  assumes distinct: "i \<noteq> j" and same: "pp_view i r = pp_view j r"
    and equivariant: "pp_equivariant_operator F"
  shows "F r \<noteq> {i}"
proof
  assume reaches: "F r = {i}"
  have left: "pp_view i (F r) = F (pp_view i r)"
    and right: "pp_view j (F r) = F (pp_view j r)"
    using equivariant unfolding pp_equivariant_operator_def by blast+
  have output_views: "pp_view i (F r) = pp_view j (F r)" using left right same by simp
  have root_membership: "[] \<in> pp_view i {i} \<longleftrightarrow> [] \<in> pp_view j {i}"
    using output_views by (simp only: reaches)
  show False using root_membership distinct by (simp add: pp_view_def)
qed

theorem gi_exact_M7_fun_prime_singleton_unreachable:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "\<exists>i. \<forall>F\<in>gi_exact_M2_invariant_stock. pp_e_raw_operator F r \<noteq> {i}"
proof -
  obtain i j where distinct: "i \<noteq> j" and same: "pp_view i r = pp_view j r"
    using gi_exact_M7_fun_prime_orbit_collision[OF fp] by blast
  show ?thesis
  proof (rule exI[where x=i], intro ballI)
    fix F assume stock: "F \<in> gi_exact_M2_invariant_stock"
    show "pp_e_raw_operator F r \<noteq> {i}"
      by (rule gi_exact_M7_collision_blocks_singleton[OF distinct same
        gi_exact_M7_invariant_raw_equivariant[OF stock]])
  qed
qed

theorem gi_exact_M7_fun_prime_exact_invariant_unreachable:
  assumes rm: "R \<in> gi_exact_domain Prop" and fp: "pp_e_exact_fun_prime (pp_n_bacon_extract R)"
  shows "\<exists>i. pp_n_bacon_embed {i} \<in> gi_exact_domain Prop \<and>
    (\<forall>F\<in>gi_exact_M2_invariant_stock. F \<acute> R \<noteq> pp_n_bacon_embed {i})"
proof -
  obtain i where no_raw: "\<forall>F\<in>gi_exact_M2_invariant_stock. pp_e_raw_operator F (pp_n_bacon_extract R) \<noteq> {i}"
    using gi_exact_M7_fun_prime_singleton_unreachable[OF fp] by blast
  have qm: "pp_n_bacon_embed {i} \<in> gi_exact_domain Prop"
    using pp_n_bacon_embed_in_domain[of "{i}"] by (simp add: gi_exact_domain_member)
  have r: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have no_exact: "F \<acute> R \<noteq> pp_n_bacon_embed {i}" if stock: "F \<in> gi_exact_M2_invariant_stock" for F
  proof
    assume reaches: "F \<acute> R = pp_n_bacon_embed {i}"
    have raw: "pp_e_raw_operator F (pp_n_bacon_extract R) = {i}"
      by (simp only: gi_exact_raw_at_extract[OF r] reaches pp_n_bacon_extract_embed)
    show False using no_raw stock raw by blast
  qed
  show ?thesis by (rule exI[where x=i]) (use qm no_exact in blast)
qed

corollary gi_exact_M7_generic_orbit_not_injective:
  "\<not> inj (\<lambda>i. pp_view i pp_e_generic_raw_seed)"
  by (rule gi_exact_M7_fun_prime_orbit_not_injective[OF gi_exact_generic_raw_seed_fun_prime])

theorem gi_exact_M7_generic_invariant_unreachable:
  "\<exists>Q\<in>gi_exact_domain Prop. \<not> gi_exact_M7_invariant_reachable pp_e_generic_root_seed Q"
proof -
  have rm: "pp_e_generic_root_seed \<in> gi_exact_domain Prop"
    using pp_e_generic_root_seed_in_domain by (simp only: gi_exact_domain_member)
  obtain i where qm: "pp_n_bacon_embed {i} \<in> gi_exact_domain Prop"
    and no_image: "\<forall>F\<in>gi_exact_M2_invariant_stock. F \<acute> pp_e_generic_root_seed \<noteq> pp_n_bacon_embed {i}"
    using gi_exact_M7_fun_prime_exact_invariant_unreachable[OF rm gi_exact_generic_root_seed_fun_prime] by blast
  show ?thesis by (rule bexI[where x="pp_n_bacon_embed {i}"])
    (use no_image qm in \<open>auto simp only: gi_exact_M7_invariant_reachable_def\<close>)
qed

corollary gi_exact_M7_generic_fundamental_invariant_incomplete:
  assumes rm: "R \<in> gi_exact_domain Prop" and fundamental: "pp_e_generic_fundamental_at Prop [] R"
  shows "\<exists>Q\<in>gi_exact_domain Prop. \<not> gi_exact_M7_invariant_reachable R Q"
proof -
  have member: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have fp: "pp_e_exact_fun_prime (pp_n_bacon_extract R)"
    by (rule gi_exact_generic_fundamental_root_fun_prime[OF member fundamental])
  obtain i where qm: "pp_n_bacon_embed {i} \<in> gi_exact_domain Prop"
    and no_image: "\<forall>F\<in>gi_exact_M2_invariant_stock. F \<acute> R \<noteq> pp_n_bacon_embed {i}"
    using gi_exact_M7_fun_prime_exact_invariant_unreachable[OF rm fp] by blast
  show ?thesis by (rule bexI[where x="pp_n_bacon_embed {i}"])
    (use no_image qm in \<open>auto simp only: gi_exact_M7_invariant_reachable_def\<close>)
qed

text \<open>
  The countable-stock diagonal works for each typed proposition R. The
  stronger singleton obstruction to ALL invariant operators requires
  fun′(extract R). That premise is proved for the actual generic root
  seed, so its formerly open orbit-injectivity instance is now settled
  negatively. The proof exhibits two DISTINCT substitution words with
  equal views; it does not infer orbit injectivity from a stabilizer.

  Arbitrary propositions can have different orbit behavior. No theorem
  above asserts noninjectivity for every R. The exact general iff and
  the chosen-seed specialization are separate results. These conclusions
  concern the specified exact carriers and stock, not arbitrary enlarged
  Pure interpretations or an arbitrary Theorem 10.1 choice of constants.
\<close>

end
