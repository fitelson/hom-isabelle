theory Bacon_Source_Relational_Bounded_Theory_Models
  imports Bacon_Source_Relational_Category_Interface
    Bacon_Source_Relational_Normalization_Formula_Validity
begin

section \<open>The set of all normalized models of T with domains inside U\<close>

definition paper_R_bounded_theory_models ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'v set \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    ('c,'v) paper_bbk_model_data set" where
  "paper_R_bounded_theory_models \<Sigma> G U T =
    {M. paper_R_bbk_data_valid \<Sigma> G M \<and> paper_R_bbk_data_canonical \<Sigma> G M \<and>
      (\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U \<and>
      (\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
        (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) A)}"

definition paper_R_bounded_theory_arrows ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'v set \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_bounded_theory_arrows \<Sigma> G U T =
    paper_R_bbk_arrows \<Sigma> G (paper_R_bounded_theory_models \<Sigma> G U T)"

lemma paper_R_bounded_theory_modelsI:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and canonical: "paper_R_bbk_data_canonical \<Sigma> G M"
    and bound: "(\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
    and theory_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) A"
  shows "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
  using assms unfolding paper_R_bounded_theory_models_def by blast

lemma paper_R_bounded_theory_models_valid:
  "M \<in> paper_R_bounded_theory_models \<Sigma> G U T \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
  unfolding paper_R_bounded_theory_models_def by blast

lemma paper_R_bounded_theory_models_canonical:
  "M \<in> paper_R_bounded_theory_models \<Sigma> G U T \<Longrightarrow> paper_R_bbk_data_canonical \<Sigma> G M"
  unfolding paper_R_bounded_theory_models_def by blast

lemma paper_R_bounded_theory_models_bound:
  "M \<in> paper_R_bounded_theory_models \<Sigma> G U T \<Longrightarrow> (\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
  unfolding paper_R_bounded_theory_models_def by blast

lemma paper_R_bounded_theory_models_truth:
  assumes object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T" and member: "A \<in> T"
  shows "paper_R_bbk_model.paper_R_valid \<Sigma> G
    (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) A"
  using assms unfolding paper_R_bounded_theory_models_def by blast

theorem paper_R_bounded_theory_models_normalize:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and bound: "(\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
    and theory_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) A"
  shows "paper_R_bbk_normalize \<Sigma> G M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
proof (rule paper_R_bounded_theory_modelsI)
  show "paper_R_bbk_data_valid \<Sigma> G (paper_R_bbk_normalize \<Sigma> G M)"
    by (rule paper_R_bbk_normalize_valid[OF valid])
  show "paper_R_bbk_data_canonical \<Sigma> G (paper_R_bbk_normalize \<Sigma> G M)"
    by (rule paper_R_bbk_normalize_canonical)
  show "(\<Union>\<sigma>. paper_bbk_domain (paper_R_bbk_normalize \<Sigma> G M) \<sigma>) \<subseteq> U"
    by (simp only: paper_R_bbk_normalize_domain; rule bound)
  show "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain (paper_R_bbk_normalize \<Sigma> G M))
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G M))
      (paper_bbk_valuation (paper_R_bbk_normalize \<Sigma> G M)) A"
    by (rule paper_R_bbk_normalizes_theory[OF valid theory_truth])
qed

theorem paper_R_bounded_theory_models_subcategory:
  "paper_R_bbk_canonical_subcategory \<Sigma> G
    (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T)"
proof -
  have models: "paper_R_bbk_data_valid \<Sigma> G M"
    if "M \<in> paper_R_bounded_theory_models \<Sigma> G U T" for M
    by (rule paper_R_bounded_theory_models_valid[OF that])
  have selected: "paper_R_bbk_subcategory \<Sigma> G
      (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T)"
    unfolding paper_R_bounded_theory_arrows_def
    by (rule paper_R_bbk_full_subcategory[OF models])
  show ?thesis unfolding paper_R_bbk_canonical_subcategory_def
    by (rule conjI[OF selected], intro ballI; rule paper_R_bounded_theory_models_canonical; assumption)
qed

corollary paper_R_bounded_theory_models_category:
  "paper_category (paper_R_bounded_theory_models \<Sigma> G U T)
    (paper_R_bounded_theory_arrows \<Sigma> G U T) paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
  by (rule paper_R_bbk_canonical_subcategory_category[OF paper_R_bounded_theory_models_subcategory])

text \<open>
  Objects and arrows are actual HOL sets on fixed carriers. The
  object set contains every canonical represented R model satisfying
  T and the displayed domain bound; arrows contain ALL normalized
  denotation-preserving maps between these objects, without requiring
  preservation of valuation. Source: §3.3 and the refinement on p.52.

  The category theorem has no infinitude, cardinal bound, consistency,
  H-theory or PE premise. The object set may be empty. Inhabitation,
  quasi-Fregeanness and quasi-functionality remain separate results;
  this is not a claim to collect a proper class of varying carriers.
\<close>

end
