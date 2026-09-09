theory Bacon_Source_Relational_Bounded_Classicism_Category
  imports Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean
    Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality
    Bacon_Source_Relational_Modalized_Functionality Bacon_Source_Relational_Intensional_Reverse
begin

section \<open>The actual bounded category of native Classicism models\<close>

abbreviation paper_R_bounded_classicism_models ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'v set \<Rightarrow> ('c,'v) paper_bbk_model_data set" where
  "paper_R_bounded_classicism_models \<Sigma> G U \<equiv>
    paper_R_bounded_theory_models \<Sigma> G U {A. paper_R_classicism_proves \<Sigma> G A}"

abbreviation paper_R_bounded_classicism_arrows ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'v set \<Rightarrow> ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_bounded_classicism_arrows \<Sigma> G U \<equiv>
    paper_R_bounded_theory_arrows \<Sigma> G U {A. paper_R_classicism_proves \<Sigma> G A}"

lemma paper_R_bounded_classicism_subcategory:
  "paper_R_bbk_subcategory \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U)"
  using paper_R_bounded_theory_models_subcategory[where \<Sigma>=\<Sigma> and G=G and U=U
    and T="{A. paper_R_classicism_proves \<Sigma> G A}"]
  unfolding paper_R_bbk_canonical_subcategory_def by blast

theorem paper_R_bounded_classicism_category:
  "paper_category (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U)
    paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
  by (rule paper_R_bounded_theory_models_category)

theorem paper_R_bounded_classicism_quasi_fregean:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_bbk_quasi_fregean_on (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U)"
  by (rule paper_R_bounded_theory_quasi_fregean[
    OF infinite names paper_R_classicism_is_H_theory paper_R_classicism_is_PE_closed[OF rich]])

lemma paper_R_bounded_classicism_modal_functionality_valid:
  assumes rich: "paper_R_rich G" and object: "M \<in> paper_R_bounded_classicism_models \<Sigma> G U"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G z = \<sigma>" and freshF: "z \<notin> named_fv F" and freshH: "z \<notin> named_fv H"
  shows "paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (named_paper_imp G
      (paper_R_named_box G (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H))"
proof -
  have derivation: "paper_R_classicism_proves \<Sigma> G
      (named_paper_imp G
        (paper_R_named_box G (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
        (named_paper_eq (Arr \<sigma> \<tau>) F H))"
    by (rule paper_R_classicism_modalized_functionality[OF rich fl hl variable freshF freshH])
  show ?thesis by (rule paper_R_bounded_theory_models_truth[OF object]; simp only: mem_Collect_eq; rule derivation)
qed

theorem paper_R_bounded_classicism_quasi_functional:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_R_quasi_functional_on \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U)"
proof (rule paper_R_quasi_functional_from_modal_functionality[
    OF paper_R_bounded_classicism_subcategory paper_R_bounded_classicism_quasi_fregean[OF infinite names rich]])
  fix M \<sigma> \<tau> F H z
  assume object: "M \<in> paper_R_bounded_classicism_models \<Sigma> G U"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G z = \<sigma>" and freshF: "z \<notin> named_fv F" and freshH: "z \<notin> named_fv H"
  show "paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (named_paper_imp G
      (paper_R_named_box G (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H))"
    by (rule paper_R_bounded_classicism_modal_functionality_valid[OF rich object fl hl variable freshF freshH])
qed

theorem paper_R_bounded_classicism_intensional:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_R_intensional_on \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U)"
  by (rule paper_R_quasi_conditions_imply_intensional[OF paper_R_bounded_classicism_subcategory
    paper_R_bounded_classicism_quasi_fregean[OF infinite names rich]
    paper_R_bounded_classicism_quasi_functional[OF infinite names rich]])

text \<open>
  The object set contains the normalized bounded models of the native
  C theorem set, and the arrow set contains all normalized homomorphisms
  between them. Modalized Functionality is valid by THEOREM MEMBERSHIP
  in each object's defining theory, not by an assumed C soundness or
  completeness theorem. Its independently derived semantic consequence
  combines with quasi-Fregeanness to give intensionality.
  Source: Theorem 3.12, pp.51–52, including n.72–73.
\<close>

end
