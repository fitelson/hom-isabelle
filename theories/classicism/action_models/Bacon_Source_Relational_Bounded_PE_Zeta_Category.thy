theory Bacon_Source_Relational_Bounded_PE_Zeta_Category
  imports Bacon_Source_Relational_Classicism_Theory_Minimality
    Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean
    Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality
    Bacon_Source_Relational_Intensional_Reverse Bacon_Source_Relational_Bounded_Theory_Common
begin

section \<open>The bounded model category of an H-theory closed under PE and ζ\<close>

lemma paper_R_bounded_PE_zeta_modal_functionality_valid:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
    and object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G z = \<sigma>" and fresh_F: "z \<notin> named_fv F" and fresh_H: "z \<notin> named_fv H"
  shows "paper_R_bbk_model.paper_R_valid \<Sigma> G
    (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (named_paper_imp G
      (paper_R_named_box G
        (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H))"
proof -
  have member: "named_paper_imp G
      (paper_R_named_box G
        (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H) \<in> T"
    by (rule paper_R_H_PE_zeta_modalized_functionality[
      OF rich theory_h pe zeta fl hl variable fresh_F fresh_H])
  show ?thesis by (rule paper_R_bounded_theory_models_truth[OF object member])
qed

theorem paper_R_bounded_PE_zeta_quasi_functional:
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
  shows "paper_R_quasi_functional_on \<Sigma> G
    (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T)"
proof -
  have category: "paper_R_bbk_subcategory \<Sigma> G
      (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T)"
    by (rule paper_R_bbk_canonical_subcategory_raw[OF paper_R_bounded_theory_models_subcategory])
  have quasi: "paper_bbk_quasi_fregean_on
      (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T)"
    by (rule paper_R_bounded_theory_quasi_fregean[OF infinite names theory_h pe])
  show ?thesis
  proof (rule paper_R_quasi_functional_from_modal_functionality[OF category quasi])
    fix M \<sigma> \<tau> F H z
    assume object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
      and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
      and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
      and variable: "G z = \<sigma>" and fresh_F: "z \<notin> named_fv F" and fresh_H: "z \<notin> named_fv H"
    show "paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
      (named_paper_imp G
        (paper_R_named_box G
          (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
        (named_paper_eq (Arr \<sigma> \<tau>) F H))"
      by (rule paper_R_bounded_PE_zeta_modal_functionality_valid[
        OF rich theory_h pe zeta object fl hl variable fresh_F fresh_H])
  qed
qed

theorem paper_R_bounded_PE_zeta_intensional:
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
  shows "paper_R_intensional_on \<Sigma> G
    (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T)"
  by (rule paper_R_quasi_conditions_imply_intensional[
    OF paper_R_bbk_canonical_subcategory_raw[OF paper_R_bounded_theory_models_subcategory]
      paper_R_bounded_theory_quasi_fregean[OF infinite names theory_h pe]
      paper_R_bounded_PE_zeta_quasi_functional[OF infinite names rich theory_h pe zeta]])

theorem paper_R_bounded_PE_zeta_category_represents:
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
  shows "paper_R_bbk_canonical_subcategory \<Sigma> G
      (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T) \<and>
    paper_R_intensional_on \<Sigma> G
      (paper_R_bounded_theory_models \<Sigma> G U T) (paper_R_bounded_theory_arrows \<Sigma> G U T) \<and>
    paper_R_common_theory \<Sigma> G (paper_R_bounded_theory_models \<Sigma> G U T) = T"
  by (rule conjI[OF paper_R_bounded_theory_models_subcategory],
    rule conjI[OF paper_R_bounded_PE_zeta_intensional[OF infinite names rich theory_h pe zeta]
      paper_R_bounded_models_common_theory[OF infinite names rich theory_h]])

text \<open>
  The objects are the actual normalized bounded models of the supplied
  T, not models of C supplied as a premise. Their common theory is
  exactly T. Modalized Functionality is valid at each object because
  its formula belongs to T by the independent native proof.

  The category may be empty when T is inconsistent; no inhabitation
  premise is added. All objects and arrows remain sets on the fixed
  carrier, with the explicit infinite-U and declared-name bounds.
  Source: the generic-theory argument of Theorem 3.12, pp.51–52,
  n.72–73. No C completeness theorem is used.
\<close>

end
