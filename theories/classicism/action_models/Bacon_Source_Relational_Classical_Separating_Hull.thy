theory Bacon_Source_Relational_Classical_Separating_Hull
  imports Bacon_Source_Relational_Separating_Hull_Category Bacon_Source_Relational_Bounded_Classicism_Category
begin

section \<open>Generate a separating C-model category around a supplied root\<close>

locale paper_R_classicism_hull =
  fixes signature :: "'c ssignature" and stock :: sgcontext and U :: "'v set"
    and Root :: "('c,'v) paper_bbk_model_data"
  assumes infinite_bound: "infinite U"
    and signature_bound: "card_of (\<Union>\<sigma>. signature \<sigma>) \<le>o card_of U"
    and root_member: "Root \<in> paper_R_bounded_classicism_models signature stock U"
begin

abbreviation full_objects where "full_objects \<equiv> paper_R_bounded_classicism_models signature stock U"
abbreviation full_arrows where "full_arrows \<equiv> paper_R_bounded_classicism_arrows signature stock U"

lemma paper_R_classicism_hull_rich:
  "paper_R_rich stock"
  by (rule paper_R_bbk_data_stock_rich[OF paper_R_bounded_theory_models_valid[OF root_member]])

sublocale Hull: paper_R_separating_hull signature stock full_objects full_arrows Root
proof (rule paper_R_separating_hull.intro)
  show "paper_R_bbk_subcategory signature stock full_objects full_arrows" by (rule paper_R_bounded_classicism_subcategory)
next
  show "Root \<in> full_objects" by (rule root_member)
next
  fix M p q
  assume object: "M \<in> full_objects" and pm: "p \<in> paper_bbk_domain M Prop"
    and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q"
  obtain r where arrow: "r \<in> full_arrows" and src: "paper_arrow_source r = M"
    and separated: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
    by (rule paper_R_bounded_theory_separating_arrow[OF infinite_bound signature_bound
      paper_R_classicism_is_H_theory paper_R_classicism_is_PE_closed[OF paper_R_classicism_hull_rich]
      object pm qm different])
  show "\<exists>r\<in>full_arrows. paper_arrow_source r = M \<and>
      paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
    by (rule bexI[where x=r], rule conjI[OF src separated], rule arrow)
qed

abbreviation generated_objects where "generated_objects \<equiv> paper_R_separating_hull_objects full_arrows Root"
abbreviation generated_arrows where "generated_arrows \<equiv> paper_R_separating_hull_arrows full_arrows Root"

theorem paper_R_classicism_hull_subcategory:
  "paper_R_bbk_subcategory signature stock generated_objects generated_arrows"
  by (rule Hull.paper_R_hull_subcategory)

lemma paper_R_classicism_hull_root:
  "Root \<in> generated_objects"
  by (rule paper_R_separating_hull_root)

lemma paper_R_classicism_hull_objects_subset:
  "generated_objects \<subseteq> full_objects"
  by (rule Hull.paper_R_hull_objects_original)

lemma paper_R_classicism_hull_arrows_subset:
  "generated_arrows \<subseteq> full_arrows"
  by (rule Hull.paper_R_hull_arrows_original)

lemma paper_R_classicism_hull_domains:
  assumes object: "M \<in> generated_objects"
  shows "(\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
  by (rule paper_R_bounded_theory_models_bound[OF subsetD[OF paper_R_classicism_hull_objects_subset object]])

theorem paper_R_classicism_hull_canonical:
  "paper_R_bbk_canonical_subcategory signature stock generated_objects generated_arrows"
  unfolding paper_R_bbk_canonical_subcategory_def
proof (rule conjI[OF paper_R_classicism_hull_subcategory], intro ballI)
  fix M
  assume object: "M \<in> generated_objects"
  show "paper_R_bbk_data_canonical signature stock M"
    by (rule paper_R_bounded_theory_models_canonical[OF subsetD[OF paper_R_classicism_hull_objects_subset object]])
qed

theorem paper_R_classicism_hull_quasi_fregean:
  "paper_bbk_quasi_fregean_on generated_objects generated_arrows"
  by (rule Hull.paper_R_hull_quasi_fregean)

theorem paper_R_classicism_hull_quasi_functional:
  "paper_R_quasi_functional_on signature stock generated_objects generated_arrows"
proof (rule paper_R_quasi_functional_from_modal_functionality[
    OF paper_R_classicism_hull_subcategory paper_R_classicism_hull_quasi_fregean])
  fix M \<sigma> \<tau> F H z
  assume object: "M \<in> generated_objects"
    and fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)" and hl: "paper_R_in_language signature stock H (Arr \<sigma> \<tau>)"
    and variable: "stock z = \<sigma>" and freshF: "z \<notin> named_fv F" and freshH: "z \<notin> named_fv H"
  have original: "M \<in> full_objects" by (rule subsetD[OF paper_R_classicism_hull_objects_subset object])
  show "paper_R_bbk_model.paper_R_valid signature stock (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (named_paper_imp stock
      (paper_R_named_box stock (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H))"
    by (rule paper_R_bounded_classicism_modal_functionality_valid[
      OF paper_R_classicism_hull_rich original fl hl variable freshF freshH])
qed

theorem paper_R_classicism_hull_intensional:
  "paper_R_intensional_on signature stock generated_objects generated_arrows"
  by (rule paper_R_quasi_conditions_imply_intensional[OF paper_R_classicism_hull_subcategory
    paper_R_classicism_hull_quasi_fregean paper_R_classicism_hull_quasi_functional])

end

text \<open>
  The hull's quasi-Fregeanness follows from its chosen separators.
  Modalized Functionality is valid because its native C theorem belongs
  to every original object's defining theory. These two proved facts
  establish the hull's quasi-functionality and intensionality anew.
  Intensionality is not inherited merely by deleting arrows. Cardinal
  bounds on the generated object and arrow sets are separate results.
\<close>

end
