theory Bacon_Source_ZF_R_Represented_Category_Action_Model
  imports Bacon_Source_ZF_R_Root_Truth_Correspondence
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Reachable_Intensional
begin

section \<open>Root the represented category at any of its objects\<close>

text \<open>
  Retain the objects reachable from M₀ and every original selected arrow
  between them. Composition ensures that every outgoing arrow from a
  retained object is retained. Thus the intension tests are unchanged,
  and the resulting selected R category is intensional and weakly rooted.
  Source: Proposition 3.22, pp.57 and 72. Root arrows need not be unique.

  Arrow injectivity and its ZF bound restrict to the smaller arrow set;
  the individual bound restricts to the smaller object set. The actual
  recursive construction is then rerun on this restricted category.
  Its domains, actions and root constants are explicit witnesses below.
  Neither an action model nor a rooted original category is assumed.

  This is the represented-category form of the construction. Original
  values are ZF sets, with a supplied common individual bound and bounded
  injective coding of the selected arrows. It does not assert that every
  arbitrary HOL carrier or proper class has such a representation. The
  original and restricted common theories are not identified.
\<close>

context paper_ZF_R_type_encoding
begin

abbreviation paper_ZF_R_reachable_objects where
  "paper_ZF_R_reachable_objects Root \<equiv>
    paper_reachable_objects arrows paper_arrow_source paper_arrow_target Root"

abbreviation paper_ZF_R_reachable_arrows where
  "paper_ZF_R_reachable_arrows Root \<equiv>
    paper_reachable_arrows arrows paper_arrow_source paper_arrow_target Root"

abbreviation paper_ZF_R_reachable_arrow_code where
  "paper_ZF_R_reachable_arrow_code Root \<equiv>
    paper_ZF_image_code ArrowBound encode (paper_ZF_R_reachable_arrows Root)"

abbreviation paper_ZF_R_reachable_source where
  "paper_ZF_R_reachable_source Root \<equiv>
    paper_ZF_recode_source (paper_ZF_R_reachable_arrows Root) encode paper_arrow_source"

abbreviation paper_ZF_R_reachable_target where
  "paper_ZF_R_reachable_target Root \<equiv>
    paper_ZF_recode_target (paper_ZF_R_reachable_arrows Root) encode paper_arrow_target"

abbreviation paper_ZF_R_reachable_compose where
  "paper_ZF_R_reachable_compose Root \<equiv>
    paper_ZF_recode_compose (paper_ZF_R_reachable_arrows Root) encode (paper_typed_compose paper_bbk_domain)"

theorem paper_ZF_R_represented_category_action_model:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and intensional: "paper_R_intensional_on signature stock objects arrows"
    and root: "Root \<in> objects"
  shows "\<exists>D T I.
    paper_ZF_action_model signature stock (paper_ZF_R_reachable_objects Root) (paper_ZF_R_reachable_arrow_code Root)
      (paper_ZF_R_reachable_source Root) (paper_ZF_R_reachable_target Root) (paper_ZF_R_reachable_compose Root)
      Encoding.coded_identity Root D T I \<and>
    (\<forall>A. paper_R_in_language signature stock A Prop \<longrightarrow>
      ((\<forall>g. paper_ZF_action_env_typed D stock Root g \<longrightarrow> named_adequate g A \<longrightarrow>
        paper_ZF_action_holds (paper_ZF_R_reachable_arrow_code Root)
          (paper_ZF_R_reachable_source Root) (paper_ZF_R_reachable_target Root) (paper_ZF_R_reachable_compose Root)
          Encoding.coded_identity D T I stock (Encoding.coded_identity Root) g A) =
       (\<forall>g. named_env_typed (paper_bbk_domain Root) stock g \<longrightarrow> named_adequate g A \<longrightarrow>
         paper_bbk_valuation Root (paper_bbk_denote Root g A))))"
proof -
  let ?Obj = "paper_ZF_R_reachable_objects Root"
  let ?Arrows = "paper_ZF_R_reachable_arrows Root"
  have category: "paper_R_bbk_subcategory signature stock ?Obj ?Arrows"
    by (rule paper_R_bbk_reachable_subcategory[OF R_category])
  have restricted_intensional: "paper_R_intensional_on signature stock ?Obj ?Arrows"
    by (rule paper_R_bbk_reachable_intensional[OF R_category intensional])
  have rooted: "paper_rooted_category ?Obj ?Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    by (rule paper_R_bbk_reachable_rooted_category[OF R_category root])
  have object_subset: "?Obj \<subseteq> objects" by (rule paper_R_bbk_reachable_objects_subset[OF R_category])
  have arrow_subset: "?Arrows \<subseteq> arrows"
    by (rule subsetI; rule paper_reachable_arrows_original; assumption)
  have injective: "inj_on encode ?Arrows" by (rule inj_on_subset[OF encode_injective arrow_subset])
  have arrow_bound: "image encode ?Arrows \<subseteq> explode ArrowBound"
    using arrow_subset encode_bounded by blast
  interpret Reach: paper_ZF_R_type_encoding signature stock ?Obj ?Arrows encode ArrowBound IndividualBound
    by unfold_locales (rule category, rule injective, rule arrow_bound)
  have individual_bound: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound" if "M \<in> ?Obj" for M
    by (rule bounded[OF subsetD[OF object_subset that]])
  have conditions: "paper_bbk_quasi_fregean_on ?Obj ?Arrows \<and>
      paper_R_quasi_functional_on signature stock ?Obj ?Arrows"
    by (rule paper_R_intensional_implies_quasi_conditions[OF restricted_intensional])
  have fregean: "paper_bbk_quasi_fregean_on ?Obj ?Arrows" by (rule conjunct1[OF conditions])
  have functional: "paper_R_quasi_functional_on signature stock ?Obj ?Arrows" by (rule conjunct2[OF conditions])
  let ?D = "\<lambda>\<rho>. paper_ZF_rep_domain (Reach.type_representation \<rho>)"
  let ?T = "\<lambda>\<rho>. paper_ZF_rep_transport (Reach.type_representation \<rho>)"
  let ?I = "Reach.paper_ZF_R_root_constant Root"
  have model: "paper_ZF_action_model signature stock ?Obj (paper_ZF_R_reachable_arrow_code Root)
      (paper_ZF_R_reachable_source Root) (paper_ZF_R_reachable_target Root) (paper_ZF_R_reachable_compose Root)
      Encoding.coded_identity Root ?D ?T ?I"
    by (rule Reach.paper_ZF_R_constructed_model[OF individual_bound fregean functional rooted])
  have truth: "\<forall>A. paper_R_in_language signature stock A Prop \<longrightarrow>
      ((\<forall>g. paper_ZF_action_env_typed ?D stock Root g \<longrightarrow> named_adequate g A \<longrightarrow>
        paper_ZF_action_holds (paper_ZF_R_reachable_arrow_code Root)
          (paper_ZF_R_reachable_source Root) (paper_ZF_R_reachable_target Root) (paper_ZF_R_reachable_compose Root)
          Encoding.coded_identity ?D ?T ?I stock (Encoding.coded_identity Root) g A) =
       (\<forall>g. named_env_typed (paper_bbk_domain Root) stock g \<longrightarrow> named_adequate g A \<longrightarrow>
         paper_bbk_valuation Root (paper_bbk_denote Root g A)))"
    by (intro allI impI; rule Reach.paper_ZF_R_root_validity_iff[OF individual_bound fregean functional rooted]; assumption)
  show ?thesis by (rule exI[where x="?D"], rule exI[where x="?T"], rule exI[where x="?I"], rule conjI[OF model truth])
qed

end

end
