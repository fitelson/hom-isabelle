theory Bacon_Source_ZF_R_Constructed_Premodel
  imports Bacon_Source_ZF_Action_Premodel Bacon_Source_ZF_R_Family_Actions
    Bacon_Source_ZF_R_Premodel_Domains Bacon_Source_ZF_R_Root_Constants
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Intensional_Forward
begin

section \<open>The recursive representation constructs an action premodel\<close>

text \<open>
  Every clause of the independent Definition 3.18 predicate is
  supplied by an earlier construction: the coded weak root,
  the all-type actions, inherited nonempty individual fibers,
  the specified subactions, and the encoded root constants.
  This is the premodel stage of Proposition 3.22 (p.72).

  Source values are ZF values; arrow representability and the
  individual bound remain explicit. Quasi-Fregeanness and
  quasi-functionality are source-category conditions. No premodel
  or model predicate, interpretation clause, or totality premise
  is assumed in order to prove this conclusion.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_constructed_premodel:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
  shows "paper_ZF_action_premodel signature objects (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity Root
    (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
    (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root)"
proof (rule paper_ZF_action_premodelI[OF paper_ZF_R_encoded_rooted_category[OF rooted]])
  fix \<rho>
  assume rt: "paper_R_type \<rho>"
  show "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain (type_representation \<rho>) M))
      (paper_ZF_rep_transport (type_representation \<rho>))"
    by (rule paper_ZF_R_all_type_action[OF bounded fregean functional rt])
next
  fix M
  assume object: "M \<in> objects"
  show "explode (paper_ZF_rep_domain (type_representation Ind) M) \<noteq> {}"
    by (rule paper_ZF_R_Ind_nonempty[OF object bounded[OF object]])
next
  show "paper_subaction objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Prop) M))
      (paper_ZF_rep_transport (type_representation Prop))
      (\<lambda>M. explode (paper_ZF_powerset_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M))
      (paper_ZF_powerset_transport_code (paper_ZF_image_code ArrowBound encode arrows)
        Encoding.coded_source Encoding.coded_target Encoding.coded_compose)"
    by (rule paper_ZF_R_premodel_Prop_subaction)
next
  fix \<sigma> \<tau>
  assume rt: "paper_R_type (Arr \<sigma> \<tau>)"
  show "paper_subaction objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) M))
      (paper_ZF_rep_transport (type_representation (Arr \<sigma> \<tau>)))
      (\<lambda>M. explode (paper_ZF_exponential_code (paper_ZF_image_code ArrowBound encode arrows)
        Encoding.coded_source Encoding.coded_target Encoding.coded_compose
        (paper_ZF_rep_domain (type_representation \<sigma>)) (paper_ZF_rep_transport (type_representation \<sigma>))
        (paper_ZF_rep_domain (type_representation \<tau>)) (paper_ZF_rep_transport (type_representation \<tau>)) M))
      (paper_ZF_exponential_transport_code (paper_ZF_image_code ArrowBound encode arrows)
        Encoding.coded_source Encoding.coded_target Encoding.coded_compose (paper_ZF_rep_domain (type_representation \<sigma>)))"
    by (rule paper_ZF_R_premodel_arrow_subaction[OF bounded fregean functional rt])
next
  fix \<rho> c
  assume rt: "paper_R_type \<rho>" and declared: "c \<in> signature \<rho>"
  have root_object: "Root \<in> objects" by (rule paper_rooted_category.root_object[OF rooted])
  show "paper_ZF_R_root_constant Root \<rho> c \<in> explode (paper_ZF_rep_domain (type_representation \<rho>) Root)"
    by (rule paper_ZF_R_root_constant_type[OF bounded fregean functional root_object declared rt])
qed

corollary paper_ZF_R_intensional_constructed_premodel:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and intensional: "paper_R_intensional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
  shows "paper_ZF_action_premodel signature objects (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity Root
    (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
    (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root)"
proof -
  have conditions: "paper_bbk_quasi_fregean_on objects arrows \<and>
      paper_R_quasi_functional_on signature stock objects arrows"
    by (rule paper_R_intensional_implies_quasi_conditions[OF intensional])
  show ?thesis by (rule paper_ZF_R_constructed_premodel[
    OF bounded conjunct1[OF conditions] conjunct2[OF conditions] rooted])
qed

end

end
