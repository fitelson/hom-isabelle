theory Bacon_Source_ZF_R_Family_Actions
  imports Bacon_Source_ZF_R_All_Type_Representation Bacon_Source_ZF_Rooted_Category_Encoding
begin

section \<open>Extract the constructed actions, rather than assume them\<close>

text \<open>
  Each R type determines an actual action on its recursively coded
  range. These actions are extracted from the proved all-type invariant
  for Proposition 3.22's construction, p.72.

  The source category is independently R-valid and already ZF-valued.
  The bounded arrow injection is part of the supplied encoding; the
  individual bound and quasi-Fregean/quasi-functional hypotheses remain
  explicit. No new family-action or nonemptiness field is assumed.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_all_type_action:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<rho>"
  shows "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation \<rho>) M))
    (paper_ZF_rep_transport (type_representation \<rho>))"
  by (rule paper_ZF_R_type_invariant_action[OF paper_ZF_R_all_type_invariant[OF bounded fregean functional rt]])

section \<open>The required individual fiber is inhabited by an original individual\<close>

text \<open>
  Definition 3.18, p.55, requires a nonempty individual action.
  At each source object M, choose a∈Mₑ using the R model's
  domain-nonemptiness clause. The literal individual representation
  retains a. This argument needs the individual bound at M but
  does not need either profile-injectivity condition.
\<close>

theorem paper_ZF_R_Ind_nonempty:
  assumes object: "M \<in> objects" and bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "explode (paper_ZF_rep_domain (type_representation Ind) M) \<noteq> {}"
proof -
  have valid: "paper_R_bbk_data_valid signature stock M"
    by (rule paper_R_bbk_subcategory_models[OF R_category object])
  have rt: "paper_R_type Ind" by simp
  have original: "paper_bbk_domain M Ind \<noteq> {}"
    by (rule paper_R_bbk_data_domain_nonempty[OF valid rt])
  obtain a where member: "a \<in> paper_bbk_domain M Ind" using original by blast
  have represented: "a \<in> explode (paper_ZF_rep_domain (type_representation Ind) M)"
    by (simp only: paper_ZF_R_Ind_elements[OF bounded]; rule member)
  show ?thesis using represented by blast
qed

theorem paper_ZF_R_represented_domain_nonempty:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<rho>" and object: "M \<in> objects"
  shows "explode (paper_ZF_rep_domain (type_representation \<rho>) M) \<noteq> {}"
proof -
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<rho> (type_representation \<rho>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have valid: "paper_R_bbk_data_valid signature stock M"
    by (rule paper_R_bbk_subcategory_models[OF R_category object])
  have original: "paper_bbk_domain M \<rho> \<noteq> {}" by (rule paper_R_bbk_data_domain_nonempty[OF valid rt])
  obtain a where member: "a \<in> paper_bbk_domain M \<rho>" using original by blast
  have represented: "paper_ZF_rep_encode (type_representation \<rho>) M a \<in>
    explode (paper_ZF_rep_domain (type_representation \<rho>) M)"
    by (rule paper_ZF_R_type_invariant_encode_type[OF invariant object member])
  show ?thesis using represented by blast
qed

text \<open>
  The stronger all-R conclusion above is derived for this source-model
  construction. It is not added to the general action-premodel definition,
  whose base nonemptiness requirement is at e.
\<close>

section \<open>A supplied weak root survives the selected-arrow encoding\<close>

theorem paper_ZF_R_encoded_rooted_category:
  assumes rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) R"
  shows "paper_rooted_category objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity R"
  by (rule Encoding.paper_ZF_encoded_rooted_category[OF rooted])

end

end
