theory Bacon_Source_ZF_R_Proposition_Base
  imports Bacon_Source_ZF_R_Individual_Base
begin

section \<open>The proposition base is exactly the range of coded truth profiles\<close>

text \<open>
  Proposition 3.22 uses fᵗM(p)=val𝒞M(p) and the range of this
  map as the new proposition domain (p.72). The recursion selectors
  below are connected to the actual range/action construction.
  Quasi-Fregeanness is needed for injectivity and reverse equivariance,
  not for range exactness, typing, the action, or the forward map.

  These are base cases only. The individual bound is a fixed parameter
  but no individual-bound assumption is needed here. No all-type
  representation or action-model condition is assumed.
\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_Prop_fields:
  "paper_ZF_rep_bound (type_representation Prop) =
    paper_ZF_powerset_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source"
  "paper_ZF_rep_domain (type_representation Prop) = proposition_range_code"
  "paper_ZF_rep_encode (type_representation Prop) = proposition_code"
  "paper_ZF_rep_transport (type_representation Prop) =
    paper_ZF_powerset_transport_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose"
  by (simp_all only: paper_ZF_R_type_representation.simps paper_ZF_R_proposition_representation_def
    paper_ZF_type_representation.select_convs)

lemma paper_ZF_R_Prop_inverse_eq:
  "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Prop) (type_representation Prop) = proposition_range_decode"
  by (rule ext, rule ext; simp only: paper_ZF_rep_inverse_def paper_ZF_R_Prop_fields(3)
    paper_ZF_R_proposition_range_decode_def paper_ZF_range_decode_def paper_action_image_inverse_def)

theorem paper_ZF_R_Prop_range:
  "explode (paper_ZF_rep_domain (type_representation Prop) M) =
    image (paper_ZF_rep_encode (type_representation Prop) M) (paper_bbk_domain M Prop)"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_proposition_range_elements)

lemma paper_ZF_R_Prop_bound:
  "paper_ZF_rep_encode (type_representation Prop) M p \<in> explode (paper_ZF_rep_bound (type_representation Prop) M)"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_truth_profile_code_type)

lemma paper_ZF_R_Prop_domain_subset_bound:
  "explode (paper_ZF_rep_domain (type_representation Prop) M) \<subseteq>
    explode (paper_ZF_rep_bound (type_representation Prop) M)"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_proposition_range_subset)

theorem paper_ZF_R_Prop_bijection:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows" and object: "M \<in> objects"
  shows "bij_betw (paper_ZF_rep_encode (type_representation Prop) M) (paper_bbk_domain M Prop)
    (explode (paper_ZF_rep_domain (type_representation Prop) M))"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_proposition_range_bijection[OF quasi object])

lemma paper_ZF_R_Prop_inverse_type:
  assumes member: "z \<in> explode (paper_ZF_rep_domain (type_representation Prop) M)"
  shows "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Prop) (type_representation Prop) M z \<in> paper_bbk_domain M Prop"
proof -
  have coded: "z \<in> explode (proposition_range_code M)" using member by (simp only: paper_ZF_R_Prop_fields(2))
  show ?thesis by (simp only: paper_ZF_R_Prop_inverse_eq;
    rule paper_ZF_R_proposition_range_decode_type[OF coded])
qed

lemma paper_ZF_R_Prop_encode_decode:
  assumes member: "z \<in> explode (paper_ZF_rep_domain (type_representation Prop) M)"
  shows "paper_ZF_rep_encode (type_representation Prop) M
    (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Prop) (type_representation Prop) M z) = z"
proof -
  have coded: "z \<in> explode (proposition_range_code M)" using member by (simp only: paper_ZF_R_Prop_fields(2))
  show ?thesis by (simp only: paper_ZF_R_Prop_fields paper_ZF_R_Prop_inverse_eq;
    rule paper_ZF_R_proposition_range_encode_decode[OF coded])
qed

lemma paper_ZF_R_Prop_decode_encode:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows" and object: "M \<in> objects"
    and member: "p \<in> paper_bbk_domain M Prop"
  shows "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Prop) (type_representation Prop) M
    (paper_ZF_rep_encode (type_representation Prop) M p) = p"
  by (simp only: paper_ZF_R_Prop_fields paper_ZF_R_Prop_inverse_eq;
    rule paper_ZF_R_proposition_range_decode_encode[OF quasi object member])

theorem paper_ZF_R_Prop_action:
  "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Prop) M)) (paper_ZF_rep_transport (type_representation Prop))"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_proposition_range_action)

theorem paper_ZF_R_Prop_subaction:
  "paper_subaction objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Prop) M)) (paper_ZF_rep_transport (type_representation Prop))
    (\<lambda>M. explode (paper_ZF_rep_bound (type_representation Prop) M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_proposition_range_subaction)

theorem paper_ZF_R_Prop_forward_map:
  "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. paper_bbk_domain M Prop) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop))
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Prop) M)) (paper_ZF_rep_transport (type_representation Prop))
    (paper_ZF_rep_encode (type_representation Prop))"
  by (simp only: paper_ZF_R_Prop_fields; rule paper_ZF_R_proposition_range_forward_map)

theorem paper_ZF_R_Prop_inverse_map:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows"
  shows "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Prop) M)) (paper_ZF_rep_transport (type_representation Prop))
    (\<lambda>M. paper_bbk_domain M Prop) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop))
    (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Prop) (type_representation Prop))"
  by (simp only: paper_ZF_R_Prop_fields paper_ZF_R_Prop_inverse_eq;
    rule paper_ZF_R_proposition_range_inverse_map[OF quasi])

end

end
