theory Bacon_Source_ZF_R_Proposition_Range
  imports Bacon_Source_ZF_R_Truth_Profile_Action Bacon_Source_ZF_Range_Action
begin

section \<open>The proposition stock is the actual truth-profile range\<close>

text \<open>
  Replace Mₜ by the encoded profiles of its OWN proposition values:
  Cₜ(M)={codeM(p) | p∈Mₜ}. Source: Definition 3.10, p.50,
  Definition 3.17, p.55, and Proposition 3.22 (statement p.57).
  This range is separated inside the ambient outgoing-arrow powerset.
  It is not enlarged to that full powerset.

  The supplied locale validates an independent R category and a bounded,
  injective encoding of its selected arrows. The inherited powerset
  transport preserves the range because the actual profile family is
  equivariant. Quasi-Fregeanness is used only for injectivity and the
  resulting bijection/inverse laws. No all-type recursion, source-model
  representability without bounds, or action-model interpretation is
  assumed. This coded layer is relative to standard HOL-ZF.
\<close>

definition paper_ZF_R_proposition_range_code ::
  "ZF \<Rightarrow> (('c,'v) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,'v) paper_R_bbk_arrow set \<Rightarrow>
    ('c,'v) paper_bbk_model_data \<Rightarrow> ZF" where
  "paper_ZF_R_proposition_range_code Bound e Arrows =
    paper_ZF_range_code
      (paper_ZF_powerset_code (paper_ZF_image_code Bound e Arrows)
        (paper_ZF_recode_source Arrows e paper_arrow_source))
      (paper_ZF_R_truth_profile_code Bound e Arrows) (\<lambda>M. paper_bbk_domain M Prop)"

definition paper_ZF_R_proposition_range_decode ::
  "ZF \<Rightarrow> (('c,'v) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,'v) paper_R_bbk_arrow set \<Rightarrow>
    ('c,'v) paper_bbk_model_data \<Rightarrow> ZF \<Rightarrow> 'v" where
  "paper_ZF_R_proposition_range_decode Bound e Arrows =
    paper_ZF_range_decode (paper_ZF_R_truth_profile_code Bound e Arrows) (\<lambda>M. paper_bbk_domain M Prop)"

context paper_ZF_R_profile_encoding
begin

abbreviation proposition_range_code where
  "proposition_range_code \<equiv> paper_ZF_R_proposition_range_code Bound encode arrows"

abbreviation proposition_range_decode where
  "proposition_range_decode \<equiv> paper_ZF_R_proposition_range_decode Bound encode arrows"

theorem paper_ZF_R_proposition_range_elements:
  "explode (proposition_range_code M) = image (proposition_code M) (paper_bbk_domain M Prop)"
  unfolding paper_ZF_R_proposition_range_code_def
  by (rule paper_ZF_range_code_explode, rule paper_ZF_R_truth_profile_code_type)

lemma paper_ZF_R_proposition_range_subset:
  "explode (proposition_range_code M) \<subseteq>
    explode (paper_ZF_powerset_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)"
  unfolding paper_ZF_R_proposition_range_code_def by (rule paper_ZF_range_code_subset)

lemma paper_ZF_R_proposition_range_encode_type:
  assumes member: "p \<in> paper_bbk_domain M Prop"
  shows "proposition_code M p \<in> explode (proposition_range_code M)"
  by (simp only: paper_ZF_R_proposition_range_elements; rule imageI[OF member])

theorem paper_ZF_R_proposition_range_action:
  "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity (\<lambda>M. explode (proposition_range_code M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)"
  unfolding paper_ZF_R_proposition_range_code_def
  by (rule paper_ZF_range_action[OF paper_ZF_R_reindexed_proposition_action
    paper_ZF_R_ambient_powerset_action paper_ZF_R_truth_profile_action_map])

theorem paper_ZF_R_proposition_range_subaction:
  "paper_subaction objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (proposition_range_code M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)
    (\<lambda>M. explode (paper_ZF_powerset_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)"
  unfolding paper_ZF_R_proposition_range_code_def
  by (rule paper_ZF_range_subaction[OF paper_ZF_R_reindexed_proposition_action
    paper_ZF_R_ambient_powerset_action paper_ZF_R_truth_profile_action_map])

theorem paper_ZF_R_proposition_range_forward_map:
  "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. paper_bbk_domain M Prop) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop))
    (\<lambda>M. explode (proposition_range_code M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose) proposition_code"
  unfolding paper_ZF_R_proposition_range_code_def
  by (rule paper_ZF_range_forward_action_map[OF paper_ZF_R_truth_profile_action_map])

section \<open>Quasi-Fregeanness identifies each original fiber with its range\<close>

theorem paper_ZF_R_proposition_range_bijection:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows" and object: "M \<in> objects"
  shows "bij_betw (proposition_code M) (paper_bbk_domain M Prop) (explode (proposition_range_code M))"
  unfolding bij_betw_def
  by (rule conjI[OF paper_ZF_R_truth_profile_code_injective[OF quasi object]];
    simp only: paper_ZF_R_proposition_range_elements)

lemma paper_ZF_R_proposition_range_decode_type:
  assumes member: "z \<in> explode (proposition_range_code M)"
  shows "proposition_range_decode M z \<in> paper_bbk_domain M Prop"
proof -
  have image_member: "z \<in> paper_action_image proposition_code (\<lambda>M. paper_bbk_domain M Prop) M"
    using member by (simp only: paper_ZF_R_proposition_range_elements paper_action_image_def)
  show ?thesis unfolding paper_ZF_R_proposition_range_decode_def paper_ZF_range_decode_def
    by (rule paper_action_image_inverse_type[OF image_member])
qed

lemma paper_ZF_R_proposition_range_encode_decode:
  assumes member: "z \<in> explode (proposition_range_code M)"
  shows "proposition_code M (proposition_range_decode M z) = z"
proof -
  have image_member: "z \<in> paper_action_image proposition_code (\<lambda>M. paper_bbk_domain M Prop) M"
    using member by (simp only: paper_ZF_R_proposition_range_elements paper_action_image_def)
  show ?thesis unfolding paper_ZF_R_proposition_range_decode_def paper_ZF_range_decode_def
    by (rule paper_action_image_inverse_right[OF image_member])
qed

lemma paper_ZF_R_proposition_range_decode_encode:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows" and object: "M \<in> objects"
    and member: "p \<in> paper_bbk_domain M Prop"
  shows "proposition_range_decode M (proposition_code M p) = p"
  unfolding paper_ZF_R_proposition_range_decode_def paper_ZF_range_decode_def
  by (rule paper_action_image_inverse_left[
    where e=proposition_code and X="\<lambda>M. paper_bbk_domain M Prop" and A=M,
    OF paper_ZF_R_truth_profile_code_injective[OF quasi object] member])

theorem paper_ZF_R_proposition_range_inverse_map:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows"
  shows "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. explode (proposition_range_code M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)
    (\<lambda>M. paper_bbk_domain M Prop) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop))
    proposition_range_decode"
  unfolding paper_ZF_R_proposition_range_code_def paper_ZF_R_proposition_range_decode_def
  by (rule paper_ZF_range_inverse_action_map[OF paper_ZF_R_reindexed_proposition_action
      paper_ZF_R_ambient_powerset_action paper_ZF_R_truth_profile_action_map],
    rule paper_ZF_R_truth_profile_code_injective[OF quasi], assumption)

end

end
