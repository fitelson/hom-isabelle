theory Bacon_Source_ZF_R_Truth_Profile_Action
  imports Bacon_Source_ZF_R_Truth_Profile_Coding Bacon_Source_ZF_Reindexed_Action
    Bacon_Classicism_Action_Development.Bacon_Source_Image_Action
begin

section \<open>Coded proposition profiles commute with actual powerset transport\<close>

text \<open>
  fₜᴺ(hₜ(p))=e(h)ᴾ(fₜᴹ(p)), where the proposition code fₜᴹ(p)
  contains exactly the coded arrows in p's truth profile.
  Source: Example 3.15, p.54, and Proposition 3.22, p.72.

  The old proposition action is only reindexed along the arrow encoding.
  The target is the ambient coded powerset action. Neither naturality nor
  typing declares that entire ambient fiber to be the proposition stock;
  the intended stock is the range of the displayed proposition map.
\<close>

context paper_ZF_R_profile_encoding
begin

theorem paper_ZF_R_truth_profile_code_naturality:
  assumes arrow: "f \<in> arrows" and member: "p \<in> paper_bbk_domain (paper_arrow_source f) Prop"
  shows "proposition_code (paper_arrow_target f) (paper_arrow_map f Prop p) =
    paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose (encode f)
      (proposition_code (paper_arrow_source f) p)"
proof -
  have category: "paper_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
    by (rule paper_R_bbk_subcategory_category[OF R_category])
  have subset: "paper_bbk_truth_profile_on arrows (paper_arrow_source f) p \<subseteq> arrows"
    by (auto simp only: paper_bbk_truth_profile_on_member)
  have raw_naturality: "paper_bbk_truth_profile_on arrows (paper_arrow_target f) (paper_arrow_map f Prop p) =
      paper_powerset_transport arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain) f
        (paper_bbk_truth_profile_on arrows (paper_arrow_source f) p)"
    by (rule paper_bbk_truth_profile_on_naturality[OF category arrow member])
  have decoded: "explode (proposition_code (paper_arrow_target f) (paper_arrow_map f Prop p)) =
      explode (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
        Encoding.coded_source Encoding.coded_target Encoding.coded_compose (encode f)
        (proposition_code (paper_arrow_source f) p))"
    by (simp only: paper_ZF_R_truth_profile_code_elements paper_ZF_decode_powerset_transport
      raw_naturality Encoding.paper_ZF_powerset_reindex[OF arrow subset])
  show ?thesis by (rule injD[OF inj_explode decoded])
qed

lemma paper_ZF_R_truth_profile_coded_naturality:
  assumes arrow: "z \<in> Encoding.coded_arrows"
    and member: "p \<in> paper_bbk_domain (Encoding.coded_source z) Prop"
  shows "proposition_code (Encoding.coded_target z)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop) z p) =
    paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose z
      (proposition_code (Encoding.coded_source z) p)"
proof -
  have original: "Encoding.decode_arrow z \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have typed: "p \<in> paper_bbk_domain (paper_arrow_source (Encoding.decode_arrow z)) Prop"
    using member by (simp only: paper_ZF_recode_source_def)
  have natural: "proposition_code (paper_arrow_target (Encoding.decode_arrow z))
      (paper_arrow_map (Encoding.decode_arrow z) Prop p) =
    paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose (encode (Encoding.decode_arrow z))
      (proposition_code (paper_arrow_source (Encoding.decode_arrow z)) p)"
    by (rule paper_ZF_R_truth_profile_code_naturality[OF original typed])
  show ?thesis using natural
    by (simp only: paper_ZF_recode_transport_def paper_ZF_recode_source_def paper_ZF_recode_target_def
      Encoding.paper_ZF_encode_decode_arrow[OF arrow])
qed

theorem paper_ZF_R_truth_profile_action_map:
  "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. paper_bbk_domain M Prop) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop))
    (\<lambda>M. explode (paper_ZF_powerset_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose) proposition_code"
proof (rule paper_action_mapI)
  fix M p
  assume "M \<in> objects" and "p \<in> paper_bbk_domain M Prop"
  show "proposition_code M p \<in>
      explode (paper_ZF_powerset_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)"
    by (rule paper_ZF_R_truth_profile_code_type)
next
  fix z p
  assume arrow: "z \<in> Encoding.coded_arrows" and member: "p \<in> paper_bbk_domain (Encoding.coded_source z) Prop"
  show "proposition_code (Encoding.coded_target z)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop) z p) =
      paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
        Encoding.coded_source Encoding.coded_target Encoding.coded_compose z
        (proposition_code (Encoding.coded_source z) p)"
    by (rule paper_ZF_R_truth_profile_coded_naturality[OF arrow member])
qed

theorem paper_ZF_R_reindexed_proposition_action:
  "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity (\<lambda>M. paper_bbk_domain M Prop)
    (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Prop))"
  by (rule paper_ZF_reindex_action[
    OF paper_R_bbk_selected_type_action[where \<sigma>=Prop, OF R_category] encode_injective encode_bounded])

theorem paper_ZF_R_ambient_powerset_action:
  "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_powerset_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)"
  by (rule paper_ZF_powerset_action[OF Encoding.paper_ZF_encoded_category])

end

end
