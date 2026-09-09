theory Bacon_Source_ZF_R_Arrow_Action
  imports Bacon_Source_ZF_R_Arrow_Bound Bacon_Source_ZF_R_Arrow_Naturality
begin

section \<open>The arrow range inherits the canonical exponential action\<close>

text \<open>
  With the child actions established, the translated arrow family is
  an action map into the full exponential. Its own domain remains
  its range, and the canonical exponential transport restricts to
  that range. Source: Definition 3.17 and Proposition 3.22, p.72.
  We construct the new action rather than assuming its action laws.
\<close>

context paper_ZF_R_arrow_step
begin

abbreviation arrow_representation where
  "arrow_representation \<equiv> paper_ZF_R_arrow_representation signature stock Bound encode arrows \<sigma> \<tau> X Y"

lemma paper_ZF_R_arrow_fields:
  "paper_ZF_rep_bound arrow_representation = paper_ZF_R_arrow_bound Bound encode arrows X Y"
  "paper_ZF_rep_domain arrow_representation =
    paper_ZF_range_code (paper_ZF_R_arrow_bound Bound encode arrows X Y)
      (paper_ZF_R_arrow_encode signature stock Bound encode arrows \<sigma> \<tau> X Y)
      (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))"
  "paper_ZF_rep_encode arrow_representation = paper_ZF_R_arrow_encode signature stock Bound encode arrows \<sigma> \<tau> X Y"
  "paper_ZF_rep_transport arrow_representation =
    paper_ZF_exponential_transport_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose (paper_ZF_rep_domain X)"
  by (simp_all only: paper_ZF_R_arrow_representation_def paper_ZF_type_representation.select_convs)

lemma paper_ZF_R_arrow_original_action:
  "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))
    (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)))"
  by (rule paper_ZF_reindex_action[
    OF paper_R_bbk_selected_type_action[where \<sigma>="Arr \<sigma> \<tau>", OF R_category]
      encode_injective encode_bounded])

lemma paper_ZF_R_arrow_ambient_action:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and output_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y)"
  shows "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_bound arrow_representation M)) (paper_ZF_rep_transport arrow_representation)"
proof -
  interpret Pair: paper_ZF_action_pair objects "paper_ZF_image_code Bound encode arrows"
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
    "paper_ZF_rep_domain X" "paper_ZF_rep_transport X" "paper_ZF_rep_domain Y" "paper_ZF_rep_transport Y"
    by (unfold_locales; use input_action output_action in
      \<open>auto simp: paper_action_def paper_action_axioms_def paper_category_def\<close>)
  show ?thesis by (simp only: paper_ZF_R_arrow_fields paper_ZF_R_arrow_bound_def;
    rule Pair.paper_ZF_exponential_action)
qed

lemma paper_ZF_R_arrow_ambient_map:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and output_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y)"
  shows "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))
    (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)))
    (\<lambda>M. explode (paper_ZF_rep_bound arrow_representation M))
    (paper_ZF_rep_transport arrow_representation) (paper_ZF_rep_encode arrow_representation)"
proof (rule paper_action_mapI)
  fix M d
  assume "M \<in> objects" and head: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
  show "paper_ZF_rep_encode arrow_representation M d \<in> explode (paper_ZF_rep_bound arrow_representation M)"
    by (simp only: paper_ZF_R_arrow_fields;
      rule paper_ZF_R_arrow_code_type[OF input_action output_action head])
next
  fix f d
  assume arrow: "f \<in> Encoding.coded_arrows"
    and head: "d \<in> paper_bbk_domain (Encoding.coded_source f) (Arr \<sigma> \<tau>)"
  have encoding: "paper_ZF_R_profile_encoding signature stock objects arrows encode Bound"
    by unfold_locales
  show "paper_ZF_rep_encode arrow_representation (Encoding.coded_target f)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)) f d) =
      paper_ZF_rep_transport arrow_representation f
        (paper_ZF_rep_encode arrow_representation (Encoding.coded_source f) d)"
    by (simp only: paper_ZF_R_arrow_fields;
      rule paper_ZF_R_arrow_encode_naturality[OF encoding arrow head])
qed

theorem paper_ZF_R_arrow_range_action:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and output_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y)"
  shows "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain arrow_representation M)) (paper_ZF_rep_transport arrow_representation)"
proof -
  have ambient: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_bound arrow_representation M)) (paper_ZF_rep_transport arrow_representation)"
    by (rule paper_ZF_R_arrow_ambient_action[OF input_action output_action])
  have family: "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)))
      (\<lambda>M. explode (paper_ZF_rep_bound arrow_representation M))
      (paper_ZF_rep_transport arrow_representation) (paper_ZF_rep_encode arrow_representation)"
    by (rule paper_ZF_R_arrow_ambient_map[OF input_action output_action])
  have action: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_range_code (paper_ZF_rep_bound arrow_representation)
        (paper_ZF_rep_encode arrow_representation) (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)) M))
      (paper_ZF_rep_transport arrow_representation)"
    by (rule paper_ZF_range_action[OF paper_ZF_R_arrow_original_action ambient family])
  show ?thesis using action by (simp only: paper_ZF_R_arrow_fields)
qed

theorem paper_ZF_R_arrow_range_forward_map:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and output_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y)"
  shows "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))
    (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)))
    (\<lambda>M. explode (paper_ZF_rep_domain arrow_representation M))
    (paper_ZF_rep_transport arrow_representation) (paper_ZF_rep_encode arrow_representation)"
proof -
  have family: "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)))
      (\<lambda>M. explode (paper_ZF_rep_bound arrow_representation M))
      (paper_ZF_rep_transport arrow_representation) (paper_ZF_rep_encode arrow_representation)"
    by (rule paper_ZF_R_arrow_ambient_map[OF input_action output_action])
  have ranged: "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>))
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)))
      (\<lambda>M. explode (paper_ZF_range_code (paper_ZF_rep_bound arrow_representation)
        (paper_ZF_rep_encode arrow_representation) (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)) M))
      (paper_ZF_rep_transport arrow_representation) (paper_ZF_rep_encode arrow_representation)"
    by (rule paper_ZF_range_forward_action_map[OF family])
  show ?thesis using ranged by (simp only: paper_ZF_R_arrow_fields)
qed

end

end
