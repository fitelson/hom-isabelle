theory Bacon_Source_ZF_R_Arrow_Coherence
  imports Bacon_Source_ZF_R_Type_Recursion
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Application_Profile
begin

section \<open>Typing and coherence of the translated arrow clause\<close>

text \<open>
  The function-type clause of Proposition 3.22 (p.72) uses the
  inverse at σ and the forward map at τ. Here those two CHILD
  maps are supplied with their action-map properties. We derive
  typing and coherence of the displayed function at σ→τ.
  No action-map or inverse law at σ→τ is assumed.

  Coherence moves the argument along the second arrow. This differs
  from precomposition, which leaves the target argument unchanged.
  All equations below retain membership in the actual child domain.
\<close>

locale paper_ZF_R_arrow_step =
  paper_ZF_R_profile_encoding signature stock objects arrows encode Bound
  for signature :: "'c ssignature" and stock :: sgcontext
    and objects :: "('c,ZF) paper_bbk_model_data set"
    and arrows :: "('c,ZF) paper_R_bbk_arrow set"
    and encode :: "('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF" and Bound :: ZF +
  fixes \<sigma> \<tau> :: otype and X Y :: "'c paper_ZF_R_representation"
  assumes arrow_type: "paper_R_type (Arr \<sigma> \<tau>)"
    and input_inverse: "paper_action_map objects
      (explode (paper_ZF_image_code Bound encode arrows))
      (paper_ZF_recode_source arrows encode paper_arrow_source)
      (paper_ZF_recode_target arrows encode paper_arrow_target)
      (\<lambda>M. explode (paper_ZF_rep_domain X M)) (paper_ZF_rep_transport X)
      (\<lambda>M. paper_bbk_domain M \<sigma>)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>))
      (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M \<sigma>) X)"
    and output_forward: "paper_action_map objects
      (explode (paper_ZF_image_code Bound encode arrows))
      (paper_ZF_recode_source arrows encode paper_arrow_source)
      (paper_ZF_recode_target arrows encode paper_arrow_target)
      (\<lambda>M. paper_bbk_domain M \<tau>)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<tau>))
      (\<lambda>M. explode (paper_ZF_rep_domain Y M)) (paper_ZF_rep_transport Y)
      (paper_ZF_rep_encode Y)"
begin

abbreviation body where
  "body \<equiv> paper_ZF_R_arrow_body signature stock Bound encode arrows \<sigma> \<tau> X Y"

abbreviation inverse_input where
  "inverse_input \<equiv> paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M \<sigma>) X"

lemma paper_ZF_R_arrow_input_type:
  assumes arrow: "h \<in> Encoding.coded_arrows"
    and member: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target h))"
  shows "inverse_input (Encoding.coded_target h) z \<in>
    paper_bbk_domain (Encoding.coded_target h) \<sigma>"
proof -
  have object: "Encoding.coded_target h \<in> objects"
    unfolding paper_ZF_recode_target_def
    by (rule Encoding.target_object[OF Encoding.paper_ZF_decode_arrow_type[OF arrow]])
  show ?thesis by (rule paper_action_map_type[OF input_inverse object member])
qed

lemma paper_ZF_R_arrow_body_profile:
  assumes arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = M"
    and member: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target h))"
  shows "body M d (h,z) = paper_ZF_rep_encode Y (Encoding.coded_target h)
    (paper_R_app_profile_on signature stock arrows M \<sigma> \<tau> d
      (Encoding.decode_arrow h, inverse_input (Encoding.coded_target h) z))"
proof -
  have pair: "Elem (Opair h z) (paper_ZF_pair_code (paper_ZF_image_code Bound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain X) M)"
    using arrow source member by (simp only: paper_ZF_pair_code_member; blast)
  have original: "Encoding.decode_arrow h \<in> arrows"
    by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have origin: "paper_arrow_source (Encoding.decode_arrow h) = M"
    using source by (simp only: paper_ZF_recode_source_def)
  have argument: "inverse_input (Encoding.coded_target h) z \<in>
      paper_bbk_domain (paper_arrow_target (Encoding.decode_arrow h)) \<sigma>"
    using paper_ZF_R_arrow_input_type[OF arrow member]
    by (simp only: paper_ZF_recode_target_def)
  have profile_value: "paper_R_app_profile_on signature stock arrows M \<sigma> \<tau> d
      (Encoding.decode_arrow h, inverse_input (paper_arrow_target (Encoding.decode_arrow h)) z) =
      paper_R_application signature stock
        (paper_bbk_domain (paper_arrow_target (Encoding.decode_arrow h)))
        (paper_bbk_denote (paper_arrow_target (Encoding.decode_arrow h))) \<sigma> \<tau>
        (paper_arrow_map (Encoding.decode_arrow h) (Arr \<sigma> \<tau>) d)
        (inverse_input (paper_arrow_target (Encoding.decode_arrow h)) z)"
    using paper_R_app_profile_on_value[OF original origin argument]
    by (simp only: paper_ZF_recode_target_def)
  show ?thesis
    by (simp only: paper_ZF_R_arrow_body_on[OF pair]
      paper_ZF_recode_target_def paper_ZF_recode_transport_def profile_value)
qed

lemma paper_ZF_R_arrow_body_type:
  assumes head: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = M"
    and member: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target h))"
  shows "body M d (h,z) \<in> explode (paper_ZF_rep_domain Y (Encoding.coded_target h))"
proof -
  have original: "Encoding.decode_arrow h \<in> arrows"
    by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have origin: "paper_arrow_source (Encoding.decode_arrow h) = M"
    using source by (simp only: paper_ZF_recode_source_def)
  have object: "Encoding.coded_target h \<in> objects"
    unfolding paper_ZF_recode_target_def by (rule Encoding.target_object[OF original])
  have argument: "inverse_input (Encoding.coded_target h) z \<in>
      paper_bbk_domain (paper_arrow_target (Encoding.decode_arrow h)) \<sigma>"
    using paper_ZF_R_arrow_input_type[OF arrow member]
    by (simp only: paper_ZF_recode_target_def)
  have result: "paper_R_app_profile_on signature stock arrows M \<sigma> \<tau> d
      (Encoding.decode_arrow h, inverse_input (Encoding.coded_target h) z)
      \<in> paper_bbk_domain (Encoding.coded_target h) \<tau>"
    using paper_R_app_profile_on_type[OF R_category arrow_type head original origin argument]
    by (simp only: paper_ZF_recode_target_def)
  show ?thesis
    by (simp only: paper_ZF_R_arrow_body_profile[OF arrow source member];
      rule paper_action_map_type[OF output_forward object result])
qed

lemma paper_ZF_R_arrow_body_coherent:
  assumes head: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and first: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = M"
    and second: "i \<in> Encoding.coded_arrows"
    and meeting: "Encoding.coded_target h = Encoding.coded_source i"
    and member: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target h))"
    and moved: "paper_ZF_rep_transport X i z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target i))"
  shows "paper_ZF_rep_transport Y i (body M d (h,z)) =
    body M d (Encoding.coded_compose i h, paper_ZF_rep_transport X i z)"
proof -
  interpret Coded: paper_category objects Encoding.coded_arrows Encoding.coded_source
    Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
    by (rule Encoding.paper_ZF_encoded_category)
  have ha: "Encoding.decode_arrow h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF first])
  have ia: "Encoding.decode_arrow i \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF second])
  have origin: "paper_arrow_source (Encoding.decode_arrow h) = M"
    using source by (simp only: paper_ZF_recode_source_def)
  have meets: "paper_arrow_target (Encoding.decode_arrow h) = paper_arrow_source (Encoding.decode_arrow i)"
    by (rule Encoding.paper_ZF_decoded_meeting[OF meeting])
  let ?a = "inverse_input (Encoding.coded_target h) z"
  let ?b = "paper_R_app_profile_on signature stock arrows M \<sigma> \<tau> d (Encoding.decode_arrow h,?a)"
  have argument: "?a \<in> paper_bbk_domain (paper_arrow_target (Encoding.decode_arrow h)) \<sigma>"
    using paper_ZF_R_arrow_input_type[OF first member]
    by (simp only: paper_ZF_recode_target_def)
  have result: "?b \<in> paper_bbk_domain (Encoding.coded_source i) \<tau>"
    using paper_R_app_profile_on_type[OF R_category arrow_type head ha origin argument]
    by (simp only: paper_ZF_recode_target_def[symmetric] meeting)
  have at_source: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_source i))"
    using member by (simp only: meeting)
  have inverse_natural: "inverse_input (Encoding.coded_target i) (paper_ZF_rep_transport X i z) =
      paper_arrow_map (Encoding.decode_arrow i) \<sigma> ?a"
    using paper_action_map_equivariant[OF input_inverse second at_source]
    by (simp only: paper_ZF_recode_transport_def meeting)
  have output_natural: "paper_ZF_rep_transport Y i
      (paper_ZF_rep_encode Y (Encoding.coded_target h) ?b) =
      paper_ZF_rep_encode Y (Encoding.coded_target i) (paper_arrow_map (Encoding.decode_arrow i) \<tau> ?b)"
    using paper_action_map_equivariant[OF output_forward second result]
    by (simp only: paper_ZF_recode_transport_def meeting)
  have coherent: "paper_arrow_map (Encoding.decode_arrow i) \<tau> ?b =
      paper_R_app_profile_on signature stock arrows M \<sigma> \<tau> d
        (paper_typed_compose paper_bbk_domain (Encoding.decode_arrow i) (Encoding.decode_arrow h),
         paper_arrow_map (Encoding.decode_arrow i) \<sigma> ?a)"
    by (rule paper_R_app_profile_on_coherent[OF R_category arrow_type head ha origin argument ia meets])
  have composite: "Encoding.coded_compose i h \<in> Encoding.coded_arrows"
    by (rule Coded.compose_arrow[OF first second meeting])
  have cs: "Encoding.coded_source (Encoding.coded_compose i h) = M"
    by (simp only: Coded.compose_source[OF first second meeting] source)
  have ct: "Encoding.coded_target (Encoding.coded_compose i h) = Encoding.coded_target i"
    by (rule Coded.compose_target[OF first second meeting])
  have composite_argument: "paper_ZF_rep_transport X i z \<in>
      explode (paper_ZF_rep_domain X (Encoding.coded_target (Encoding.coded_compose i h)))"
    by (simp only: ct; rule moved)
  show ?thesis
    by (simp only: paper_ZF_R_arrow_body_profile[OF first source member]
      paper_ZF_R_arrow_body_profile[OF composite cs composite_argument]
      ct Encoding.paper_ZF_decode_coded_compose[OF first second meeting]
      inverse_natural output_natural coherent)
qed

end

end
