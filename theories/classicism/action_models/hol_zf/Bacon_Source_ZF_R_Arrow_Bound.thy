theory Bacon_Source_ZF_R_Arrow_Bound
  imports Bacon_Source_ZF_R_Arrow_Coherence
begin

section \<open>The arrow range is not truncated by its exponential bound\<close>

text \<open>
  The child actions and their forward/inverse maps put the translated
  function in the coherent exponential of Example 3.16. Therefore
  separation inside that exponential contains EVERY encoded original
  operator. This proves exact range equality for the arrow clause of
  Proposition 3.22 (p.72); it does not identify the range with the
  full exponential. Quasi-functionality is not needed for this part.
\<close>

context paper_ZF_R_arrow_step
begin

lemma paper_ZF_R_arrow_body_exponential:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and head: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
  shows "body M d \<in> paper_exponential_fiber Encoding.coded_arrows
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose
    (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)
    (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y) M"
proof -
  interpret Input: paper_action objects Encoding.coded_arrows
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
    "\<lambda>N. explode (paper_ZF_rep_domain X N)" "paper_ZF_rep_transport X" by (rule input_action)
  show ?thesis
  proof (rule paper_exponential_fiberI)
    fix p
    assume outside: "p \<notin> paper_exponential_pairs Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target (\<lambda>N. explode (paper_ZF_rep_domain X N)) M"
    show "body M d p = undefined"
    proof (cases p)
      case (Pair h z)
      have absent: "(h,z) \<notin> paper_exponential_pairs Encoding.coded_arrows
          Encoding.coded_source Encoding.coded_target (\<lambda>N. explode (paper_ZF_rep_domain X N)) M"
        using outside by (simp add: Pair)
      show ?thesis by (simp only: Pair paper_ZF_R_arrow_body_def Let_def prod.case if_not_P[OF absent])
    qed
  next
    fix h z
    assume arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = M"
      and member: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target h))"
    show "body M d (h,z) \<in> explode (paper_ZF_rep_domain Y (Encoding.coded_target h))"
      by (rule paper_ZF_R_arrow_body_type[OF head arrow source member])
  next
    fix h i z
    assume first: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = M"
      and second: "i \<in> Encoding.coded_arrows" and meeting: "Encoding.coded_target h = Encoding.coded_source i"
      and member: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_target h))"
    have at_source: "z \<in> explode (paper_ZF_rep_domain X (Encoding.coded_source i))"
      using member by (simp only: meeting)
    have moved: "paper_ZF_rep_transport X i z \<in>
        explode (paper_ZF_rep_domain X (Encoding.coded_target i))"
      by (rule Input.transport_type[OF second at_source])
    show "paper_ZF_rep_transport Y i (body M d (h,z)) =
        body M d (Encoding.coded_compose i h, paper_ZF_rep_transport X i z)"
      by (rule paper_ZF_R_arrow_body_coherent[OF head first source second meeting member moved])
  qed
qed

theorem paper_ZF_R_arrow_code_type:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and output_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y)"
    and head: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
  shows "paper_ZF_R_arrow_encode signature stock Bound encode arrows \<sigma> \<tau> X Y M d
    \<in> explode (paper_ZF_R_arrow_bound Bound encode arrows X Y M)"
proof -
  interpret Pair: paper_ZF_action_pair objects "paper_ZF_image_code Bound encode arrows"
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
    "paper_ZF_rep_domain X" "paper_ZF_rep_transport X"
    "paper_ZF_rep_domain Y" "paper_ZF_rep_transport Y"
    by (unfold_locales; use input_action output_action in
      \<open>auto simp: paper_action_def paper_action_axioms_def paper_category_def\<close>)
  have member: "body M d \<in> Pair.exponential_fiber M"
    by (rule paper_ZF_R_arrow_body_exponential[OF input_action head])
  show ?thesis unfolding paper_ZF_R_arrow_encode_def paper_ZF_R_arrow_bound_def
    by (rule Pair.paper_ZF_encode_exponential_type[OF member])
qed

theorem paper_ZF_R_arrow_range_elements:
  assumes input_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) (paper_ZF_rep_transport X)"
    and output_action: "paper_action objects Encoding.coded_arrows
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>N. explode (paper_ZF_rep_domain Y N)) (paper_ZF_rep_transport Y)"
  shows "explode (paper_ZF_rep_domain
      (paper_ZF_R_arrow_representation signature stock Bound encode arrows \<sigma> \<tau> X Y) M) =
    image (paper_ZF_R_arrow_encode signature stock Bound encode arrows \<sigma> \<tau> X Y M)
      (paper_bbk_domain M (Arr \<sigma> \<tau>))"
  unfolding paper_ZF_R_arrow_representation_def paper_ZF_type_representation.select_convs
  by (rule paper_ZF_range_code_explode,
    rule paper_ZF_R_arrow_code_type[OF input_action output_action], assumption)

end

end
