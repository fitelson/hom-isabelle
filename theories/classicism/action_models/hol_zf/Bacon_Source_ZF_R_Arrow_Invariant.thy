theory Bacon_Source_ZF_R_Arrow_Invariant
  imports Bacon_Source_ZF_R_Arrow_Action Bacon_Source_ZF_R_Arrow_Injectivity
    Bacon_Source_ZF_R_Type_Invariant
begin

section \<open>The function-type construction preserves the induction invariant\<close>

text \<open>
  Assume the representation invariant already proved at σ and τ.
  The σ bijection supplies its inverse, and its action-map property
  supplies inverse equivariance. The τ forward map gives coherence
  and typing of the new function. Quasi-functionality separates
  original operators once both child encodings are injective.

  The resulting arrow domain is exactly the range of fσ→τM,
  with the inherited canonical exponential action. This is the
  function-type induction step of Proposition 3.22 (p.72), not
  an assumed all-type model interface.
\<close>

theorem paper_ZF_R_arrow_invariant:
  fixes X Y :: "'c paper_ZF_R_representation"
  assumes encoding: "paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows e ArrowBound"
    and quasi: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and child_input: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<sigma> X"
    and child_output: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<tau> Y"
  shows "paper_ZF_R_type_invariant Obj Arrows e ArrowBound (Arr \<sigma> \<tau>)
    (paper_ZF_R_arrow_representation \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y)"
proof -
  interpret Source: paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows e ArrowBound by (rule encoding)
  have original_input: "paper_action Obj Source.Encoding.coded_arrows
      Source.Encoding.coded_source Source.Encoding.coded_target Source.Encoding.coded_compose Source.Encoding.coded_identity
      (\<lambda>M. paper_bbk_domain M \<sigma>)
      (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<sigma>))"
    by (rule paper_ZF_reindex_action[
      OF paper_R_bbk_selected_type_action[where \<sigma>=\<sigma>, OF Source.R_category]
        Source.encode_injective Source.encode_bounded])
  have inverse_input: "paper_action_map Obj Source.Encoding.coded_arrows
      Source.Encoding.coded_source Source.Encoding.coded_target
      (\<lambda>M. explode (paper_ZF_rep_domain X M)) (paper_ZF_rep_transport X)
      (\<lambda>M. paper_bbk_domain M \<sigma>)
      (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<sigma>))
      (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M \<sigma>) X)"
    by (rule paper_ZF_R_type_invariant_inverse_map[OF child_input original_input])
  have forward_output: "paper_action_map Obj Source.Encoding.coded_arrows
      Source.Encoding.coded_source Source.Encoding.coded_target
      (\<lambda>M. paper_bbk_domain M \<tau>)
      (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<tau>))
      (\<lambda>M. explode (paper_ZF_rep_domain Y M)) (paper_ZF_rep_transport Y) (paper_ZF_rep_encode Y)"
    by (rule paper_ZF_R_type_invariant_forward[OF child_output])
  interpret Step: paper_ZF_R_arrow_step \<Sigma> G Obj Arrows e ArrowBound \<sigma> \<tau> X Y
    by unfold_locales (rule rt, rule inverse_input, rule forward_output)
  have input_action: "paper_action Obj Source.Encoding.coded_arrows
      Source.Encoding.coded_source Source.Encoding.coded_target Source.Encoding.coded_compose Source.Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain X M)) (paper_ZF_rep_transport X)"
    by (rule paper_ZF_R_type_invariant_action[OF child_input])
  have output_action: "paper_action Obj Source.Encoding.coded_arrows
      Source.Encoding.coded_source Source.Encoding.coded_target Source.Encoding.coded_compose Source.Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain Y M)) (paper_ZF_rep_transport Y)"
    by (rule paper_ZF_R_type_invariant_action[OF child_output])
  show ?thesis
  proof (rule paper_ZF_R_type_invariantI[
      OF Step.paper_ZF_R_arrow_range_action[OF input_action output_action]
        Step.paper_ZF_R_arrow_range_forward_map[OF input_action output_action]])
    fix M
    assume object: "M \<in> Obj"
    have injective: "inj_on (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M)
        (paper_bbk_domain M (Arr \<sigma> \<tau>))"
    proof (rule paper_ZF_R_arrow_encode_injective_from_children[OF encoding quasi object rt])
      fix N a
      assume no: "N \<in> Obj" and am: "a \<in> paper_bbk_domain N \<sigma>"
      show "paper_ZF_rep_encode X N a \<in> explode (paper_ZF_rep_domain X N)"
        by (rule paper_ZF_R_type_invariant_encode_type[OF child_input no am])
    next
      fix N
      assume no: "N \<in> Obj"
      show "inj_on (paper_ZF_rep_encode X N) (paper_bbk_domain N \<sigma>)"
        by (rule paper_ZF_R_type_invariant_injective[OF child_input no])
    next
      fix N
      assume no: "N \<in> Obj"
      show "inj_on (paper_ZF_rep_encode Y N) (paper_bbk_domain N \<tau>)"
        by (rule paper_ZF_R_type_invariant_injective[OF child_output no])
    qed
    have range: "explode (paper_ZF_rep_domain Step.arrow_representation M) =
        image (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M)
          (paper_bbk_domain M (Arr \<sigma> \<tau>))"
      by (rule Step.paper_ZF_R_arrow_range_elements[OF input_action output_action])
    show "bij_betw (paper_ZF_rep_encode Step.arrow_representation M) (paper_bbk_domain M (Arr \<sigma> \<tau>))
        (explode (paper_ZF_rep_domain Step.arrow_representation M))"
      by (simp only: bij_betw_def Step.paper_ZF_R_arrow_fields(3) range;
        rule conjI[OF injective refl])
  qed
qed

end
