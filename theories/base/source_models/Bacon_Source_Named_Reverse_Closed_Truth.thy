theory Bacon_Source_Named_Reverse_Closed_Truth
  imports Bacon_Source_Named_Reverse_Model
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Closed_Roundtrip
begin

section \<open>The reverse model preserves closed named values and truth\<close>

text \<open>
  For a closed named A:τ, interpreting its source encoding in the reverse
  model gives (τ,⟦A⟧ᵍ), for every typed named assignment g. The finite
  source environment ρ is arbitrary because the encoding uses no slots.
  Source role: the closed-term consequence of locality in Bacon–Dorr
  Definition 3.1(ii.c), pp.43–44, and the reverse representation bridge.

  Isabelle representation. Use the tagged model's erased agreement with
  the empty chart. Decoding the encoding is α-equivalent to A; the proved
  closed α denotation theorem compares the empty assignment with g.
  This proves the closed case only. It does not assert open-formula
  transport, an untagged value isomorphism, or named H soundness.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_reverse_closed_denote:
  assumes language: "named_in_language paper_logical_type signature stock A \<tau>"
    and closed: "named_fv A = {}" and typed: "named_env_typed domain stock g"
  shows "named_erased_denote stock model_tag_denote \<rho> (named_to_source stock [] A) = (\<tau>, denote g A)"
proof -
  let ?E = "named_to_source stock [] A"
  let ?B = "source_to_named stock [] ?E"
  have source_language: "sterm_in_language paper_logical_type signature [] ?E \<tau>"
    by (rule named_to_source_closed_language[OF language closed])
  have source_type: "has_stype paper_logical_type [] ?E \<tau>"
    using source_language unfolding sterm_in_language_def by (rule conjunct1)
  have decoded_language: "named_in_language paper_logical_type signature stock ?B \<tau>"
    by (rule source_to_named_language[OF source_language named_chart_Nil stock_rich])
  have decoded_closed: "named_fv ?B = {}"
    by (rule source_to_named_closed_fv[OF source_type stock_rich])
  have alpha: "named_alpha stock ?B A"
    by (rule named_closed_roundtrip_alpha[OF language closed stock_rich])
  have empty_typed: "named_env_typed domain stock Map.empty"
    by (simp add: named_env_typed_def)
  have payload: "denote Map.empty ?B = denote g A"
    by (rule paper_named_closed_alpha_denote[OF alpha decoded_language decoded_closed empty_typed typed])
  have erased: "named_erased_denote stock model_tag_denote \<rho> ?E =
    model_tag_denote (named_chart_assignment [] \<rho>) ?B"
    by (rule named_erased_denote_agrees[OF model_type_tagging source_language pbbk_env_empty named_chart_Nil])
  have untag_empty: "named_untag_assignment (named_chart_assignment [] \<rho>) = Map.empty"
    by (rule ext) (simp add: named_chart_assignment_empty named_untag_assignment_def)
  have tagged: "model_tag_denote (named_chart_assignment [] \<rho>) ?B = (\<tau>, denote Map.empty ?B)"
    by (simp only: model_tag_denote_eq[OF decoded_language] untag_empty)
  show ?thesis by (simp only: erased tagged payload)
qed

corollary paper_named_reverse_closed_truth:
  assumes language: "named_in_language paper_logical_type signature stock A Prop"
    and closed: "named_fv A = {}" and typed: "named_env_typed domain stock g"
  shows "model_tag_valuation (named_erased_denote stock model_tag_denote \<rho> (named_to_source stock [] A)) =
    valuation (denote g A)"
  by (simp only: paper_named_reverse_closed_denote[OF language closed typed] model_tag_valuation_def snd_conv)

end

end
