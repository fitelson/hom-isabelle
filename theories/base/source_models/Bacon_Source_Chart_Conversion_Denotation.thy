theory Bacon_Source_Chart_Conversion_Denotation
  imports Bacon_Source_Chart_Denotation
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Decoder_Conversion
begin

section \<open>Chart denotation respects guarded source conversion\<close>

text \<open>
  In an arbitrary named BBK model, Γ ⊢ A ≡βη B:τ implies
  ⟦A⟧ⁿˢ,ρ = ⟦B⟧ⁿˢ,ρ for a chart ns of Γ and a Γ-typed ρ.
  Source: Bacon–Dorr Definition 3.1(ii.d), pp.43–44.

  Representation. Decode the whole guarded source conversion, include it
  in raw typed named βη, and apply the independently stated named-model
  clause. The chart assignment need only be adequate for the endpoints;
  it need not cover extra names in the intermediate conversion proof.
  This is not a context-erasure theorem or an H soundness assumption.
\<close>

context paper_named_bbk_model
begin

theorem chart_denote_conversion:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> \<tau> A B"
    and chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "chart_denote ns \<rho> A = chart_denote ns \<rho> B"
proof -
  have source_languages: "sterm_in_language paper_logical_type signature \<Gamma> A \<tau> \<and>
    sterm_in_language paper_logical_type signature \<Gamma> B \<tau>"
    by (rule sbeta_eta_equiv_in_signature_language[OF conversion])
  have at: "has_stype paper_logical_type \<Gamma> A \<tau>"
    using conjunct1[OF source_languages] unfolding sterm_in_language_def by (rule conjunct1)
  have bt: "has_stype paper_logical_type \<Gamma> B \<tau>"
    using conjunct2[OF source_languages] unfolding sterm_in_language_def by (rule conjunct1)
  have decoded: "named_beta_eta_in_language paper_logical_type signature stock \<tau>
    (source_to_named stock ns A) (source_to_named stock ns B)"
    by (rule source_to_named_conversion[OF conversion chart stock_rich])
  have raw: "named_raw_beta_eta paper_logical_type stock \<tau>
    (source_to_named stock ns A) (source_to_named stock ns B)"
    by (rule named_conversion_to_raw[OF decoded])
  have named_languages: "named_in_language paper_logical_type signature stock (source_to_named stock ns A) \<tau> \<and>
    named_in_language paper_logical_type signature stock (source_to_named stock ns B) \<tau>"
    by (rule named_beta_eta_languages[OF decoded])
  show ?thesis unfolding chart_denote_def
    by (rule denote_beta_eta[OF raw conjunct1[OF named_languages] conjunct2[OF named_languages]
      named_chart_assignment_typed[OF chart env] chart_decoder_adequate[OF at chart] chart_decoder_adequate[OF bt chart]])
qed

end

end
