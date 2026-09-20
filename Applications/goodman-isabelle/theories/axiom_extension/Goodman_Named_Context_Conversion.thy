theory Goodman_Named_Context_Conversion
  imports Goodman_Expansion_Language
begin

section \<open>Transport guarded expansion conversion to the named translation\<close>

theorem gi_named_conversion_from_expansion:
  assumes rich: "sg_rich G"
    and typed_A: "\<Gamma> \<turnstile> A : \<tau>" and typed_B: "\<Gamma> \<turnstile> B : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and conversion: "sbeta_eta_equiv_in_signature book_minimal_logical_type \<Sigma> \<Gamma> \<tau>
      (gi_expand G k A) (gi_expand G k B)"
  shows "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    (gi_to_book G ns k A) (gi_to_book G ns k B)"
proof -
  let ?DA = "source_to_named G ns (gi_expand G k A)"
  let ?DB = "source_to_named G ns (gi_expand G k B)"
  have nc: "named_chart G \<Gamma> ns" by (rule gi_chart_is_named_chart[OF distinct chart])
  have languages:
    "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k A) \<tau> \<and>
     sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k B) \<tau>"
    by (rule sbeta_eta_equiv_in_signature_language[OF conversion])
  have at: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k A) \<tau>"
    and bt: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k B) \<tau>"
    using languages unfolding sterm_in_language_def by blast+
  have al: "named_in_language book_minimal_logical_type \<Sigma> G ?DA \<tau>"
    by (rule source_to_named_language[OF conjunct1[OF languages] nc rich])
  have bl: "named_in_language book_minimal_logical_type \<Sigma> G ?DB \<tau>"
    by (rule source_to_named_language[OF conjunct2[OF languages] nc rich])
  have middle: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau> ?DA ?DB"
    by (rule source_to_named_conversion[OF conversion nc rich])
  have alpha_A: "named_alpha G ?DA (gi_to_book G ns k A)"
    by (rule gi_decoder_alignment[OF rich typed_A chart distinct at])
  have alpha_B: "named_alpha G ?DB (gi_to_book G ns k B)"
    by (rule gi_decoder_alignment[OF rich typed_B chart distinct bt])
  have first: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    (gi_to_book G ns k A) ?DA"
    by (rule named_beta_eta_in_language.Sym, rule named_alpha_implies_beta_eta[OF alpha_A al])
  have last: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    ?DB (gi_to_book G ns k B)"
    by (rule named_alpha_implies_beta_eta[OF alpha_B bl])
  show ?thesis by (rule named_beta_eta_in_language.Trans[OF first named_beta_eta_in_language.Trans[OF middle last]])
qed

section \<open>Every old constructor context is covered\<close>

theorem gi_to_book_beta_context:
  assumes rich: "sg_rich G" and step: "compatible_step beta_contract A B"
    and typed_A: "\<Gamma> \<turnstile> A : \<tau>" and typed_B: "\<Gamma> \<turnstile> B : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants_A: "gi_constants_admitted k \<Sigma> A"
    and constants_B: "gi_constants_admitted k \<Sigma> B"
  shows "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    (gi_to_book G ns k A) (gi_to_book G ns k B)"
proof -
  have al: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k A) \<tau>"
    by (rule gi_expand_language[OF rich typed_A chart distinct constants_A])
  have bl: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k B) \<tau>"
    by (rule gi_expand_language[OF rich typed_B chart distinct constants_B])
  have at: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k A) \<tau>"
    and an: "sterm_in_signature \<Sigma> (gi_expand G k A)"
    using al unfolding sterm_in_language_def by blast+
  have bt: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k B) \<tau>"
    and bn: "sterm_in_signature \<Sigma> (gi_expand G k B)"
    using bl unfolding sterm_in_language_def by blast+
  have expanded: "scompatible_step sbeta_contract (gi_expand G k A) (gi_expand G k B)"
    by (rule gi_expand_beta_context[OF step])
  have conversion: "sbeta_eta_equiv_in_signature book_minimal_logical_type \<Sigma> \<Gamma> \<tau>
    (gi_expand G k A) (gi_expand G k B)"
    by (rule sbeta_eta_equiv_in_signature.Beta[OF at bt an bn expanded])
  show ?thesis by (rule gi_named_conversion_from_expansion[OF rich typed_A typed_B chart distinct conversion])
qed

theorem gi_to_book_eta_context:
  assumes rich: "sg_rich G" and step: "compatible_step eta_contract A B"
    and typed_A: "\<Gamma> \<turnstile> A : \<tau>" and typed_B: "\<Gamma> \<turnstile> B : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants_A: "gi_constants_admitted k \<Sigma> A"
    and constants_B: "gi_constants_admitted k \<Sigma> B"
  shows "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    (gi_to_book G ns k A) (gi_to_book G ns k B)"
proof -
  have al: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k A) \<tau>"
    by (rule gi_expand_language[OF rich typed_A chart distinct constants_A])
  have bl: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k B) \<tau>"
    by (rule gi_expand_language[OF rich typed_B chart distinct constants_B])
  have at: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k A) \<tau>"
    and an: "sterm_in_signature \<Sigma> (gi_expand G k A)"
    using al unfolding sterm_in_language_def by blast+
  have bt: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k B) \<tau>"
    and bn: "sterm_in_signature \<Sigma> (gi_expand G k B)"
    using bl unfolding sterm_in_language_def by blast+
  have expanded: "scompatible_step seta_contract (gi_expand G k A) (gi_expand G k B)"
    by (rule gi_expand_eta_context[OF step])
  have conversion: "sbeta_eta_equiv_in_signature book_minimal_logical_type \<Sigma> \<Gamma> \<tau>
    (gi_expand G k A) (gi_expand G k B)"
    by (rule sbeta_eta_equiv_in_signature.Eta[OF at bt an bn expanded])
  show ?thesis by (rule gi_named_conversion_from_expansion[OF rich typed_A typed_B chart distinct conversion])
qed

text \<open>
  These conclusions are in the actual typed, signature-guarded named βη
  relation, not merely raw steps in the intermediate expansion. The
  arbitrary old context may contain application, abstraction, identity,
  Boolean operators and either quantifier. Both endpoint guards are
  retained. No rule of contextual equivalence from a truth premise is added.
\<close>

end
