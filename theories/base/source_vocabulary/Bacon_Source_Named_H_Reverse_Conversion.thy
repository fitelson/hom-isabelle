theory Bacon_Source_Named_H_Reverse_Conversion
  imports Bacon_Source_Named_H_Conversion Bacon_Source_Named_Representation_Reflection
    Bacon_Source_Named_Decoder_Contexts
begin

section \<open>Named theorem preimages of source β and η biconditionals\<close>

text \<open>
  For a contextual source β or η step A→B between formulas, choose one
  finite prefix supporting both endpoints. Decode them in its identity
  chart, derive their native H biconditional, and encode that theorem.
  Its result is exactly the literal source A↔B, including the closed
  λ-defined biconditional operator of Figure 1.
  Source: Bacon–Dorr Figure 2, p.8, and Figure 1, p.6.

  Status. These are witnesses in the independently defined named calculus,
  obtained from source syntax and native named PC/β/η/MP only. No source-H
  theorem, general reverse-proof hypothesis, model, or β simplification
  of the biconditional operator is used.
\<close>

lemma paper_named_iff_prefix_preimage:
  assumes left: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and right: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and boundA: "source_free_bound A \<le> m" and boundB: "source_free_bound B \<le> m"
    and rich: "sg_rich G"
    and conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop
      (source_to_named G [0..<m] A) (source_to_named G [0..<m] B)"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = paper_iff A B"
proof -
  let ?A = "source_to_named G [0..<m] A"
  let ?B = "source_to_named G [0..<m] B"
  let ?N = "named_paper_iff G ?A ?B"
  have native: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H_iff_conversion[OF conversion rich])
  have encA: "named_to_source G [] ?A = A" by (rule source_prefix_decoder_encoding[OF left boundA rich])
  have encB: "named_to_source G [] ?B = B" by (rule source_prefix_decoder_encoding[OF right boundB rich])
  have encoded: "named_to_source G [] ?N = paper_iff A B"
    by (simp only: named_paper_iff_encoding[OF rich] encA encB)
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF native encoded])
qed

theorem paper_named_beta_preimage:
  assumes left: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and right: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step sbeta_contract A B" and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = paper_iff A B"
proof -
  let ?m = "max (source_free_bound A) (source_free_bound B)"
  have boundA: "source_free_bound A \<le> ?m" by simp
  have boundB: "source_free_bound B \<le> ?m" by simp
  have prefixA: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) A Prop"
    by (rule source_language_in_prefix[OF left boundA])
  have prefixB: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) B Prop"
    by (rule source_language_in_prefix[OF right boundB])
  have conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop
    (source_to_named G [0..< ?m] A) (source_to_named G [0..< ?m] B)"
    by (rule source_to_named_beta_step_conversion[OF step prefixA prefixB named_identity_prefix_chart rich])
  show ?thesis by (rule paper_named_iff_prefix_preimage[OF left right boundA boundB rich conversion])
qed

theorem paper_named_eta_preimage:
  assumes left: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and right: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step seta_contract A B" and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = paper_iff A B"
proof -
  let ?m = "max (source_free_bound A) (source_free_bound B)"
  have boundA: "source_free_bound A \<le> ?m" by simp
  have boundB: "source_free_bound B \<le> ?m" by simp
  have prefixA: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) A Prop"
    by (rule source_language_in_prefix[OF left boundA])
  have prefixB: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) B Prop"
    by (rule source_language_in_prefix[OF right boundB])
  have conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop
    (source_to_named G [0..< ?m] A) (source_to_named G [0..< ?m] B)"
    by (rule source_to_named_eta_step_conversion[OF step prefixA prefixB named_identity_prefix_chart rich])
  show ?thesis by (rule paper_named_iff_prefix_preimage[OF left right boundA boundB rich conversion])
qed

end
