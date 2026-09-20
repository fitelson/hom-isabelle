theory Goodman_Conversion_Derivability
  imports Goodman_Named_Context_Conversion
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Conversion
begin

section \<open>Conversion yields actual book-H implications\<close>

theorem gi_H_conversion_pair:
  assumes rich: "sg_rich G"
    and conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
  shows "book_H \<Sigma> G (book_imp A B) \<and> book_H \<Sigma> G (book_imp B A)"
proof -
  have pair: "book_theory_derivable \<Sigma> G {} (book_imp A B) \<and>
    book_theory_derivable \<Sigma> G {} (book_imp B A)"
    by (rule book_theory_conversion_pair[OF conversion refl])
  show ?thesis using pair by (simp only: book_H_iff_theory[OF rich])
qed

theorem gi_goodman_conversion_transport:
  assumes rich: "sg_rich G"
    and conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
    and derivation: "goodman_book_proves \<Sigma> G T A"
  shows "goodman_book_proves \<Sigma> G T B"
proof -
  have H_implication: "book_H \<Sigma> G (book_imp A B)"
    using gi_H_conversion_pair[OF rich conversion] by blast
  have implication: "goodman_book_proves \<Sigma> G T (book_imp A B)"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H[OF H_implication])
  have bl: "book_theory_formula \<Sigma> G B"
    using named_beta_eta_languages[OF conversion] by (simp only: book_language_UNIV; blast)
  show ?thesis by (rule goodman_book_proves.MP[OF derivation implication bl])
qed

corollary gi_goodman_conversion_iff:
  assumes rich: "sg_rich G"
    and conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
  shows "goodman_book_proves \<Sigma> G T A \<longleftrightarrow> goodman_book_proves \<Sigma> G T B"
  by (rule iffI,
    rule gi_goodman_conversion_transport[OF rich conversion], assumption,
    rule gi_goodman_conversion_transport[OF rich named_beta_eta_in_language.Sym[OF conversion]], assumption)

text \<open>
  This transport uses H implications derived from syntactic conversion.
  It does NOT introduce contextual Equivalence from an assumed material
  biconditional, nor apply PE to temporary local assumptions.
\<close>

section \<open>Conversion-schema implications from the old constructor calculus\<close>

theorem gi_H_beta_context_implications:
  assumes rich: "sg_rich G" and step: "compatible_step beta_contract A B"
    and typed_A: "\<Gamma> \<turnstile> A : Prop" and typed_B: "\<Gamma> \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants_A: "gi_constants_admitted k \<Sigma> A"
    and constants_B: "gi_constants_admitted k \<Sigma> B"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp A B)) \<and>
    book_H \<Sigma> G (gi_to_book G ns k (Imp B A))"
  using gi_H_conversion_pair[OF rich
    gi_to_book_beta_context[OF rich step typed_A typed_B chart distinct constants_A constants_B]]
  by (simp only: gi_to_book.simps)

theorem gi_H_eta_context_implications:
  assumes rich: "sg_rich G" and step: "compatible_step eta_contract A B"
    and typed_A: "\<Gamma> \<turnstile> A : Prop" and typed_B: "\<Gamma> \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants_A: "gi_constants_admitted k \<Sigma> A"
    and constants_B: "gi_constants_admitted k \<Sigma> B"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp A B)) \<and>
    book_H \<Sigma> G (gi_to_book G ns k (Imp B A))"
  using gi_H_conversion_pair[OF rich
    gi_to_book_eta_context[OF rich step typed_A typed_B chart distinct constants_A constants_B]]
  by (simp only: gi_to_book.simps)

section \<open>The translated MP rule\<close>

theorem gi_H_MP:
  assumes rich: "sg_rich G" and typed_B: "\<Gamma> \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and constants_B: "gi_constants_admitted k \<Sigma> B"
    and first: "book_H \<Sigma> G (gi_to_book G ns k A)"
    and second: "book_H \<Sigma> G (gi_to_book G ns k (Imp A B))"
  shows "book_H \<Sigma> G (gi_to_book G ns k B)"
proof -
  have first_d: "book_theory_derivable \<Sigma> G {} (gi_to_book G ns k A)"
    using first by (simp only: book_H_iff_theory[OF rich])
  have second_d: "book_theory_derivable \<Sigma> G {}
    (book_imp (gi_to_book G ns k A) (gi_to_book G ns k B))"
    using second by (simp only: book_H_iff_theory[OF rich] gi_to_book.simps)
  have bl: "book_theory_formula \<Sigma> G (gi_to_book G ns k B)"
    by (rule gi_to_book_language[OF rich typed_B chart constants_B])
  have result: "book_theory_derivable \<Sigma> G {} (gi_to_book G ns k B)"
    by (rule book_theory_derivable.MP[OF first_d second_d bl])
  show ?thesis using result by (simp only: book_H_iff_theory[OF rich])
qed

text \<open>
  These are actual derivability results, not model validity. The old
  Beta/Eta constructors conclude a primitive conjunction of the two
  implications. This leaf proves both implications; the downstream
  Goodman_H_Conversion_Schemas assembles their actual translated book_and
  formula. Neither leaf claims whole-proof H preservation.
\<close>

end
