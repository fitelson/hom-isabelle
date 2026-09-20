theory Goodman_H_Certificate_Interface
  imports Goodman_H_Universal_Instantiation
    Bacon_Book_Environment_Development.Bacon_Book_H_Soundness
    Bacon_Book_Environment_Development.Bacon_Book_Minimal_Existential_Truth
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Signature_Conservativity
begin

section \<open>Use the proved H completeness theorem without changing its scope\<close>

theorem gi_H_validity_certificate:
  fixes \<Sigma> :: "'c ssignature" and A :: "'c book_named_term"
  assumes rich: "sg_rich G" and language: "book_theory_formula \<Sigma> G A"
    and valid: "\<And>D :: otype \<Rightarrow> ('c book_henkin_name) book_named_term set set.
      \<And>app J V c g. book_full_minimal_model D app \<Sigma> G J V c \<Longrightarrow>
        book_env_typed D G g \<Longrightarrow> V (J g A)"
  shows "book_H \<Sigma> G A"
  unfolding book_H_canonical_completeness[OF rich language] book_canonical_consequence_def
  by (intro allI impI book_formula_validI; rule valid; assumption)

lemma gi_H_alpha_transport:
  assumes rich: "sg_rich G" and alpha: "named_alpha G A B" and derivation: "book_H \<Sigma> G A"
  shows "book_H \<Sigma> G B"
proof -
  have language: "named_in_language book_minimal_logical_type \<Sigma> G A Prop"
    using book_H_language[OF rich derivation] by (simp only: book_language_UNIV)
  have conv: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
    by (rule named_alpha_implies_beta_eta[OF alpha language])
  have ad: "book_theory_derivable \<Sigma> G {} A"
    using derivation by (simp only: book_H_iff_theory[OF rich])
  have bd: "book_theory_derivable \<Sigma> G {} B"
    by (rule book_theory_conversion_transport[OF conv ad])
  show ?thesis using bd by (simp only: book_H_iff_theory[OF rich])
qed

lemma gi_H_imp_trans:
  assumes rich: "sg_rich G"
    and al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and cl: "book_theory_formula \<Sigma> G C"
    and ab: "book_H \<Sigma> G (book_imp A B)" and bc: "book_H \<Sigma> G (book_imp B C)"
  shows "book_H \<Sigma> G (book_imp A C)"
  using book_theory_imp_trans[OF al bl cl, where S="{}"] ab bc
  by (simp only: book_H_iff_theory[OF rich])

lemma gi_constants_universal:
  "gi_constants_admitted k (\<lambda>_. UNIV) A"
  by (induction A) simp_all

text \<open>
  The certificate quantifies every independent full-minimal model on the
  exact carrier used by the upstream H completeness theorem. It neither
  assumes full function spaces nor uses generic C completeness.
\<close>

end
