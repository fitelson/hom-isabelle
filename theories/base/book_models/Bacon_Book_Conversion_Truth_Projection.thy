theory Bacon_Book_Conversion_Truth_Projection
  imports Bacon_Book_Conversion_Closed_Values Bacon_Book_Minimal_Validity
begin

section \<open>Truth is membership of the closed substituted formula\<close>

text \<open>
  v(Jg(A)) iff A[rep∘g]∈M. This is a consequence of the actual
  denotation and valuation definitions and their proved typing and
  representative-invariance properties, not a model axiom.
  Source role: the characteristic valuation in Bacon's term construction,
  p.321. A may be open; its substituted representative is closed.
\<close>

theorem book_conversion_truth_projection:
  assumes rich: "sg_rich G"
    and maximal: "book_closed_maximal_extension \<Sigma> G S M"
    and language: "book_theory_formula \<Sigma> G A"
    and typed: "book_env_typed (book_conversion_domain \<Sigma> G) G g"
  shows "book_conversion_valuation M (book_conversion_denote \<Sigma> G g A) \<longleftrightarrow>
    book_environment_subst {} (book_conversion_representatives g) A \<in> M"
  by (simp only: book_conversion_denote_eq[OF book_language_type[OF language]];
      rule book_conversion_valuation_class[OF rich maximal
        book_conversion_substituted_closed_terms[OF language typed]])

section \<open>Closed formula validity is membership\<close>

text \<open>
  For closed A in the full witness signature, truth at all typed
  assignments iff A∈M. The validity-to-membership direction uses the actual
  constructed assignment g₀; validity is not inferred from an empty
  assignment space. This lemma does not assume a logical model or
  witness completeness. Those additional truth-clause obligations are
  handled by the separate model construction.
\<close>

theorem book_henkin_conversion_closed_valid_iff:
  assumes rich: "sg_rich G"
    and maximal: "book_closed_maximal_extension (book_henkin_full_signature \<Sigma> G) G S M"
    and language: "book_theory_formula (book_henkin_full_signature \<Sigma> G) G A"
    and closed: "named_fv A = {}"
  shows "book_formula_valid (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G
    (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G)
    (book_conversion_valuation M) A \<longleftrightarrow> A \<in> M"
proof -
  let ?D = "book_conversion_domain (book_henkin_full_signature \<Sigma> G) G"
  let ?J = "book_conversion_denote (book_henkin_full_signature \<Sigma> G) G"
  have at: "book_conversion_valuation M (?J g A) \<longleftrightarrow> A \<in> M"
    if typed: "book_env_typed ?D G g" for g
    by (simp only: book_conversion_truth_projection[OF rich maximal language typed]
        book_environment_subst_closed_fixed[OF closed])
  show ?thesis
  proof
    assume valid: "book_formula_valid ?D G ?J (book_conversion_valuation M) A"
    have typed: "book_env_typed ?D G (book_henkin_conversion_assignment \<Sigma> G)"
      by (rule book_henkin_conversion_assignment_typed[OF rich])
    have truth: "book_conversion_valuation M (?J (book_henkin_conversion_assignment \<Sigma> G) A)"
      by (rule book_formula_validE[OF valid typed])
    show "A \<in> M" by (rule iffD1[OF at[OF typed] truth])
  next
    assume member: "A \<in> M"
    show "book_formula_valid ?D G ?J (book_conversion_valuation M) A"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed ?D G g"
      show "book_conversion_valuation M (?J g A)"
        by (rule iffD2[OF at[OF typed] member])
    qed
  qed
qed

end
