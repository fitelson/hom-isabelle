theory Bacon_Book_Canonical_Model_Existence
  imports Bacon_Book_Conversion_Expanded_Model_Existence Bacon_Book_Constant_Model_Pullback
begin

section \<open>A model of the original signature and unrenamed premises\<close>

text \<open>
  Retain the expanded term-class carrier, domains, App, v and κ, but
  interpret an original term A by J′g(A)=Jg(Original(A)). The original
  signature may have no closed terms at some types; we do not shrink
  the semantic domains to classes of old terms. Original constant names
  embed in Σ∞ at their declared types, so the checked model pullback
  applies. Its conclusion interprets the ORIGINAL language and premises.

  Source: Bacon's Theorem 15.3, pp.320–321. The result below covers
  arbitrary well-formed premise sets, including open formulas, arbitrary
  nonlogical signatures, and the full F type grammar. It retains the
  minimal logical basis, rich variable stock and witnessed closed-value
  convention of the independently defined model class. General 𝒥 and
  richer primitive bases are separate source-scope obligations.
\<close>

theorem book_henkin_original_model_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_full_minimal_model
      (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G)
      (book_conversion_app (book_henkin_full_signature \<Sigma> G) G)
      \<Sigma> G
      (book_constant_pullback_denote (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_conversion_valuation M)
      (book_conversion_logical_value (book_henkin_full_signature \<Sigma> G) G) \<and>
    (\<forall>A\<in>S. book_formula_valid (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G
      (book_constant_pullback_denote (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_conversion_valuation M) A)"
proof -
  let ?\<Omega> = "book_henkin_full_signature \<Sigma> G"
  let ?D = "book_conversion_domain ?\<Omega> G"
  let ?app = "book_conversion_app ?\<Omega> G"
  let ?J = "book_conversion_denote ?\<Omega> G"
  let ?k = "book_conversion_logical_value ?\<Omega> G"
  obtain M where model: "book_full_minimal_model ?D ?app ?\<Omega> G ?J (book_conversion_valuation M) ?k"
    and premise_truth: "\<forall>A\<in>S. book_formula_valid ?D G ?J (book_conversion_valuation M)
      (book_constant_rename BookOriginal A)"
    using book_henkin_expanded_model_exists[OF rich language consistent] by blast
  interpret Model: book_full_minimal_model ?D ?app ?\<Omega> G ?J "book_conversion_valuation M" ?k
    by (rule model)
  have maps: "BookOriginal c \<in> ?\<Omega> \<sigma>" if "c \<in> \<Sigma> \<sigma>" for \<sigma> c
    by (simp only: book_henkin_full_original_iff; rule that)
  have pulled: "book_full_minimal_model ?D ?app \<Sigma> G
    (book_constant_pullback_denote ?J BookOriginal) (book_conversion_valuation M) ?k"
    by (rule Model.book_constant_pullback_full_minimal_model[OF maps])
  have original_truth: "\<forall>A\<in>S. book_formula_valid ?D G
    (book_constant_pullback_denote ?J BookOriginal) (book_conversion_valuation M) A"
    using premise_truth by (simp only: book_formula_valid_def book_constant_pullback_denote_def)
  show ?thesis by (rule exI[where x=M], rule conjI[OF pulled original_truth])
qed

text \<open>
  The following existential packaging exposes the model fields on an
  explicit carrier. This is existence, not a restriction of the independent
  model predicate to models produced by the construction. Later semantic
  consequence will quantify over every model on that carrier.
\<close>

corollary book_canonical_model_existence:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_theory_consistent \<Sigma> G S"
  shows "\<exists>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
    book_full_minimal_model D app \<Sigma> G J V k \<and>
    (\<forall>A\<in>S. book_formula_valid D G J V A)"
proof -
  obtain M where model: "book_full_minimal_model
      (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G)
      (book_conversion_app (book_henkin_full_signature \<Sigma> G) G) \<Sigma> G
      (book_constant_pullback_denote (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_conversion_valuation M) (book_conversion_logical_value (book_henkin_full_signature \<Sigma> G) G)"
    and premise_truth: "\<forall>A\<in>S. book_formula_valid
      (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G
      (book_constant_pullback_denote (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_conversion_valuation M) A"
    using book_henkin_original_model_exists[OF rich language consistent] by blast
  show ?thesis by (intro exI; rule conjI[OF model premise_truth])
qed

end
