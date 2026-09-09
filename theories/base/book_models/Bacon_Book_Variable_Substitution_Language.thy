theory Bacon_Book_Variable_Substitution_Language
  imports Bacon_Book_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Variable substitution respects partial logical signatures\<close>

text \<open>
  Substitution M[N/x] preserves type and the declared language when N
  has x's type and belongs to that language. The logical symbols of the
  result occur in M or N. This is a syntax lemma supporting the
  substitution and reduction clauses of Definition 9.1, p.190.
  Typing does not imply freedom from capture; a separate free-for guard
  remains required for β contraction and language substitution closure.
\<close>

lemma book_variable_subst_logical_occurrences:
  "named_logical_occurrences (named_subst n B A) \<subseteq>
    named_logical_occurrences A \<union> named_logical_occurrences B"
  by (induction A) auto

theorem book_variable_subst_language:
  assumes body: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and replacement: "book_in_language L \<Lambda> \<Sigma> G B (G n)"
  shows "book_in_language L \<Lambda> \<Sigma> G (named_subst n B A) \<tau>"
proof -
  have language: "named_in_language L \<Sigma> G (named_subst n B A) \<tau>"
    by (rule named_subst_language[OF book_language_named[OF body] book_language_named[OF replacement]])
  have allowed: "named_logical_occurrences A \<union> named_logical_occurrences B \<subseteq> \<Lambda>"
    using book_language_logical_occurrences[OF body] book_language_logical_occurrences[OF replacement] by blast
  have symbols: "named_logical_occurrences (named_subst n B A) \<subseteq> \<Lambda>"
    by (rule subset_trans[OF book_variable_subst_logical_occurrences allowed])
  show ?thesis unfolding book_in_language_def by (rule conjI[OF language symbols])
qed

end
