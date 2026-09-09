theory Bacon_Book_Alpha_Language
  imports Bacon_Book_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha
begin

section \<open>Bound-variable relabelling preserves declared logical symbols\<close>

text \<open>
  Relabelling bound variables changes neither the nonlogical signature nor
  the logical symbols of a term. Type preservation is already checked for
  the independently generated named α relation. Together these give full
  declared-language preservation, including partial logical signatures.
  Source role: α steps in Definition 3.10's reduction relation, p.73.
\<close>

lemma book_swap_logical_occurrences:
  "named_logical_occurrences (named_swap x y A) = named_logical_occurrences A"
  by (induction A) (simp_all add: named_swap.simps)

lemma book_alpha_logical_occurrences:
  assumes alpha: "named_alpha G A B"
  shows "named_logical_occurrences A = named_logical_occurrences B"
  using alpha
  by (induction rule: named_alpha.induct)
     (simp_all add: book_swap_logical_occurrences)

theorem book_alpha_language_iff:
  assumes alpha: "named_alpha G A B"
  shows "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<longleftrightarrow>
    book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  by (simp only: book_in_language_def named_in_language_def
      named_alpha_type_iff[OF alpha] named_alpha_signature[OF alpha]
      book_alpha_logical_occurrences[OF alpha])

end
