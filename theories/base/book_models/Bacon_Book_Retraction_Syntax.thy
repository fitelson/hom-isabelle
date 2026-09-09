theory Bacon_Book_Retraction_Syntax
  imports Bacon_Book_Minimal_Formula_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Retraction_Steps
begin

section \<open>Fresh-variable retraction preserves the book's literal syntax\<close>

text \<open>
  Replace constants outside Ω of type τ by a variable vτ of that type.
  The logical signature is unchanged. The closed definitions of ⊥ and
  ¬ contain no nonlogical constants, so this retraction fixes them
  literally, unlike a swap of their bound names.
  Source role: signature-relative proof substitution, Bacon pp.99–102.

  Status. Syntax and language guards only. Immediate β and η steps
  retain their capture/freshness conditions when v avoids the endpoint
  names. No theory substitution rule, H identification, model, or
  richness premise is added.
\<close>

lemma book_retract_logical_occurrences:
  "named_logical_occurrences (named_retract \<Omega> v A) = named_logical_occurrences A"
  by (induction A) (simp_all split: if_splits)

lemma book_retract_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and stock: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>"
  shows "book_in_language L \<Lambda> \<Omega> G (named_retract \<Omega> v A) \<tau>"
proof -
  have typed: "has_ntype L G (named_retract \<Omega> v A) \<tau>"
    by (rule named_retract_type[OF book_language_type[OF language] stock])
  have logicals: "named_logical_occurrences (named_retract \<Omega> v A) \<subseteq> \<Lambda>"
    by (simp only: book_retract_logical_occurrences; rule book_language_logical_occurrences[OF language])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed named_retract_signature] logicals])
qed

lemma book_retract_imp:
  "named_retract \<Omega> v (book_imp A B) = book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  by (simp only: book_imp_def named_retract.simps)

lemma book_retract_all:
  "named_retract \<Omega> v (book_all G n A) = book_all G n (named_retract \<Omega> v A)"
  by (simp only: book_all_def named_retract.simps)

lemma book_retract_bottom:
  "named_retract \<Omega> v (book_bottom G) = book_bottom G"
  by (simp only: book_bottom_def named_retract.simps)

lemma book_retract_not_const:
  "named_retract \<Omega> v (book_not_const G) = book_not_const G"
  by (simp only: book_not_const_def named_retract.simps book_retract_imp book_retract_bottom)

lemma book_retract_not:
  "named_retract \<Omega> v (book_not G A) = book_not G (named_retract \<Omega> v A)"
  by (simp only: book_not_def named_retract.simps book_retract_not_const)

lemma book_retract_beta_equivalent:
  assumes step: "named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A"
    and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars A \<union> named_vars B"
  shows "named_compatible_step named_beta_contract (named_retract \<Omega> v A) (named_retract \<Omega> v B) \<or>
    named_compatible_step named_beta_contract (named_retract \<Omega> v B) (named_retract \<Omega> v A)"
  using step
proof
  assume forward: "named_compatible_step named_beta_contract A B"
  show ?thesis by (rule disjI1, rule named_retract_beta_step[OF forward fresh])
next
  assume backward: "named_compatible_step named_beta_contract B A"
  have reverse_fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars B \<union> named_vars A" using fresh by blast
  show ?thesis by (rule disjI2, rule named_retract_beta_step[OF backward reverse_fresh])
qed

lemma book_retract_eta_equivalent:
  assumes step: "named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A"
    and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars A \<union> named_vars B"
  shows "named_compatible_step named_eta_contract (named_retract \<Omega> v A) (named_retract \<Omega> v B) \<or>
    named_compatible_step named_eta_contract (named_retract \<Omega> v B) (named_retract \<Omega> v A)"
  using step
proof
  assume forward: "named_compatible_step named_eta_contract A B"
  show ?thesis by (rule disjI1, rule named_retract_eta_step[OF forward fresh])
next
  assume backward: "named_compatible_step named_eta_contract B A"
  have reverse_fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars B \<union> named_vars A" using fresh by blast
  show ?thesis by (rule disjI2, rule named_retract_eta_step[OF backward reverse_fresh])
qed

end
