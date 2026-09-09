theory Bacon_Book_Conjunction_Constant_Substitution
  imports Bacon_Book_Conjunction_Variable_Substitution
    Bacon_Book_Conjunction_Background_Fresh_Constant Bacon_Book_Constant_Substitution_Abstraction
begin

section \<open>Nonlogical-constant substitution in native theorems\<close>

text \<open>
  If ⊢∧A and N:σ is free for the ordinary nonlogical constant c:σ
  in A, then ⊢∧A[N/c:σ]. Encode the theorem as a proof from Π∧.
  The proved retraction keeps Π∧ and its conjunction tag fixed while
  replacing Inl(c):σ by a fresh variable. Global-theory substitution
  inserts enc(N), and the fresh-marker equation gives the desired result.
  Source: Definition 5.2, p.99, for the extension in §5.2, p.104.

  No empty-premise minimal constant-substitution theorem is applied to a
  proof from Π∧. Only ordinary native constants are replaced; primitive
  ∧ remains a logical symbol. The native empty-premise guard matters:
  an arbitrary theory need not permit substitution for its constants.
\<close>

lemma book_conj_encoded_empty:
  "book_conj_encoded_premises \<Sigma> G {} = book_conj_axioms \<Sigma> G"
  by (simp add: book_conj_encoded_premises_def)

theorem book_conj_theory_constant_substitution:
  assumes rich: "sg_rich G"
    and derivation: "book_conj_theory_derivable \<Sigma> G {} A"
    and replacement: "book_in_language book_conj_logical_type UNIV \<Sigma> G B \<sigma>"
    and free_for: "book_const_free_for B c \<sigma> A"
  shows "book_conj_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> B A)"
proof -
  let ?target = "book_conj_target_signature \<Sigma>"
  let ?P = "book_conj_axioms \<Sigma> G"
  have printed: "book_printed_theory_derivable ?target G ?P (book_conj_encode A)"
    using book_conj_theory_encode[OF derivation] by (simp only: book_conj_encoded_empty)
  have encoded: "book_theory_derivable ?target G ?P (book_conj_encode A)"
    by (rule book_printed_theory_to_theory[OF printed])
  obtain x where xtype: "G x = \<sigma>"
    and fresh: "x \<notin> named_vars (book_conj_encode A) \<union> named_vars (book_conj_encode B)"
    and abstracted: "book_theory_derivable ?target G ?P
      (book_const_subst (Inl c) \<sigma> (NVar x) (book_conj_encode A))"
    using book_conj_background_fresh_constant_variable[
      where c=c and \<sigma>=\<sigma> and F="named_vars (book_conj_encode B)",
      OF rich encoded named_vars_finite] by blast
  have fresh_A: "x \<notin> named_vars (book_conj_encode A)" using fresh by blast
  have bl: "book_in_language book_minimal_logical_type UNIV ?target G (book_conj_encode B) (G x)"
    by (simp only: xtype; rule book_conj_encode_language[OF replacement])
  have encoded_free_for: "book_const_free_for (book_conj_encode B) (Inl c) \<sigma> (book_conj_encode A)"
    by (rule iffD2[OF book_conj_encode_const_free_for free_for])
  have permitted: "named_free_for (book_conj_encode B) x
      (book_const_subst (Inl c) \<sigma> (NVar x) (book_conj_encode A))"
    by (rule book_const_abstract_free_for[OF fresh_A encoded_free_for])
  have instantiated: "book_theory_derivable ?target G ?P
    (named_subst x (book_conj_encode B) (book_const_subst (Inl c) \<sigma> (NVar x) (book_conj_encode A)))"
    by (rule book_theory_variable_substitution[OF rich abstracted bl permitted])
  have target_result: "book_theory_derivable ?target G ?P
    (book_const_subst (Inl c) \<sigma> (book_conj_encode B) (book_conj_encode A))"
    using instantiated by (simp only: book_const_abstract_instantiate[OF fresh_A])
  have printed_result: "book_printed_theory_derivable ?target G
    (book_conj_encoded_premises \<Sigma> G {}) (book_conj_encode (book_const_subst c \<sigma> B A))"
    by (simp only: book_conj_encoded_empty book_conj_encode_const_subst;
      rule book_theory_to_printed[OF rich target_result])
  show ?thesis by (rule iffD2[OF book_conj_theory_encoding_iff printed_result])
qed

corollary book_conj_theory_printed_constant_substitution:
  assumes rich: "sg_rich G" and derivation: "book_conj_theory_derivable \<Sigma> G {} A"
    and replacement: "book_in_language book_conj_logical_type UNIV \<Sigma> G B \<sigma>"
    and free_for: "book_printed_free_for B x A"
  shows "book_conj_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> B A)"
  by (rule book_conj_theory_constant_substitution[
    OF rich derivation replacement book_printed_free_for_constant[OF free_for]])

end
