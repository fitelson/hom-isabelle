theory Bacon_Book_Conjunction_Variable_Substitution
  imports Bacon_Book_Conjunction_Proof_Correspondence
    Bacon_Book_Conjunction_Constant_Substitution_Transport Bacon_Book_Theory_Variable_Substitution
begin

section \<open>Global theory substitution preserves the fixed background\<close>

text \<open>
  If S⊢∧A and N:G(x) is free for x in A, then S⊢∧A[N/x].
  Encode the proof over enc(S)∪Π∧, apply the already derived minimal
  GLOBAL-theory variable-substitution theorem under those unchanged
  premises, and reflect. The substitution does not change Π∧ or S.
  Source: the Chapter 5 global theory rules and Definition 5.2, p.99.

  This is not a local-assumption substitution rule. An open premise
  expresses truth at every assignment. The exact-capture test is allowed
  by the proved printed-calculus correspondence; the printed-test
  specialization is stated separately below.
\<close>

theorem book_conj_theory_variable_substitution:
  assumes rich: "sg_rich G"
    and derivation: "book_conj_theory_derivable \<Sigma> G S A"
    and replacement: "book_in_language book_conj_logical_type UNIV \<Sigma> G B (G x)"
    and free_for: "named_free_for B x A"
  shows "book_conj_theory_derivable \<Sigma> G S (named_subst x B A)"
proof -
  let ?T = "book_conj_encoded_premises \<Sigma> G S"
  let ?target = "book_conj_target_signature \<Sigma>"
  have printed: "book_printed_theory_derivable ?target G ?T (book_conj_encode A)"
    by (rule book_conj_theory_encode[OF derivation])
  have encoded: "book_theory_derivable ?target G ?T (book_conj_encode A)"
    by (rule book_printed_theory_to_theory[OF printed])
  have bl: "book_in_language book_minimal_logical_type UNIV ?target G (book_conj_encode B) (G x)"
    by (rule book_conj_encode_language[OF replacement])
  have permitted: "named_free_for (book_conj_encode B) x (book_conj_encode A)"
    by (rule iffD2[OF book_conj_encode_named_free_for free_for])
  have instantiated: "book_theory_derivable ?target G ?T
    (named_subst x (book_conj_encode B) (book_conj_encode A))"
    by (rule book_theory_variable_substitution[OF rich encoded bl permitted])
  have target_result: "book_printed_theory_derivable ?target G ?T (book_conj_encode (named_subst x B A))"
    by (simp only: book_conj_encode_subst; rule book_theory_to_printed[OF rich instantiated])
  show ?thesis by (rule iffD2[OF book_conj_theory_encoding_iff target_result])
qed

corollary book_conj_theory_printed_variable_substitution:
  assumes rich: "sg_rich G" and derivation: "book_conj_theory_derivable \<Sigma> G S A"
    and replacement: "book_in_language book_conj_logical_type UNIV \<Sigma> G B (G x)"
    and free_for: "book_printed_free_for B x A"
  shows "book_conj_theory_derivable \<Sigma> G S (named_subst x B A)"
  by (rule book_conj_theory_variable_substitution[
    OF rich derivation replacement book_printed_free_for_named[OF free_for]])

end
