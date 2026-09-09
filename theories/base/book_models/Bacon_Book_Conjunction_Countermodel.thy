theory Bacon_Book_Conjunction_Countermodel
  imports Bacon_Book_Conjunction_Model_Existence
begin

section \<open>Countermodels reflect through the fixed-background encoding\<close>

text \<open>
  If S does not derive A in the native conjunction calculus, the proof
  correspondence makes enc(A) unprovable from enc(S)∪Π∧. The minimal
  countermodel globally satisfies that fixed theory and has a typed
  assignment falsifying enc(A). The actual richer-model construction
  keeps the same values and assignment, so it falsifies A itself.
  Source: the completeness route of Corollary 15.2, p.321, applied to
  the primitive conjunction extension of §5.2, p.104.

  No closedness or finiteness assumption on S or A is introduced.
  For open A the conclusion is an actual falsifying assignment, not
  global truth of its negation. No native-model existence premise is used.
\<close>

lemma book_conj_encoded_valid_iff:
  "book_formula_valid D G (book_conj_encoded_denote J) V A \<longleftrightarrow>
    book_formula_valid D G J V (book_conj_encode A)"
  by (simp only: book_formula_valid_def book_conj_encoded_denote_def)

theorem book_conj_canonical_countermodel:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G B"
    and al: "book_conj_formula \<Sigma> G A"
    and nonderivable: "\<not> book_conj_theory_derivable \<Sigma> G S A"
  shows "\<exists>(D::otype \<Rightarrow> 'c book_conj_canonical_value set) app J V k.
    book_conjunction_model D app \<Sigma> G J V k \<and>
    (\<forall>B\<in>S. book_formula_valid D G J V B) \<and>
    \<not> book_formula_valid D G J V A \<and>
    (\<exists>g. book_env_typed D G g \<and> \<not> V (J g A))"
proof -
  let ?T = "book_conj_encoded_premises \<Sigma> G S"
  let ?target = "book_conj_target_signature \<Sigma>"
  have target_language: "book_printed_theory_formula ?target G B" if "B \<in> ?T" for B
    by (rule book_conj_encoded_premises_language[OF language that])
  have encoded_language: "book_printed_theory_formula ?target G (book_conj_encode A)"
    by (rule book_conj_encode_language[OF al])
  have target_nonderivable: "\<not> book_printed_theory_derivable ?target G ?T (book_conj_encode A)"
  proof
    assume target_derivation: "book_printed_theory_derivable ?target G ?T (book_conj_encode A)"
    have original_derivation: "book_conj_theory_derivable \<Sigma> G S A"
      by (rule iffD2[OF book_conj_theory_encoding_iff target_derivation])
    show False by (rule notE[OF nonderivable original_derivation])
  qed
  obtain D :: "otype \<Rightarrow> 'c book_conj_canonical_value set" and app J V k where
    target_model: "book_full_minimal_model D app ?target G J V k"
    and target_truth: "\<forall>B\<in>?T. book_formula_valid D G J V B"
    and target_failure: "\<not> book_formula_valid D G J V (book_conj_encode A)"
    and witness: "\<exists>g. book_env_typed D G g \<and> \<not> V (J g (book_conj_encode A))"
    using book_printed_canonical_countermodel[OF rich target_language encoded_language target_nonderivable] by blast
  have background: "\<forall>B\<in>book_conj_axioms \<Sigma> G. book_formula_valid D G J V B"
    using target_truth unfolding book_conj_encoded_premises_def by blast
  obtain k' where native: "book_conjunction_model D app \<Sigma> G (book_conj_encoded_denote J) V k'"
    using book_conj_model_from_background[OF target_model rich background] by blast
  have original_truth: "\<forall>B\<in>S. book_formula_valid D G (book_conj_encoded_denote J) V B"
    using target_truth unfolding book_conj_encoded_premises_def
    by (simp only: book_conj_encoded_valid_iff; blast)
  have failure: "\<not> book_formula_valid D G (book_conj_encoded_denote J) V A"
  proof
    assume valid: "book_formula_valid D G (book_conj_encoded_denote J) V A"
    have encoded_valid: "book_formula_valid D G J V (book_conj_encode A)"
      by (rule iffD1[OF book_conj_encoded_valid_iff valid])
    show False by (rule notE[OF target_failure encoded_valid])
  qed
  have counterassignment: "\<exists>g. book_env_typed D G g \<and> \<not> V (book_conj_encoded_denote J g A)"
    using witness by (simp only: book_conj_encoded_denote_def)
  show ?thesis by (rule exI[where x=D], rule exI[where x=app],
    rule exI[where x="book_conj_encoded_denote J"], rule exI[where x=V], rule exI[where x="k'"],
    rule conjI[OF native conjI[OF original_truth conjI[OF failure counterassignment]]])
qed

end
