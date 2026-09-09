theory Bacon_Book_Classicism_Identity_Stability
  imports Bacon_Book_Identity_Stability_Truth Bacon_Book_Canonical_Language_Inclusion
begin

theorem book_H_identity_stability_conditional:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
  shows "book_H \<Sigma> G (book_imp (book_box G (book_leibniz G \<sigma> A A))
    (book_imp (book_leibniz G \<sigma> A B) (book_box G (book_leibniz G \<sigma> A B))))"
proof -
  let ?N = "book_box G (book_leibniz G \<sigma> A A)"
  let ?E = "book_leibniz G \<sigma> A B"
  let ?BE = "book_box G ?E"
  have nl: "book_theory_formula \<Sigma> G ?N" by (rule book_box_language[OF rich book_leibniz_language[OF rich al al]])
  have el: "book_theory_formula \<Sigma> G ?E" by (rule book_leibniz_language[OF rich al bl])
  have bel: "book_theory_formula \<Sigma> G ?BE" by (rule book_box_language[OF rich el])
  have tail: "book_theory_formula \<Sigma> G (book_imp ?E ?BE)" by (rule book_imp_language[OF el bel])
  have whole: "book_theory_formula \<Sigma> G (book_imp ?N (book_imp ?E ?BE))" by (rule book_imp_language[OF nl tail])
  show ?thesis unfolding book_H_canonical_completeness[OF rich whole]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>C\<in>{}. book_formula_valid D G J V C"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp ?N (book_imp ?E ?BE))"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      have calculation: "V (J g ?N) \<longrightarrow> V (J g ?E) \<longrightarrow> V (J g ?BE)"
        by (intro impI; rule M.book_identity_stability_conditional_truth[OF rich typed al bl]; assumption)
      show "V (J g (book_imp ?N (book_imp ?E ?BE)))"
        by (simp only: M.book_imp_truth[OF typed nl tail] M.book_imp_truth[OF typed el bel]; rule calculation)
    qed
  qed
qed

theorem book_C_identity_stability:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
  shows "book_C_proves \<Sigma> G (book_imp (book_leibniz G \<sigma> A B) (book_box G (book_leibniz G \<sigma> A B)))"
proof -
  have reflexive: "book_C_proves \<Sigma> G (book_leibniz G \<sigma> A A)"
    by (rule book_C_proves.H[OF book_H_leibniz_reflexive[OF rich al]])
  have necessary: "book_C_proves \<Sigma> G (book_box G (book_leibniz G \<sigma> A A))"
    by (rule book_C_necessitation[OF rich reflexive])
  have conditional: "book_C_proves \<Sigma> G (book_imp (book_box G (book_leibniz G \<sigma> A A))
    (book_imp (book_leibniz G \<sigma> A B) (book_box G (book_leibniz G \<sigma> A B))))"
    by (rule book_C_proves.H[OF book_H_identity_stability_conditional[OF rich al bl]])
  have el: "book_theory_formula \<Sigma> G (book_leibniz G \<sigma> A B)" by (rule book_leibniz_language[OF rich al bl])
  show ?thesis by (rule book_C_proves.MP[OF necessary conditional book_imp_language[OF el book_box_language[OF rich el]]])
qed

text \<open>
  C ⊢ (A=σB) → □(A=σB), for every type σ and typed A,B (open or closed).
  Only the original H theorem A=σA is necessitated. The conditional
  bridge is an H certificate, obtained from independently verified H
  completeness. This supplies the identity-persistence step on p.399
  without adding Necessitation to a world's local consequence relation.
\<close>

end
