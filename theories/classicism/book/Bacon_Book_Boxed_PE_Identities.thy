theory Bacon_Book_Boxed_PE_Identities
  imports Bacon_Book_H_Identity_Certificates
begin

section \<open>Three original C identities for boxed propositional equivalence\<close>

definition book_boxed_PE_premises where
  "book_boxed_PE_premises G P Q = {
    book_leibniz G Prop (book_imp (book_iff G P Q) P) (book_imp (book_iff G P Q) Q),
    book_leibniz G Prop (book_imp (book_top G) P) P,
    book_leibniz G Prop (book_imp (book_top G) Q) Q}"

lemma book_boxed_PE_premises_language:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
    and member: "A \<in> book_boxed_PE_premises G P Q"
  shows "book_theory_formula \<Sigma> G A"
  using member unfolding book_boxed_PE_premises_def
  by (auto intro: book_leibniz_language[OF rich] book_imp_language book_iff_language[OF rich] book_top_language[OF rich] pl ql)

lemma book_H_iff_antecedent_implications:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_H \<Sigma> G (book_iff G (book_imp (book_iff G P Q) P) (book_imp (book_iff G P Q) Q))"
proof -
  let ?E = "book_iff G P Q"
  have el: "book_theory_formula \<Sigma> G ?E" by (rule book_iff_language[OF rich pl ql])
  have left: "book_theory_formula \<Sigma> G (book_imp ?E P)" by (rule book_imp_language[OF el pl])
  have right: "book_theory_formula \<Sigma> G (book_imp ?E Q)" by (rule book_imp_language[OF el ql])
  show ?thesis
  proof (rule book_H_from_pointwise_models[OF rich book_iff_language[OF rich left right]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "V (J g (book_iff G (book_imp ?E P) (book_imp ?E Q)))"
      by (simp only: M.book_iff_truth[OF rich typed left right] M.book_imp_truth[OF typed el pl]
        M.book_imp_truth[OF typed el ql] M.book_iff_truth[OF rich typed pl ql]; blast)
  qed
qed

lemma book_C_top_imp_identity:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
  shows "book_C_proves \<Sigma> G (book_leibniz G Prop (book_imp (book_top G) P) P)"
  by (rule book_C_propositional_equivalence[OF book_imp_language[OF book_top_language[OF rich] pl] pl
    book_C_proves.H[OF book_H_top_imp_iff[OF rich pl]]])

theorem book_C_boxed_PE_premises:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
    and member: "A \<in> book_boxed_PE_premises G P Q"
  shows "book_C_proves \<Sigma> G A"
proof -
  have el: "book_theory_formula \<Sigma> G (book_iff G P Q)" by (rule book_iff_language[OF rich pl ql])
  have common: "book_C_proves \<Sigma> G
    (book_leibniz G Prop (book_imp (book_iff G P Q) P) (book_imp (book_iff G P Q) Q))"
    by (rule book_C_propositional_equivalence[OF book_imp_language[OF el pl] book_imp_language[OF el ql]
      book_C_proves.H[OF book_H_iff_antecedent_implications[OF rich pl ql]]])
  show ?thesis using member common book_C_top_imp_identity[OF rich pl] book_C_top_imp_identity[OF rich ql]
    unfolding book_boxed_PE_premises_def by blast
qed

text \<open>
  Put E=(P↔Q). H proves (E→P)↔(E→Q), (⊤→P)↔P and (⊤→Q)↔Q.
  Propositional Equivalence gives the corresponding three identities
  in C. The displayed premise set is an auxiliary finite set of proved
  C theorems, not a new axiom stock or a model requirement.
\<close>

end
