theory Bacon_Book_Classicism_Normal_K
  imports Bacon_Book_H_Normal_K_Certificate Bacon_Book_Classicism_Necessitation
begin

section \<open>The C identity that completes the K calculation\<close>

theorem book_H_top_imp_iff:
  assumes rich: "sg_rich G" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_H \<Sigma> G (book_iff G (book_imp (book_top G) Q) Q)"
proof -
  have tl: "book_theory_formula \<Sigma> G (book_top G)" by (rule book_top_language[OF rich])
  have il: "book_theory_formula \<Sigma> G (book_imp (book_top G) Q)" by (rule book_imp_language[OF tl ql])
  have result_type: "book_theory_formula \<Sigma> G (book_iff G (book_imp (book_top G) Q) Q)"
    by (rule book_iff_language[OF rich il ql])
  show ?thesis unfolding book_H_canonical_completeness[OF rich result_type]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_iff G (book_imp (book_top G) Q) Q)"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      show "V (J g (book_iff G (book_imp (book_top G) Q) Q))"
        by (simp only: M.book_iff_truth[OF rich typed il ql] M.book_imp_truth[OF typed tl ql]
          M.book_top_true[OF rich typed]; simp)
    qed
  qed
qed

theorem book_C_normal_K:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_C_proves \<Sigma> G (book_K_formula G P Q)"
proof -
  have il: "book_theory_formula \<Sigma> G (book_imp (book_top G) Q)"
    by (rule book_imp_language[OF book_top_language[OF rich] ql])
  have iff_proof: "book_C_proves \<Sigma> G (book_iff G (book_imp (book_top G) Q) Q)"
    by (rule book_C_proves.H[OF book_H_top_imp_iff[OF rich ql]])
  have identity: "book_C_proves \<Sigma> G (book_leibniz G Prop (book_imp (book_top G) Q) Q)"
    by (rule book_C_propositional_equivalence[OF il ql iff_proof])
  have conditional: "book_C_proves \<Sigma> G (book_imp
      (book_leibniz G Prop (book_imp (book_top G) Q) Q) (book_K_formula G P Q))"
    by (rule book_C_proves.H[OF book_H_normal_K_conditional[OF rich pl ql]])
  show ?thesis by (rule book_C_proves.MP[OF identity conditional book_K_language[OF rich pl ql]])
qed

text \<open>
  C proves □(P→Q)→(□P→□Q). H first proves (⊤→Q)↔Q.
  Propositional Equivalence in C supplies the identity (⊤→Q)=Q,
  and the independently checked H conditional finishes the proof.
  This derives K in the book's own language and calculus, not by
  importing the paper's R-language theorem. H completeness is used
  solely to obtain H certificates, never C completeness.
\<close>

end
