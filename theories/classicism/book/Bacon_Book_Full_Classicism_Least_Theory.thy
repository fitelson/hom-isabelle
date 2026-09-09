theory Bacon_Book_Full_Classicism_Least_Theory
  imports Bacon_Book_Full_Classicism_Calculus
begin

definition book_full_classicist_theory where
  "book_full_classicist_theory \<Sigma> G T \<longleftrightarrow>
    book_higher_order_theory \<Sigma> G T \<and>
    (\<forall>\<sigma> \<tau>. book_MF_axiom G \<sigma> \<tau> \<in> T) \<and>
    (\<forall>P Q. book_theory_formula \<Sigma> G P \<longrightarrow> book_theory_formula \<Sigma> G Q \<longrightarrow>
      book_iff G P Q \<in> T \<longrightarrow> book_leibniz G Prop P Q \<in> T)"

definition book_full_C where
  "book_full_C \<Sigma> G A \<longleftrightarrow> book_theory_formula \<Sigma> G A \<and>
    (\<forall>T. book_full_classicist_theory \<Sigma> G T \<longrightarrow> A \<in> T)"

theorem book_full_C_proofs_form_theory:
  assumes rich: "sg_rich G"
  shows "book_full_classicist_theory \<Sigma> G {A. book_full_C_proves \<Sigma> G A}"
proof (unfold book_full_classicist_theory_def, intro conjI)
  show "book_higher_order_theory \<Sigma> G {A. book_full_C_proves \<Sigma> G A}"
    unfolding book_higher_order_theory_def
    using book_full_C_proves_language[OF rich] book_full_C_contains_theory_derivation[OF rich] by blast
  show "\<forall>\<sigma> \<tau>. book_MF_axiom G \<sigma> \<tau> \<in> {A. book_full_C_proves \<Sigma> G A}"
    by (intro allI; simp only: mem_Collect_eq; rule book_full_C_proves.MF)
  show "\<forall>P Q. book_theory_formula \<Sigma> G P \<longrightarrow> book_theory_formula \<Sigma> G Q \<longrightarrow>
    book_iff G P Q \<in> {A. book_full_C_proves \<Sigma> G A} \<longrightarrow>
    book_leibniz G Prop P Q \<in> {A. book_full_C_proves \<Sigma> G A}"
    by (intro allI impI; simp only: mem_Collect_eq; rule book_full_C_proves.PE; assumption)
qed

theorem book_full_classicist_theory_contains_proof:
  assumes rich: "sg_rich G" and target: "book_full_classicist_theory \<Sigma> G T"
    and derivation: "book_full_C_proves \<Sigma> G A"
  shows "A \<in> T"
proof -
  have theory_ok: "book_higher_order_theory \<Sigma> G T"
    and mf: "\<forall>\<sigma> \<tau>. book_MF_axiom G \<sigma> \<tau> \<in> T"
    and pe: "\<forall>P Q. book_theory_formula \<Sigma> G P \<longrightarrow> book_theory_formula \<Sigma> G Q \<longrightarrow>
      book_iff G P Q \<in> T \<longrightarrow> book_leibniz G Prop P Q \<in> T"
    using target unfolding book_full_classicist_theory_def by blast+
  have rules: "book_theory_rules \<Sigma> G T" using theory_ok book_higher_order_theory_iff_rules by blast
  show ?thesis using derivation
  proof (induction rule: book_full_C_proves.induct)
    case (H A)
    have proof_H: "book_theory_derivable \<Sigma> G {} A" using H.hyps by (simp only: book_H_iff_theory[OF rich])
    show ?case by (rule book_theory_contains_derivation[OF theory_ok proof_H empty_subsetI])
  next
    case MF
    show ?case using mf by blast
  next
    case MP
    show ?case using rules MP.IH unfolding book_theory_rules_def by blast
  next
    case Gen
    show ?case using rules Gen.IH Gen.hyps(4) unfolding book_theory_rules_def by blast
  next
    case PE
    show ?case using pe PE.IH PE.hyps(2,3) by blast
  qed
qed

theorem book_full_C_iff_proves:
  assumes rich: "sg_rich G"
  shows "book_full_C \<Sigma> G A \<longleftrightarrow> book_full_C_proves \<Sigma> G A"
proof
  assume least: "book_full_C \<Sigma> G A"
  show "book_full_C_proves \<Sigma> G A"
    using least book_full_C_proofs_form_theory[OF rich, where \<Sigma>=\<Sigma>] unfolding book_full_C_def by blast
next
  assume derivation: "book_full_C_proves \<Sigma> G A"
  have language: "book_theory_formula \<Sigma> G A" by (rule book_full_C_proves_language[OF rich derivation])
  show "book_full_C \<Sigma> G A" unfolding book_full_C_def
    by (rule conjI[OF language], intro allI impI; rule book_full_classicist_theory_contains_proof[OF rich _ derivation]; assumption)
qed

text \<open>
  The finite H/MF/MP/Gen/PE calculus equals the independently defined
  least higher-order theory containing all MFστ and closed under PE.
  This is a presentation theorem for the full-type specification in
  §8.1, endnote 5, not a semantic completeness theorem. No model,
  consistency, old-base inclusion or vector-Equivalence admissibility
  is assumed in this identification.
\<close>

end
