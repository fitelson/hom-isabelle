theory Bacon_Book_Canonical_Biconditional
  imports Bacon_Book_Classicism_Boxed_PE Bacon_Book_Modal_Term_Action
begin

lemma book_H_biconditional_rules:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_H \<Sigma> G (book_imp (book_iff G P Q) (book_imp P Q))"
    and "book_H \<Sigma> G (book_imp (book_iff G P Q) (book_imp Q P))"
    and "book_H \<Sigma> G (book_imp (book_imp P Q) (book_imp (book_imp Q P) (book_iff G P Q)))"
proof -
  let ?I = "book_iff G P Q"
  let ?F = "book_imp P Q"
  let ?R = "book_imp Q P"
  have il: "book_theory_formula \<Sigma> G ?I" by (rule book_iff_language[OF rich pl ql])
  have fl: "book_theory_formula \<Sigma> G ?F" by (rule book_imp_language[OF pl ql])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_imp_language[OF ql pl])
  have tail: "book_theory_formula \<Sigma> G (book_imp ?R ?I)" by (rule book_imp_language[OF rl il])
  have clauses_typed: "book_theory_formula \<Sigma> G A"
    if "A \<in> {book_imp ?I ?F, book_imp ?I ?R, book_imp ?F (book_imp ?R ?I)}" for A
    using that book_imp_language[OF il fl] book_imp_language[OF il rl] book_imp_language[OF fl tail] by blast
  have clauses: "book_H \<Sigma> G A"
    if member: "A \<in> {book_imp ?I ?F, book_imp ?I ?R, book_imp ?F (book_imp ?R ?I)}" for A
  proof (rule book_H_from_pointwise_models[OF rich clauses_typed[OF member]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "V (J g A)" using member
      by (auto simp only: insert_iff singleton_iff M.book_imp_truth[OF typed il fl]
        M.book_imp_truth[OF typed il rl] M.book_imp_truth[OF typed fl tail] M.book_imp_truth[OF typed rl il]
        M.book_imp_truth[OF typed pl ql] M.book_imp_truth[OF typed ql pl] M.book_iff_truth[OF rich typed pl ql])
  qed
  show "book_H \<Sigma> G (book_imp ?I ?F)" by (rule clauses; blast)
  show "book_H \<Sigma> G (book_imp ?I ?R)" by (rule clauses; blast)
  show "book_H \<Sigma> G (book_imp ?F (book_imp ?R ?I))" by (rule clauses; blast)
qed

context book_C_identity_world
begin

theorem member_biconditional_iff:
  assumes pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
    and pc: "named_fv P = {}" and qc: "named_fv Q = {}"
  shows "book_iff G P Q \<in> w \<longleftrightarrow> (P \<in> w \<longleftrightarrow> Q \<in> w)"
proof -
  let ?I = "book_iff G P Q"
  let ?F = "book_imp P Q"
  let ?R = "book_imp Q P"
  have il: "book_theory_formula \<Sigma> G ?I" by (rule book_iff_language[OF rich pl ql])
  have fl: "book_theory_formula \<Sigma> G ?F" by (rule book_imp_language[OF pl ql])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_imp_language[OF ql pl])
  have tl: "book_theory_formula \<Sigma> G (book_imp ?R ?I)" by (rule book_imp_language[OF rl il])
  have ic: "named_fv ?I = {}" by (simp add: book_iff_fv pc qc)
  have fc: "named_fv ?F = {}" by (simp only: book_imp_fv pc qc Un_empty)
  have rc: "named_fv ?R = {}" by (simp only: book_imp_fv pc qc Un_empty)
  have tc: "named_fv (book_imp ?R ?I) = {}" by (simp add: book_imp_fv book_iff_fv pc qc)
  have first: "book_imp ?I ?F \<in> w"
    by (rule book_C_closed_maximal_original_theorem[OF rich maximal book_C_proves.H[
      OF book_H_biconditional_rules(1)[OF rich pl ql]]]; simp add: book_imp_fv book_iff_fv pc qc)
  have second: "book_imp ?I ?R \<in> w"
    by (rule book_C_closed_maximal_original_theorem[OF rich maximal book_C_proves.H[
      OF book_H_biconditional_rules(2)[OF rich pl ql]]]; simp add: book_imp_fv book_iff_fv pc qc)
  have third: "book_imp ?F (book_imp ?R ?I) \<in> w"
    by (rule book_C_closed_maximal_original_theorem[OF rich maximal book_C_proves.H[
      OF book_H_biconditional_rules(3)[OF rich pl ql]]]; simp add: book_imp_fv book_iff_fv pc qc)
  have Hmax: "book_closed_maximal_extension \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> {}) w"
    using maximal unfolding book_C_closed_maximal_extension_def .
  have law1: "?I \<in> w \<longrightarrow> (P \<in> w \<longrightarrow> Q \<in> w)"
    using first by (simp only: book_closed_maximal_implication_iff[OF rich Hmax il fl ic fc]
      book_closed_maximal_implication_iff[OF rich Hmax pl ql pc qc]; blast)
  have law2: "?I \<in> w \<longrightarrow> (Q \<in> w \<longrightarrow> P \<in> w)"
    using second by (simp only: book_closed_maximal_implication_iff[OF rich Hmax il rl ic rc]
      book_closed_maximal_implication_iff[OF rich Hmax ql pl qc pc]; blast)
  have law3: "(P \<in> w \<longrightarrow> Q \<in> w) \<longrightarrow> (Q \<in> w \<longrightarrow> P \<in> w) \<longrightarrow> ?I \<in> w"
    using third by (simp only: book_closed_maximal_implication_iff[OF rich Hmax fl tl fc tc]
      book_closed_maximal_implication_iff[OF rich Hmax rl il rc ic]
      book_closed_maximal_implication_iff[OF rich Hmax pl ql pc qc]
      book_closed_maximal_implication_iff[OF rich Hmax ql pl qc pc]; blast)
  show ?thesis using law1 law2 law3 by blast
qed

end

text \<open>
  The literal λ-defined biconditional has its Boolean membership clause
  in a closed C world. This uses three H tautologies and the independently
  proved implication membership clause. It does not assume a semantic
  interpretation or identify a formula with a convenient β reduct.
\<close>

end
