theory Bacon_Book_Proposition_Identity_Membership
  imports Bacon_Book_Canonical_Biconditional
begin

lemma book_H_proposition_identity_implies_iff:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G Prop P Q) (book_iff G P Q))"
proof (rule book_H_from_pointwise_models[OF rich book_imp_language[
  OF book_leibniz_language[OF rich pl ql] book_iff_language[OF rich pl ql]]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
  assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
  have calculation: "book_leibniz_equiv D app V Prop (J g P) (J g Q) \<longrightarrow> V (J g P) = V (J g Q)"
    by (intro impI; rule M.book_minimal_leibniz_valuation; assumption)
  show "V (J g (book_imp (book_leibniz G Prop P Q) (book_iff G P Q)))"
    by (simp only: M.book_imp_truth[OF typed book_leibniz_language[OF rich pl ql] book_iff_language[OF rich pl ql]]
      M.book_leibniz_truth[OF rich typed pl ql] M.book_iff_truth[OF rich typed pl ql]; rule calculation)
qed

context book_C_identity_world
begin

lemma proposition_identity_membership:
  assumes pm: "P \<in> book_closed_terms \<Sigma> G Prop" and qm: "Q \<in> book_closed_terms \<Sigma> G Prop"
    and identity: "book_leibniz G Prop P Q \<in> w"
  shows "P \<in> w \<longleftrightarrow> Q \<in> w"
proof -
  have pl: "book_theory_formula \<Sigma> G P" by (rule book_closed_terms_language[OF pm])
  have ql: "book_theory_formula \<Sigma> G Q" by (rule book_closed_terms_language[OF qm])
  have pc: "named_fv P = {}" by (rule book_closed_terms_closed[OF pm])
  have qc: "named_fv Q = {}" by (rule book_closed_terms_closed[OF qm])
  have closed: "named_fv (book_iff G P Q) = {}" by (simp add: book_iff_fv pc qc)
  have member: "book_iff G P Q \<in> w" by (rule apply_H[OF book_H_proposition_identity_implies_iff[OF rich pl ql] identity closed])
  show ?thesis using member by (simp only: member_biconditional_iff[OF pl ql pc qc])
qed

end

end
