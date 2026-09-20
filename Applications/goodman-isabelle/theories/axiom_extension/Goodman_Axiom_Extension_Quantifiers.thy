theory Goodman_Axiom_Extension_Quantifiers
  imports Goodman_Closed_Axiom_Transport
begin

section \<open>Existential elimination above the added axioms\<close>

theorem gi_H_quantified_Inst_certificate:
  fixes \<Sigma> :: "'c ssignature" and P Q :: "'c book_named_term"
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
    and ql: "book_theory_formula \<Sigma> G Q" and fresh: "n \<notin> named_fv Q"
  shows "book_H \<Sigma> G
    (book_imp (book_all G n (book_imp P Q)) (book_imp (book_exists G n P) Q))"
proof -
  have il: "book_theory_formula \<Sigma> G (book_imp P Q)" by (rule book_imp_language[OF pl ql])
  have all: "book_theory_formula \<Sigma> G (book_all G n (book_imp P Q))" by (rule book_all_language[OF il])
  have ex: "book_theory_formula \<Sigma> G (book_exists G n P)" by (rule book_exists_language[OF rich pl])
  have tail: "book_theory_formula \<Sigma> G (book_imp (book_exists G n P) Q)" by (rule book_imp_language[OF ex ql])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_imp_language[OF all tail]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    show "V (J g (book_imp (book_all G n (book_imp P Q)) (book_imp (book_exists G n P) Q)))"
    proof (simp only: M.book_imp_truth[OF typed all tail] M.book_imp_truth[OF typed ex ql]
        M.book_all_truth[OF typed il] M.book_exists_truth[OF rich typed pl]; intro impI)
      assume universal: "\<forall>a\<in>D (G n). V (J (g(n := a)) (book_imp P Q))"
        and witness: "\<exists>a\<in>D (G n). V (J (g(n := a)) P)"
      then obtain a where am: "a \<in> D (G n)" and pa: "V (J (g(n := a)) P)" by blast
      have updated: "book_env_typed D G (g(n := a))" by (rule book_env_update[OF typed am])
      have implication: "V (J (g(n := a)) (book_imp P Q))" using universal am by blast
      have qa: "V (J (g(n := a)) Q)" using implication pa
        by (simp only: M.book_imp_truth[OF updated pl ql]; blast)
      have local: "J (g(n := a)) Q = J g Q"
        by (rule M.book_denote_locality[OF UNIV_I ql updated typed]; use fresh in auto)
      show "V (J g Q)" using qa by (simp only: local)
    qed
  qed
qed

theorem gi_goodman_Inst:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
    and ql: "book_theory_formula \<Sigma> G Q" and fresh: "n \<notin> named_fv Q"
    and premise: "goodman_book_proves \<Sigma> G T (book_imp P Q)"
  shows "goodman_book_proves \<Sigma> G T (book_imp (book_exists G n P) Q)"
proof -
  have quantified: "goodman_book_proves \<Sigma> G T (book_all G n (book_imp P Q))"
    by (rule gi_goodman_generalize[OF rich premise])
  have certificate: "goodman_book_proves \<Sigma> G T
    (book_imp (book_all G n (book_imp P Q)) (book_imp (book_exists G n P) Q))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule gi_H_quantified_Inst_certificate[OF rich pl ql fresh])
  show ?thesis by (rule goodman_book_proves.MP[OF quantified certificate
    book_imp_language[OF book_exists_language[OF rich pl] ql]])
qed

lemma gi_goodman_alpha_transport:
  assumes rich: "sg_rich G" and alpha: "named_alpha G A B"
    and derivation: "goodman_book_proves \<Sigma> G T A"
  shows "goodman_book_proves \<Sigma> G T B"
proof -
  have language: "named_in_language book_minimal_logical_type \<Sigma> G A Prop"
    using goodman_book_proves_language[OF rich derivation] by (simp only: book_language_UNIV)
  have conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
    by (rule named_alpha_implies_beta_eta[OF alpha language])
  show ?thesis by (rule gi_goodman_conversion_transport[OF rich conversion derivation])
qed

text \<open>
  Inst is derived from a fixed H theorem and theorem-level generalization
  within C+[T]. We never apply H soundness to a premise proved using T.
  This avoids silently assuming that the added axioms are H theorems or
  globally valid in all H models.
\<close>

end
