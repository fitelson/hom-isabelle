theory Goodman_H_Quantifier_Certificates
  imports Goodman_H_Certificate_Interface
begin

section \<open>Book-H existential introduction and the Inst rule\<close>

theorem gi_book_H_EG:
  fixes \<Sigma> :: "'c ssignature" and F a :: "'c book_named_term"
  assumes rich: "sg_rich G"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma>"
  shows "book_H \<Sigma> G (book_imp (NApp F a) (NApp (book_exists_const G \<sigma>) F))"
proof -
  have fal: "book_theory_formula \<Sigma> G (NApp F a)" by (rule book_language_App[OF fl al])
  have el: "book_theory_formula \<Sigma> G (NApp (book_exists_const G \<sigma>) F)"
    by (rule book_exists_application_language[OF rich fl])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_imp_language[OF fal el]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    have member: "J g a \<in> D \<sigma>" by (rule M.denote_type[OF UNIV_I al typed])
    show "V (J g (book_imp (NApp F a) (NApp (book_exists_const G \<sigma>) F)))"
      by (simp only: M.book_imp_truth[OF typed fal el] M.book_exists_application_truth[OF rich typed fl]
        M.denote_app[OF UNIV_I UNIV_I UNIV_I fl al typed]; use member in blast)
  qed
qed

theorem gi_book_H_Inst:
  fixes \<Sigma> :: "'c ssignature" and P Q :: "'c book_named_term"
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
    and ql: "book_theory_formula \<Sigma> G Q" and fresh: "n \<notin> named_fv Q"
    and premise: "book_H \<Sigma> G (book_imp P Q)"
  shows "book_H \<Sigma> G (book_imp (book_exists G n P) Q)"
proof -
  have el: "book_theory_formula \<Sigma> G (book_exists G n P)" by (rule book_exists_language[OF rich pl])
  have il: "book_theory_formula \<Sigma> G (book_imp P Q)" by (rule book_imp_language[OF pl ql])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_imp_language[OF el ql]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    have valid: "book_formula_valid D G J V (book_imp P Q)"
      by (rule M.book_H_soundness[OF rich premise])
    show "V (J g (book_imp (book_exists G n P) Q))"
    proof (simp only: M.book_imp_truth[OF typed el ql] M.book_exists_truth[OF rich typed pl]; rule impI)
      assume exists: "\<exists>a\<in>D (G n). V (J (g(n := a)) P)"
      then obtain a where am: "a \<in> D (G n)" and pa: "V (J (g(n := a)) P)" by blast
      have updated: "book_env_typed D G (g(n := a))" by (rule book_env_update[OF typed am])
      have implication: "V (J (g(n := a)) (book_imp P Q))"
        using valid updated unfolding book_formula_valid_def by blast
      have qa: "V (J (g(n := a)) Q)"
        using implication pa by (simp only: M.book_imp_truth[OF updated pl ql]; blast)
      have local: "J (g(n := a)) Q = J g Q"
        by (rule M.book_denote_locality[OF UNIV_I ql updated typed]; use fresh in auto)
      show "V (J g Q)" using qa by (simp only: local)
    qed
  qed
qed

lemma gi_alpha_imp_left:
  "named_alpha G A B \<Longrightarrow> named_alpha G (book_imp A C) (book_imp B C)"
  unfolding book_imp_def by (intro named_alpha.App named_alpha.Refl; assumption)

lemma gi_alpha_imp_right:
  "named_alpha G A B \<Longrightarrow> named_alpha G (book_imp C A) (book_imp C B)"
  unfolding book_imp_def by (intro named_alpha.App named_alpha.Refl; assumption)

text \<open>
  Inst uses soundness and completeness of H with a fresh-name condition
  proved at the point of use. It is a theorem-level rule, not unrestricted
  existential elimination from arbitrary local assumptions.
\<close>

end
