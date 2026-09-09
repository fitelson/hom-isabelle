theory Bacon_Book_H_Identity_Certificates
  imports Bacon_Book_Canonical_Identity_Persistence
begin

section \<open>H certificates for the identity-class algebra\<close>

lemma book_H_from_pointwise_models:
  fixes A :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and valid: "\<And>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k g.
      book_full_minimal_model D app \<Sigma> G J V k \<Longrightarrow> book_env_typed D G g \<Longrightarrow> V (J g A)"
  shows "book_H \<Sigma> G A"
proof (unfold book_H_canonical_completeness[OF rich al] book_canonical_consequence_def, intro allI impI)
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
  assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
  show "book_formula_valid D G J V A" by (rule book_formula_validI; rule valid[OF model]; assumption)
qed

theorem book_H_identity_symmetry:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G \<sigma> A B) (book_leibniz G \<sigma> B A))"
proof -
  let ?E = "book_leibniz G \<sigma> A B"
  let ?F = "book_leibniz G \<sigma> B A"
  have el: "book_theory_formula \<Sigma> G ?E" by (rule book_leibniz_language[OF rich al bl])
  have fl: "book_theory_formula \<Sigma> G ?F" by (rule book_leibniz_language[OF rich bl al])
  show ?thesis
  proof (rule book_H_from_pointwise_models[OF rich book_imp_language[OF el fl]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "V (J g (book_imp ?E ?F))"
      by (simp only: M.book_imp_truth[OF typed el fl] M.book_leibniz_truth[OF rich typed al bl]
        M.book_leibniz_truth[OF rich typed bl al]; intro impI; rule book_leibniz_sym; assumption)
  qed
qed

theorem book_H_identity_transitivity:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    and cl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G C \<sigma>"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G \<sigma> A B)
    (book_imp (book_leibniz G \<sigma> B C) (book_leibniz G \<sigma> A C)))"
proof -
  let ?E = "book_leibniz G \<sigma> A B"
  let ?F = "book_leibniz G \<sigma> B C"
  let ?R = "book_leibniz G \<sigma> A C"
  have el: "book_theory_formula \<Sigma> G ?E" by (rule book_leibniz_language[OF rich al bl])
  have fl: "book_theory_formula \<Sigma> G ?F" by (rule book_leibniz_language[OF rich bl cl])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_leibniz_language[OF rich al cl])
  have tail: "book_theory_formula \<Sigma> G (book_imp ?F ?R)" by (rule book_imp_language[OF fl rl])
  show ?thesis
  proof (rule book_H_from_pointwise_models[OF rich book_imp_language[OF el tail]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "V (J g (book_imp ?E (book_imp ?F ?R)))"
      by (simp only: M.book_imp_truth[OF typed el tail] M.book_imp_truth[OF typed fl rl]
        M.book_leibniz_truth[OF rich typed al bl] M.book_leibniz_truth[OF rich typed bl cl]
        M.book_leibniz_truth[OF rich typed al cl]; intro impI; rule book_leibniz_trans; assumption)
  qed
qed

theorem book_H_identity_application:
  assumes rich: "sg_rich G"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G (Arr \<sigma> \<tau>) F H)
    (book_imp (book_leibniz G \<sigma> A B) (book_leibniz G \<tau> (NApp F A) (NApp H B))))"
proof -
  let ?E = "book_leibniz G (Arr \<sigma> \<tau>) F H"
  let ?I = "book_leibniz G \<sigma> A B"
  let ?R = "book_leibniz G \<tau> (NApp F A) (NApp H B)"
  have fal: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp F A) \<tau>"
    by (rule book_language_App[OF fl al])
  have hbl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp H B) \<tau>"
    by (rule book_language_App[OF hl bl])
  have el: "book_theory_formula \<Sigma> G ?E" by (rule book_leibniz_language[OF rich fl hl])
  have il: "book_theory_formula \<Sigma> G ?I" by (rule book_leibniz_language[OF rich al bl])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_leibniz_language[OF rich fal hbl])
  have tail: "book_theory_formula \<Sigma> G (book_imp ?I ?R)" by (rule book_imp_language[OF il rl])
  show ?thesis
  proof (rule book_H_from_pointwise_models[OF rich book_imp_language[OF el tail]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "V (J g (book_imp ?E (book_imp ?I ?R)))"
      by (simp only: M.book_imp_truth[OF typed el tail] M.book_imp_truth[OF typed il rl]
        M.book_leibniz_truth[OF rich typed fl hl] M.book_leibniz_truth[OF rich typed al bl]
        M.book_leibniz_truth[OF rich typed fal hbl]
        M.denote_app[OF UNIV_I UNIV_I UNIV_I fl al typed] M.denote_app[OF UNIV_I UNIV_I UNIV_I hl bl typed];
        intro impI; rule M.book_leibniz_application_cong[OF rich typed]; assumption)
  qed
qed

text \<open>
  Symmetry, transitivity and application congruence are original H
  implications with every term's type stated. The pointwise-model helper
  is just the independently proved H completeness theorem on its explicit
  canonical carrier. No C completeness, modal model, Functionality or
  arbitrary-world identity assumption occurs in these H certificates.
\<close>

end
