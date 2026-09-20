theory Goodman_Theorem_Equivalence_Congruence
  imports Goodman_Modal_Abbreviation_Bridge
begin

section \<open>Theorem-level equivalence under implication and universal quantification\<close>

text \<open>
  The premises below are theorems of the same C+[T] extension. In
  particular the universal rule generalizes a theorem, not a local
  assumption. These rules do not license contextual Equivalence from
  an assumed material biconditional.
\<close>

lemma gi_H_iff_reflexive:
  fixes \<Sigma> :: "'c ssignature" and A :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_H \<Sigma> G (book_iff G A A)"
proof (rule gi_H_validity_certificate[OF rich book_iff_language[OF rich al al]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
  assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
  show "V (J g (book_iff G A A))" by (simp only: M.book_iff_truth[OF rich typed al al]; simp)
qed

lemma gi_goodman_iff_reflexive:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G A \<Longrightarrow>
    goodman_book_proves \<Sigma> G T (book_iff G A A)"
  by (rule goodman_book_proves.Base, rule book_full_C_proves.H, rule gi_H_iff_reflexive; assumption)

lemma gi_H_iff_imp_congruence:
  fixes \<Sigma> :: "'c ssignature" and A B C D :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B" and cl: "book_theory_formula \<Sigma> G C"
    and dl: "book_theory_formula \<Sigma> G D"
  shows "book_H \<Sigma> G (book_imp (book_iff G A B)
    (book_imp (book_iff G C D) (book_iff G (book_imp A C) (book_imp B D))))"
proof -
  have lang: "book_theory_formula \<Sigma> G (book_imp (book_iff G A B)
    (book_imp (book_iff G C D) (book_iff G (book_imp A C) (book_imp B D))))"
    by (intro book_imp_language book_iff_language[OF rich] al bl cl dl)
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich lang])
    fix E :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model E app \<Sigma> G J V c" and typed: "book_env_typed E G g"
    interpret M: book_full_minimal_model E app \<Sigma> G J V c by (rule model)
    show "V (J g (book_imp (book_iff G A B)
      (book_imp (book_iff G C D) (book_iff G (book_imp A C) (book_imp B D)))))"
      by (simp add: M.book_imp_truth M.book_iff_truth book_imp_language book_iff_language rich typed al bl cl dl)
  qed
qed

lemma gi_goodman_iff_imp_congruence:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B" and cl: "book_theory_formula \<Sigma> G C"
    and dl: "book_theory_formula \<Sigma> G D"
    and ab: "goodman_book_proves \<Sigma> G T (book_iff G A B)"
    and cd: "goodman_book_proves \<Sigma> G T (book_iff G C D)"
  shows "goodman_book_proves \<Sigma> G T (book_iff G (book_imp A C) (book_imp B D))"
proof -
  have result: "book_theory_formula \<Sigma> G (book_iff G (book_imp A C) (book_imp B D))"
    by (intro book_iff_language[OF rich] book_imp_language al bl cl dl)
  have tail: "book_theory_formula \<Sigma> G
    (book_imp (book_iff G C D) (book_iff G (book_imp A C) (book_imp B D)))"
    by (intro book_imp_language book_iff_language[OF rich] cl dl result)
  have certificate: "goodman_book_proves \<Sigma> G T (book_imp (book_iff G A B)
    (book_imp (book_iff G C D) (book_iff G (book_imp A C) (book_imp B D))))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule gi_H_iff_imp_congruence[OF rich al bl cl dl])
  show ?thesis by (rule goodman_book_proves.MP[OF cd
    goodman_book_proves.MP[OF ab certificate tail] result])
qed

lemma gi_H_iff_all_congruence:
  fixes \<Sigma> :: "'c ssignature" and A B :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_H \<Sigma> G (book_imp (book_all G n (book_iff G A B))
    (book_iff G (book_all G n A) (book_all G n B)))"
proof -
  have il: "book_theory_formula \<Sigma> G (book_iff G A B)" by (rule book_iff_language[OF rich al bl])
  have lang: "book_theory_formula \<Sigma> G (book_imp (book_all G n (book_iff G A B))
    (book_iff G (book_all G n A) (book_all G n B)))"
    by (intro book_imp_language book_iff_language[OF rich] book_all_language al bl il)
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich lang])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    have each: "\<And>a. a \<in> D (G n) \<Longrightarrow>
      V (J (g(n := a)) (book_iff G A B)) = (V (J (g(n := a)) A) = V (J (g(n := a)) B))"
      by (rule M.book_iff_truth[OF rich book_env_update[OF typed] al bl]; assumption)
    show "V (J g (book_imp (book_all G n (book_iff G A B))
      (book_iff G (book_all G n A) (book_all G n B))))"
      by (simp only: M.book_imp_truth[OF typed book_all_language[OF il]
          book_iff_language[OF rich book_all_language[OF al] book_all_language[OF bl]]]
        M.book_iff_truth[OF rich typed book_all_language[OF al] book_all_language[OF bl]]
        M.book_all_truth[OF typed il] M.book_all_truth[OF typed al] M.book_all_truth[OF typed bl];
        use each in blast)
  qed
qed

lemma gi_goodman_iff_all_congruence:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and ab: "goodman_book_proves \<Sigma> G T (book_iff G A B)"
  shows "goodman_book_proves \<Sigma> G T (book_iff G (book_all G n A) (book_all G n B))"
proof -
  have universal: "goodman_book_proves \<Sigma> G T (book_all G n (book_iff G A B))"
    by (rule gi_goodman_generalize[OF rich ab])
  have certificate: "goodman_book_proves \<Sigma> G T (book_imp (book_all G n (book_iff G A B))
    (book_iff G (book_all G n A) (book_all G n B)))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule gi_H_iff_all_congruence[OF rich al bl])
  show ?thesis by (rule goodman_book_proves.MP[OF universal certificate];
    intro book_iff_language[OF rich] book_all_language al bl)
qed

lemma gi_H_iff_forward:
  fixes \<Sigma> :: "'c ssignature" and A B :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_H \<Sigma> G (book_imp (book_iff G A B) (book_imp A B))"
proof (rule gi_H_validity_certificate[OF rich
    book_imp_language[OF book_iff_language[OF rich al bl] book_imp_language[OF al bl]]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
  assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
  show "V (J g (book_imp (book_iff G A B) (book_imp A B)))"
    by (simp add: M.book_imp_truth M.book_iff_truth book_imp_language book_iff_language rich typed al bl)
qed

lemma gi_H_iff_symmetric:
  fixes \<Sigma> :: "'c ssignature" and A B :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_H \<Sigma> G (book_imp (book_iff G A B) (book_iff G B A))"
proof (rule gi_H_validity_certificate[OF rich
    book_imp_language[OF book_iff_language[OF rich al bl] book_iff_language[OF rich bl al]]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
  assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
  show "V (J g (book_imp (book_iff G A B) (book_iff G B A)))"
    by (simp add: M.book_imp_truth M.book_iff_truth book_imp_language book_iff_language rich typed al bl)
qed

lemma gi_goodman_iff_transport:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and ab: "goodman_book_proves \<Sigma> G T (book_iff G A B)"
    and derivation: "goodman_book_proves \<Sigma> G T A"
  shows "goodman_book_proves \<Sigma> G T B"
proof -
  have certificate: "goodman_book_proves \<Sigma> G T (book_imp (book_iff G A B) (book_imp A B))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H, rule gi_H_iff_forward[OF rich al bl])
  show ?thesis by (rule goodman_book_proves.MP[OF derivation
    goodman_book_proves.MP[OF ab certificate book_imp_language[OF al bl]] bl])
qed

theorem gi_goodman_equivalent_proofs:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and ab: "goodman_book_proves \<Sigma> G T (book_iff G A B)"
  shows "goodman_book_proves \<Sigma> G T A \<longleftrightarrow> goodman_book_proves \<Sigma> G T B"
proof -
  have certificate: "goodman_book_proves \<Sigma> G T (book_imp (book_iff G A B) (book_iff G B A))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H, rule gi_H_iff_symmetric[OF rich al bl])
  have ba: "goodman_book_proves \<Sigma> G T (book_iff G B A)"
    by (rule goodman_book_proves.MP[OF ab certificate book_iff_language[OF rich bl al]])
  show ?thesis using gi_goodman_iff_transport[OF rich al bl ab]
    gi_goodman_iff_transport[OF rich bl al ba] by blast
qed

end
