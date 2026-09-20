theory Goodman_Propositional_Equivalence_Bridge
  imports Goodman_H_Proof_Preservation
begin

section \<open>The old expanded biconditional and the book's biconditional\<close>

theorem gi_H_expanded_iff_to_book:
  fixes \<Sigma> :: "'c ssignature" and A B :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_H \<Sigma> G
    (book_imp (book_and G (book_imp A B) (book_imp B A)) (book_iff G A B))"
proof -
  have ab: "book_theory_formula \<Sigma> G (book_imp A B)" by (rule book_imp_language[OF al bl])
  have ba: "book_theory_formula \<Sigma> G (book_imp B A)" by (rule book_imp_language[OF bl al])
  have expanded: "book_theory_formula \<Sigma> G (book_and G (book_imp A B) (book_imp B A))"
    by (rule book_and_language[OF rich ab ba])
  have iff: "book_theory_formula \<Sigma> G (book_iff G A B)" by (rule book_iff_language[OF rich al bl])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_imp_language[OF expanded iff]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    show "V (J g (book_imp (book_and G (book_imp A B) (book_imp B A)) (book_iff G A B)))"
      by (simp only: M.book_imp_truth[OF typed expanded iff] M.book_and_truth[OF rich typed ab ba]
        M.book_imp_truth[OF typed al bl] M.book_imp_truth[OF typed bl al] M.book_iff_truth[OF rich typed al bl]; blast)
  qed
qed

theorem gi_goodman_expanded_PE:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and premise: "goodman_book_proves \<Sigma> G T (book_and G (book_imp A B) (book_imp B A))"
  shows "goodman_book_proves \<Sigma> G T (book_leibniz G Prop A B)"
proof -
  have certificate: "goodman_book_proves \<Sigma> G T
    (book_imp (book_and G (book_imp A B) (book_imp B A)) (book_iff G A B))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule gi_H_expanded_iff_to_book[OF rich al bl])
  have equivalent: "goodman_book_proves \<Sigma> G T (book_iff G A B)"
    by (rule goodman_book_proves.MP[OF premise certificate book_iff_language[OF rich al bl]])
  show ?thesis by (rule goodman_book_proves.PE[OF equivalent al bl])
qed

theorem gi_goodman_translated_PE:
  assumes rich: "sg_rich G" and a: "\<Gamma> \<turnstile> A : Prop" and b: "\<Gamma> \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>"
    and ac: "gi_constants_admitted k \<Sigma> A" and bc: "gi_constants_admitted k \<Sigma> B"
    and premise: "goodman_book_proves \<Sigma> G T
      (gi_to_book G ns k (Conj (Imp A B) (Imp B A)))"
  shows "goodman_book_proves \<Sigma> G T (gi_to_book G ns k (Eq Prop A B))"
proof -
  have expanded: "goodman_book_proves \<Sigma> G T
    (book_and G (book_imp (gi_to_book G ns k A) (gi_to_book G ns k B))
      (book_imp (gi_to_book G ns k B) (gi_to_book G ns k A)))"
    using premise by (simp only: gi_to_book.simps)
  have result: "goodman_book_proves \<Sigma> G T
    (book_leibniz G Prop (gi_to_book G ns k A) (gi_to_book G ns k B))"
    by (rule gi_goodman_expanded_PE[OF rich gi_to_book_language[OF rich a chart ac]
      gi_to_book_language[OF rich b chart bc] expanded])
  show ?thesis using result by (simp only: gi_to_book.simps)
qed

text \<open>
  The premise is theoremhood in C+[T], not membership in a temporary
  assumption set. No semantic validity of T is assumed. The H certificate
  justifies the change of biconditional representation before PE is used.
  This is the proposition-level rule, not yet nonempty vector Equivalence.
\<close>

end
