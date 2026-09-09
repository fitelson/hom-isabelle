theory Bacon_Book_Full_Classicism_Necessitation
  imports Bacon_Book_Full_Classicism_Least_Theory Bacon_Book_H_Modal_Certificates
begin

theorem book_full_C_necessitation:
  assumes rich: "sg_rich G" and premise: "book_full_C_proves \<Sigma> G P"
  shows "book_full_C_proves \<Sigma> G (book_box G P)"
proof -
  have pl: "book_theory_formula \<Sigma> G P" by (rule book_full_C_proves_language[OF rich premise])
  have tl: "book_theory_formula \<Sigma> G (book_top G)" by (rule book_top_language[OF rich])
  have il: "book_theory_formula \<Sigma> G (book_iff G P (book_top G))" by (rule book_iff_language[OF rich pl tl])
  have implication: "book_full_C_proves \<Sigma> G (book_imp P (book_iff G P (book_top G)))"
    by (rule book_full_C_proves.H[OF book_H_imp_iff_top[OF rich pl]])
  have equivalent: "book_full_C_proves \<Sigma> G (book_iff G P (book_top G))"
    by (rule book_full_C_proves.MP[OF premise implication il])
  have identity: "book_full_C_proves \<Sigma> G (book_leibniz G Prop P (book_top G))"
    by (rule book_full_C_proves.PE[OF equivalent pl tl])
  have fold: "book_full_C_proves \<Sigma> G (book_imp (book_leibniz G Prop P (book_top G)) (book_box G P))"
    by (rule book_full_C_proves.H[OF book_H_box_fold_unfold(1)[OF rich pl]])
  show ?thesis by (rule book_full_C_proves.MP[OF identity fold book_box_language[OF rich pl]])
qed

text \<open>
  Necessitation is derived for every original full-C theorem, including
  its MF axioms. It is not added as a primitive rule or allowed on local
  assumptions. The proof uses only PE and H certificates; it does not
  assume an embedding of the older vector-Equivalence base.
\<close>

end
