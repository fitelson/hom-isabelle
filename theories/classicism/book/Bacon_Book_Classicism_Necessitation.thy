theory Bacon_Book_Classicism_Necessitation
  imports Bacon_Book_H_Modal_Certificates
begin

section \<open>Necessitation in the original C theorem set\<close>

theorem book_C_necessitation:
  assumes rich: "sg_rich G" and premise: "book_C_proves \<Sigma> G P"
  shows "book_C_proves \<Sigma> G (book_box G P)"
proof -
  have pl: "book_theory_formula \<Sigma> G P" by (rule book_C_proves_language[OF rich premise])
  have tl: "book_theory_formula \<Sigma> G (book_top G)" by (rule book_top_language[OF rich])
  have il: "book_theory_formula \<Sigma> G (book_iff G P (book_top G))" by (rule book_iff_language[OF rich pl tl])
  have implication: "book_C_proves \<Sigma> G (book_imp P (book_iff G P (book_top G)))"
    by (rule book_C_proves.H[OF book_H_imp_iff_top[OF rich pl]])
  have equivalent: "book_C_proves \<Sigma> G (book_iff G P (book_top G))"
    by (rule book_C_proves.MP[OF premise implication il])
  have identity: "book_C_proves \<Sigma> G (book_leibniz G Prop P (book_top G))"
    by (rule book_C_propositional_equivalence[OF pl tl equivalent])
  have fold: "book_C_proves \<Sigma> G (book_imp (book_leibniz G Prop P (book_top G)) (book_box G P))"
    by (rule book_C_proves.H[OF book_H_box_fold_unfold(1)[OF rich pl]])
  show ?thesis by (rule book_C_proves.MP[OF identity fold book_box_language[OF rich pl]])
qed

text \<open>
  From a C theorem P, the H certificate gives P↔⊤, then the
  propositional Equivalence rule gives P=ₜ⊤. H's checked folding
  certificate returns the literal □P. No new assumption is made
  necessary, and no C model or C completeness premise is used.
  This is the necessitation step needed in Proposition 18.3, p.399.
\<close>

end
