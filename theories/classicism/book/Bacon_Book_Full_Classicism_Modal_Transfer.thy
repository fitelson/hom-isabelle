theory Bacon_Book_Full_Classicism_Modal_Transfer
  imports Bacon_Book_Full_Classicism_Base_Bridge Bacon_Book_Classicism_Closed_Accessibility
    Bacon_Book_Full_Classicism_Closed_Maximal
begin

lemma book_full_C_normal_K:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G P \<Longrightarrow> book_theory_formula \<Sigma> G Q \<Longrightarrow>
    book_full_C_proves \<Sigma> G (book_K_formula G P Q)"
  by (rule book_C_base_embeds_full; (assumption | rule book_C_normal_K); assumption)

lemma book_full_C_modal_T:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G P \<Longrightarrow>
    book_full_C_proves \<Sigma> G (book_imp (book_box G P) P)"
  by (rule book_C_base_embeds_full; (assumption | rule book_C_modal_T); assumption)

lemma book_full_C_modal_4:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G P \<Longrightarrow>
    book_full_C_proves \<Sigma> G (book_imp (book_box G P) (book_box G (book_box G P)))"
  by (rule book_C_base_embeds_full; (assumption | rule book_C_modal_4); assumption)

theorem book_full_C_closed_maximal_is_base:
  assumes rich: "sg_rich G" and maximal: "book_full_C_closed_maximal_extension \<Sigma> G S M"
  shows "book_C_closed_maximal_extension \<Sigma> G S M"
proof -
  have included: "book_C_closed_theorems \<Sigma> G \<subseteq> book_full_C_closed_theorems \<Sigma> G"
    using book_C_base_embeds_full[OF rich] unfolding book_C_closed_theorems_def book_full_C_closed_theorems_def by blast
  show ?thesis using maximal included unfolding book_C_closed_maximal_extension_def
    book_full_C_closed_maximal_extension_def book_closed_maximal_extension_def by blast
qed

text \<open>
  The verified base embedding transfers the original K/T/4 theorems.
  A full-C closed maximal sentence set also satisfies the base maximal
  condition, because it contains the base's closed theorems and retains
  the same H consistency/maximality. This is a one-way structural fact;
  it does not identify the two canonical frames or their future truth sets.
\<close>

end
