theory Bacon_Book_MF_Free_For
  imports Bacon_Book_MF_Term_Syntax
begin

lemma book_named_free_for_leibniz:
  assumes left: "named_free_for A x P" and right: "named_free_for A x Q"
  shows "named_free_for A x (book_leibniz G \<sigma> P Q)"
proof -
  have operator: "named_free_for A x (book_leibniz_const G \<sigma>)"
    by (rule named_free_for_fresh; simp only: book_leibniz_const_closed; simp)
  show ?thesis by (simp only: book_leibniz_def named_free_for.simps; intro conjI; rule operator left right)
qed

lemma book_named_free_for_box:
  assumes body: "named_free_for A x P"
  shows "named_free_for A x (book_box G P)"
proof -
  have closed: "named_fv (book_box_const G) = {}" by (simp add: book_box_const_def book_leibniz_fv book_top_closed)
  have operator: "named_free_for A x (book_box_const G)" by (rule named_free_for_fresh; simp add: closed)
  show ?thesis by (simp only: book_box_def named_free_for.simps; rule conjI[OF operator body])
qed

lemma book_named_free_for_all:
  assumes body: "named_free_for A x P" and fresh: "n \<notin> named_fv A"
  shows "named_free_for A x (book_all G n P)"
  unfolding book_all_def using body fresh by auto

lemma book_named_free_for_imp:
  assumes left: "named_free_for A x P" and right: "named_free_for A x Q"
  shows "named_free_for A x (book_imp P Q)"
  by (simp only: book_imp_def named_free_for.simps; intro conjI; (rule TrueI | rule left | rule right))

theorem book_named_free_for_MF_condition:
  assumes left: "named_free_for A x F" and right: "named_free_for A x H"
    and fresh: "n \<notin> named_fv A"
  shows "named_free_for A x (book_MF_condition G \<sigma> \<tau> n F H)"
proof -
  have argument: "named_free_for A x (NVar n)" by simp
  have fl: "named_free_for A x (NApp F (NVar n))" by (simp add: left)
  have hl: "named_free_for A x (NApp H (NVar n))" by (simp add: right)
  show ?thesis unfolding book_MF_condition_def
    by (rule book_named_free_for_imp[OF book_named_free_for_box[OF book_named_free_for_all[
      OF book_named_free_for_leibniz[OF fl hl] fresh]] book_named_free_for_leibniz[OF left right]])
qed

text \<open>
  Closed logical operators cannot capture an inserted free occurrence.
  In MF(F,H;n), it is enough to check substitution in F and H and to
  keep n outside the payload's free variables. These are sufficient
  capture conditions, not a replacement for literal substitution typing.
\<close>

end
