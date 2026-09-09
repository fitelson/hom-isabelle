theory Bacon_Book_MF_Term_Syntax
  imports Bacon_Book_Full_Classicism_Structural
    Bacon_Book_Environment_Development.Bacon_Book_Existential_Conversion
begin

section \<open>Literal substitution in the MF condition\<close>

definition book_MF_condition where
  "book_MF_condition G \<sigma> \<tau> n F H = book_imp
    (book_box G (book_all G n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))))
    (book_leibniz G (Arr \<sigma> \<tau>) F H)"

lemma book_MF_body_as_condition:
  "book_MF_body G \<sigma> \<tau> = book_MF_condition G \<sigma> \<tau> (book_MF_argument G \<sigma> \<tau>)
    (NVar (book_MF_left G \<sigma> \<tau>)) (NVar (book_MF_right G \<sigma> \<tau>))"
  by (simp only: book_MF_body_def book_MF_condition_def)

lemma book_named_subst_leibniz:
  "named_subst n A (book_leibniz G \<sigma> P Q) = book_leibniz G \<sigma> (named_subst n A P) (named_subst n A Q)"
proof -
  have fixed: "named_subst n A (book_leibniz_const G \<sigma>) = book_leibniz_const G \<sigma>"
    by (rule named_subst_fresh; simp only: book_leibniz_const_closed; simp)
  show ?thesis by (simp only: book_leibniz_def named_subst.simps fixed)
qed

lemma book_named_subst_box:
  "named_subst n A (book_box G P) = book_box G (named_subst n A P)"
proof -
  have closed: "named_fv (book_box_const G) = {}"
    by (simp add: book_box_const_def book_leibniz_fv book_top_closed)
  have fixed: "named_subst n A (book_box_const G) = book_box_const G"
    by (rule named_subst_fresh; simp add: closed)
  show ?thesis by (simp only: book_box_def named_subst.simps fixed)
qed

lemma book_named_subst_imp:
  "named_subst n A (book_imp P Q) = book_imp (named_subst n A P) (named_subst n A Q)"
  by (simp only: book_imp_def named_subst.simps)

lemma book_named_subst_all_other:
  fixes n m :: nat
  assumes different: "n \<noteq> m"
  shows "named_subst n A (book_all G m P) = book_all G m (named_subst n A P)"
proof -
  have reverse: "m \<noteq> n"
  proof
    assume equal: "m = n"
    show False by (rule notE[OF different equal[symmetric]])
  qed
  show ?thesis by (simp only: book_all_def named_subst.simps reverse if_False)
qed

lemma book_named_subst_MF_condition:
  fixes x n :: nat
  assumes different: "x \<noteq> n"
  shows "named_subst x A (book_MF_condition G \<sigma> \<tau> n F H) =
    book_MF_condition G \<sigma> \<tau> n (named_subst x A F) (named_subst x A H)"
proof -
  have reverse: "n \<noteq> x"
  proof
    assume equal: "n = x"
    show False by (rule notE[OF different equal[symmetric]])
  qed
  show ?thesis by (simp only: book_MF_condition_def book_named_subst_imp book_named_subst_box
    book_named_subst_all_other[OF different] book_named_subst_leibniz named_subst.simps reverse if_False)
qed

lemma book_MF_condition_language:
  assumes rich: "sg_rich G" and nt: "G n = \<sigma>"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
  shows "book_theory_formula \<Sigma> G (book_MF_condition G \<sigma> \<tau> n F H)"
proof -
  have nl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar n) \<sigma>"
    by (simp only: book_language_var_iff; rule nt[symmetric])
  show ?thesis unfolding book_MF_condition_def
    by (rule book_imp_language[OF book_box_language[OF rich book_all_language[
      OF book_leibniz_language[OF rich book_language_App[OF fl nl] book_language_App[OF hl nl]]]]
      book_leibniz_language[OF rich fl hl]])
qed

text \<open>
  MF(F,H;n) is the open condition □∀n.(Fn=τHn) → F=σ→τH.
  These are literal substitution identities, with x≠n required when
  substitution passes its binder. They do not establish free-for by
  themselves: admissible proof substitution retains a separate capture
  check. Closed logical operators are fixed using their proved FV facts.
\<close>

end
