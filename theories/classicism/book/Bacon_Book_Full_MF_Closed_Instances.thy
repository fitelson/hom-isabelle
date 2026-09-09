theory Bacon_Book_Full_MF_Closed_Instances
  imports Bacon_Book_MF_Term_Syntax
begin

theorem book_full_C_MF_closed_instance:
  assumes rich: "sg_rich G"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
    and fc: "named_fv F = {}" and hc: "named_fv H = {}"
  shows "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> (book_MF_argument G \<sigma> \<tau>) F H)"
proof -
  let ?x = "book_MF_left G \<sigma> \<tau>"
  let ?y = "book_MF_right G \<sigma> \<tau>"
  let ?z = "book_MF_argument G \<sigma> \<tau>"
  have xy: "?x \<noteq> ?y" and xz: "?x \<noteq> ?z" and yz: "?y \<noteq> ?z"
    using book_MF_names_distinct[OF rich, where \<sigma>=\<sigma> and \<tau>=\<tau>] by auto
  have fx: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (G ?x)"
    by (simp only: book_MF_names_type(1)[OF rich]; rule fl)
  have hy: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (G ?y)"
    by (simp only: book_MF_names_type(2)[OF rich]; rule hl)
  have first_free: "named_free_for F ?x (book_MF_body G \<sigma> \<tau>)" by (rule book_exists_closed_free_for[OF fc])
  have first: "book_full_C_proves \<Sigma> G (named_subst ?x F (book_MF_body G \<sigma> \<tau>))"
    by (rule book_full_C_variable_substitution[OF rich book_full_C_MF_body[OF rich] fx first_free])
  have first_shape: "named_subst ?x F (book_MF_body G \<sigma> \<tau>) = book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y)"
    by (simp add: book_MF_body_as_condition book_named_subst_MF_condition[OF xz] xy eq_commute)
  have open_condition: "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y))"
    using first by (simp only: first_shape)
  have second_free: "named_free_for H ?y (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y))"
    by (rule book_exists_closed_free_for[OF hc])
  have second: "book_full_C_proves \<Sigma> G (named_subst ?y H (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y)))"
    by (rule book_full_C_variable_substitution[OF rich open_condition hy second_free])
  have fixed_F: "named_subst ?y H F = F" by (rule named_subst_fresh; simp add: fc)
  have second_shape: "named_subst ?y H (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y)) = book_MF_condition G \<sigma> \<tau> ?z F H"
    by (simp add: book_named_subst_MF_condition[OF yz] fixed_F)
  show ?thesis using second by (simp only: second_shape)
qed

text \<open>
  The instance needed for closed term representatives is now an actual
  full-C theorem at every pair of types. We remove MF's outer binders,
  replace X by F and Y by H, and check both free-for conditions. Since
  F is closed, the second replacement does not alter its payload.
  The argument binder remains the designated typed MF variable.
  This is not yet the arbitrary-open-head instance needed to recover
  vector Equivalence; no such bridge is inferred from this theorem.
\<close>

end
