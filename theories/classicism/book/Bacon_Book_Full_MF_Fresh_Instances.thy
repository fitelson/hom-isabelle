theory Bacon_Book_Full_MF_Fresh_Instances
  imports Bacon_Book_MF_Free_For Bacon_Book_Full_MF_Closed_Instances
begin

theorem book_full_C_MF_fresh_instance:
  assumes rich: "sg_rich G"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
    and fresh_F: "book_MF_argument G \<sigma> \<tau> \<notin> named_fv F"
    and fresh_H: "book_MF_argument G \<sigma> \<tau> \<notin> named_fv H"
    and independent: "book_MF_right G \<sigma> \<tau> \<notin> named_fv F"
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
  have first_free: "named_free_for F ?x (book_MF_body G \<sigma> \<tau>)"
    by (simp only: book_MF_body_as_condition; rule book_named_free_for_MF_condition; (simp | rule fresh_F))
  have first: "book_full_C_proves \<Sigma> G (named_subst ?x F (book_MF_body G \<sigma> \<tau>))"
    by (rule book_full_C_variable_substitution[OF rich book_full_C_MF_body[OF rich] fx first_free])
  have first_shape: "named_subst ?x F (book_MF_body G \<sigma> \<tau>) = book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y)"
    by (simp add: book_MF_body_as_condition book_named_subst_MF_condition[OF xz] xy eq_commute)
  have open_condition: "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y))"
    using first by (simp only: first_shape)
  have free_F: "named_free_for H ?y F" by (rule named_free_for_fresh[OF independent])
  have second_free: "named_free_for H ?y (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y))"
    by (rule book_named_free_for_MF_condition[OF free_F _ fresh_H]; simp)
  have second: "book_full_C_proves \<Sigma> G (named_subst ?y H (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y)))"
    by (rule book_full_C_variable_substitution[OF rich open_condition hy second_free])
  have fixed_F: "named_subst ?y H F = F" by (rule named_subst_fresh[OF independent])
  have second_shape: "named_subst ?y H (book_MF_condition G \<sigma> \<tau> ?z F (NVar ?y)) = book_MF_condition G \<sigma> \<tau> ?z F H"
    by (simp add: book_named_subst_MF_condition[OF yz] fixed_F)
  show ?thesis using second by (simp only: second_shape)
qed

text \<open>
  F and H may now be open. The designated argument variable must be
  fresh for both heads, and the second placeholder must be absent from
  F so that sequential substitution leaves the first payload unchanged.
  The latter proviso is a proof-method condition, not part of Bacon's
  MF principle. Fresh relettering or simultaneous substitution must
  discharge it in the unrestricted instantiation/Equivalence bridge.
\<close>

end
