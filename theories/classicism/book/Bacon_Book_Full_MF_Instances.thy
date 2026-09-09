theory Bacon_Book_Full_MF_Instances
  imports Bacon_Book_MF_Argument_Renaming
begin

section \<open>Arbitrary typed heads with only the intended argument freshness\<close>

theorem book_full_C_MF_instance:
  assumes rich: "sg_rich G" and nt: "G n = \<sigma>"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
    and nf: "n \<notin> named_fv F" and nh: "n \<notin> named_fv H"
  shows "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> n F H)"
proof -
  let ?x = "book_MF_left G \<sigma> \<tau>"
  let ?y = "book_MF_right G \<sigma> \<tau>"
  let ?ns = "n # ?x # ?y # sorted_list_of_set (named_fv F)"
  let ?u = "named_chart_fresh G ?ns (Arr \<sigma> \<tau>)"
  have ut: "G ?u = Arr \<sigma> \<tau>" by (rule named_chart_fresh_type[OF rich])
  have fresh: "?u \<notin> set ?ns" by (rule named_chart_fresh_notin[OF rich])
  have un: "?u \<noteq> n" and ux: "?u \<noteq> ?x" and uf: "?u \<notin> named_fv F"
    using fresh by (auto simp: named_fv_finite)
  have nx: "n \<noteq> ?x" and ny: "n \<noteq> ?y"
    using nt book_MF_names_type(1,2)[OF rich, where \<sigma>=\<sigma> and \<tau>=\<tau>]
      book_type_not_own_arrow[where \<sigma>=\<sigma> and \<tau>=\<tau>] by auto
  have xy: "?x \<noteq> ?y" using book_MF_names_distinct[OF rich, where \<sigma>=\<sigma> and \<tau>=\<tau>] by auto
  have xn: "?x \<noteq> n" and yn: "?y \<noteq> n" using nx ny by auto
  have uy: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?u) (G ?y)"
    by (simp only: book_language_var_iff book_MF_names_type(2)[OF rich] ut)
  have fx: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (G ?x)"
    by (simp only: book_MF_names_type(1)[OF rich]; rule fl)
  have hu: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (G ?u)" by (simp only: ut; rule hl)
  have original: "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?y))"
    by (rule book_full_C_MF_argument_variant[OF rich nt])
  have nu: "n \<noteq> ?u"
  proof
    assume equal: "n = ?u"
    show False by (rule notE[OF un equal[symmetric]])
  qed
  have marker_fresh: "n \<notin> named_fv (NVar ?u)"
    by (simp only: named_fv.simps singleton_iff; rule nu)
  have marker_free: "named_free_for (NVar ?u) ?y (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?y))"
    by (rule book_named_free_for_MF_condition[OF _ _ marker_fresh]; simp)
  have marked_raw: "book_full_C_proves \<Sigma> G
    (named_subst ?y (NVar ?u) (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?y)))"
    by (rule book_full_C_variable_substitution[OF rich original uy marker_free])
  have marked: "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?u))"
    using marked_raw by (simp add: book_named_subst_MF_condition[OF yn] xy)
  have first_free: "named_free_for F ?x (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?u))"
    by (rule book_named_free_for_MF_condition; (simp | rule nf))
  have first_raw: "book_full_C_proves \<Sigma> G
    (named_subst ?x F (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?u)))"
    by (rule book_full_C_variable_substitution[OF rich marked fx first_free])
  have first: "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> n F (NVar ?u))"
    using first_raw by (simp add: book_named_subst_MF_condition[OF xn] ux)
  have payload_free: "named_free_for H ?u F" by (rule named_free_for_fresh[OF uf])
  have second_free: "named_free_for H ?u (book_MF_condition G \<sigma> \<tau> n F (NVar ?u))"
    by (rule book_named_free_for_MF_condition[OF payload_free _ nh]; simp)
  have second: "book_full_C_proves \<Sigma> G (named_subst ?u H (book_MF_condition G \<sigma> \<tau> n F (NVar ?u)))"
    by (rule book_full_C_variable_substitution[OF rich first hu second_free])
  have fixed_F: "named_subst ?u H F = F" by (rule named_subst_fresh[OF uf])
  show ?thesis using second by (simp add: book_named_subst_MF_condition[OF un] fixed_F)
qed

theorem book_full_C_function_identity_rule:
  assumes rich: "sg_rich G"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr (G n) \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr (G n) \<tau>)"
    and nf: "n \<notin> named_fv F" and nh: "n \<notin> named_fv H"
    and pointwise: "book_full_C_proves \<Sigma> G (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))"
  shows "book_full_C_proves \<Sigma> G (book_leibniz G (Arr (G n) \<tau>) F H)"
proof -
  have quantified: "book_full_C_proves \<Sigma> G
    (book_all G n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n))))"
    by (rule book_full_C_generalize[OF rich pointwise])
  have necessary: "book_full_C_proves \<Sigma> G
    (book_box G (book_all G n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))))"
    by (rule book_full_C_necessitation[OF rich quantified])
  have condition: "book_full_C_proves \<Sigma> G (book_MF_condition G (G n) \<tau> n F H)"
    by (rule book_full_C_MF_instance[OF rich refl fl hl nf nh])
  show ?thesis using condition unfolding book_MF_condition_def
    by (rule book_full_C_proves.MP[OF necessary _ book_leibniz_language[OF rich fl hl]])
qed

text \<open>
  MF(F,H;n) now holds for arbitrary typed F,H with n fresh for both.
  A fresh marker protects F from the later substitution for H; neither
  head is required to be closed or to avoid MF's fixed placeholders.
  The derived function-identity rule applies only to an original proved
  pointwise identity. It generalizes and necessitates that theorem before
  applying MF, not a temporary world assumption.
\<close>

end
