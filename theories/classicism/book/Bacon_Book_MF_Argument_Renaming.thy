theory Bacon_Book_MF_Argument_Renaming
  imports Bacon_Book_MF_Binder_Conversion
begin

theorem book_MF_condition_binder_conversion:
  assumes rich: "sg_rich G" and mt: "G m = \<sigma>" and nt: "G n = \<sigma>"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
    and mf: "m \<notin> named_fv F" and mh: "m \<notin> named_fv H"
    and nf: "n \<notin> named_fv F" and nh: "n \<notin> named_fv H"
  shows "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop
    (book_MF_condition G \<sigma> \<tau> m F H) (book_MF_condition G \<sigma> \<tau> n F H)"
proof -
  let ?A = "book_leibniz G \<tau> (NApp F (NVar m)) (NApp H (NVar m))"
  let ?B = "book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n))"
  have ml: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar m) \<sigma>"
    by (simp only: book_language_var_iff; rule mt[symmetric])
  have al: "book_theory_formula \<Sigma> G ?A" by (rule book_leibniz_language[OF rich book_language_App[OF fl ml] book_language_App[OF hl ml]])
  have same: "G m = G n" by (simp only: mt nt)
  have fresh: "n \<notin> named_fv (NLam m ?A)" using nf nh by (auto simp: book_leibniz_fv)
  have free_F: "named_free_for (NVar n) m F" by (rule named_free_for_fresh[OF mf])
  have free_H: "named_free_for (NVar n) m H" by (rule named_free_for_fresh[OF mh])
  have permitted: "named_free_for (NVar n) m ?A"
    by (rule book_named_free_for_leibniz; simp add: free_F free_H)
  have fixed_F: "named_subst m (NVar n) F = F" by (rule named_subst_fresh[OF mf])
  have fixed_H: "named_subst m (NVar n) H = H" by (rule named_subst_fresh[OF mh])
  have substitution: "named_subst m (NVar n) ?A = ?B" by (simp add: book_named_subst_leibniz fixed_F fixed_H)
  have predicates: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G (Arr \<sigma> Prop) (NLam m ?A) (NLam n ?B)"
    using book_binder_rename_with_free_for[OF book_language_named[OF al] same fresh permitted]
    by (simp only: mt substitution)
  have quantified: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop
    (book_all G m ?A) (book_all G n ?B)"
    unfolding book_all_def by (simp only: mt nt; rule named_conversion_App_right[
      OF book_language_named[OF book_all_operator_language] predicates])
  have boxed: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop
    (book_box G (book_all G m ?A)) (book_box G (book_all G n ?B))"
    unfolding book_box_def by (rule named_conversion_App_right[OF book_language_named[OF book_box_const_language[OF rich]] quantified])
  have consequent: "named_in_language book_minimal_logical_type \<Sigma> G (book_leibniz G (Arr \<sigma> \<tau>) F H) Prop"
    by (rule book_language_named[OF book_leibniz_language[OF rich fl hl]])
  show ?thesis unfolding book_MF_condition_def book_imp_def
    by (rule named_conversion_App_left[OF named_conversion_App_right[
      OF book_language_named[OF book_imp_operator_language] boxed] consequent])
qed

lemma book_type_not_own_arrow:
  "\<sigma> \<noteq> Arr \<sigma> \<tau>"
  by (induction \<sigma> arbitrary: \<tau>) auto

theorem book_full_C_MF_argument_variant:
  assumes rich: "sg_rich G" and nt: "G n = \<sigma>"
  shows "book_full_C_proves \<Sigma> G (book_MF_condition G \<sigma> \<tau> n
    (NVar (book_MF_left G \<sigma> \<tau>)) (NVar (book_MF_right G \<sigma> \<tau>)))"
proof -
  let ?x = "book_MF_left G \<sigma> \<tau>"
  let ?y = "book_MF_right G \<sigma> \<tau>"
  let ?z = "book_MF_argument G \<sigma> \<tau>"
  have nx: "n \<noteq> ?x" and ny: "n \<noteq> ?y"
    using nt book_MF_names_type(1,2)[OF rich, where \<sigma>=\<sigma> and \<tau>=\<tau>] book_type_not_own_arrow[where \<sigma>=\<sigma> and \<tau>=\<tau>] by auto
  have zx: "?z \<noteq> ?x" and zy: "?z \<noteq> ?y"
    using book_MF_names_distinct[OF rich, where \<sigma>=\<sigma> and \<tau>=\<tau>] by auto
  have xl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?x) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff; rule book_MF_names_type(1)[OF rich, symmetric])
  have yl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff; rule book_MF_names_type(2)[OF rich, symmetric])
  have conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop
    (book_MF_body G \<sigma> \<tau>) (book_MF_condition G \<sigma> \<tau> n (NVar ?x) (NVar ?y))"
    by (simp only: book_MF_body_as_condition; rule book_MF_condition_binder_conversion[
      OF rich book_MF_names_type(3)[OF rich] nt xl yl]; simp add: zx zy nx ny)
  show ?thesis by (rule book_full_C_conversion[OF rich book_full_C_MF_body[OF rich] conversion])
qed

text \<open>
  The argument binder can be changed by explicit η/β conversion when
  both old and new names are fresh for the heads. For the original MF
  variables, every n of the argument type is eligible: σ is not σ→τ,
  so n cannot be either functional placeholder. This supplies a proved
  MF body with any correctly typed argument variable, before inserting
  potentially open function terms.
\<close>

end
