theory Bacon_Book_Function_Identity_Predicate
  imports Bacon_Book_Full_Term_World_Bridge
begin

definition book_function_identity_predicate where
  "book_function_identity_predicate G n \<tau> F H =
    NLam n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))"

lemma book_function_identity_predicate_language:
  assumes rich: "sg_rich G" and nt: "G n = \<sigma>"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_function_identity_predicate G n \<tau> F H) (Arr \<sigma> Prop)"
proof -
  have nl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar n) \<sigma>"
    by (simp only: book_language_var_iff; rule nt[symmetric])
  have body: "book_theory_formula \<Sigma> G (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))"
    by (rule book_leibniz_language[OF rich book_language_App[OF fl nl] book_language_App[OF hl nl]])
  show ?thesis unfolding book_function_identity_predicate_def
    using book_language_Lam[where n=n, OF body] by (simp only: nt)
qed

lemma book_function_identity_predicate_closed:
  "named_fv F = {} \<Longrightarrow> named_fv H = {} \<Longrightarrow>
    named_fv (book_function_identity_predicate G n \<tau> F H) = {}"
  by (auto simp: book_function_identity_predicate_def book_leibniz_fv)

lemma book_function_identity_predicate_beta:
  assumes fc: "named_fv F = {}" and hc: "named_fv H = {}" and ac: "named_fv A = {}"
  shows "named_beta_contract (NApp (book_function_identity_predicate G n \<tau> F H) A)
    (book_leibniz G \<tau> (NApp F A) (NApp H A))"
proof -
  have fixed_F: "named_subst n A F = F" by (rule named_subst_fresh; simp add: fc)
  have fixed_H: "named_subst n A H = H" by (rule named_subst_fresh; simp add: hc)
  have free: "named_free_for A n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))"
    by (rule book_exists_closed_free_for[OF ac])
  have substitution: "named_subst n A (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n))) =
    book_leibniz G \<tau> (NApp F A) (NApp H A)"
    by (simp add: book_named_subst_leibniz fixed_F fixed_H)
  show ?thesis unfolding book_function_identity_predicate_def
    using named_beta_contract.beta[OF free] by (simp only: substitution)
qed

context book_C_identity_world
begin

lemma function_identity_predicate_instance_member:
  assumes nt: "G n = \<sigma>" and fm: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and hm: "H \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and am: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
    and identity: "book_leibniz G \<tau> (NApp F A) (NApp H A) \<in> w"
  shows "NApp (book_function_identity_predicate G n \<tau> F H) A \<in> w"
proof -
  let ?R = "NApp (book_function_identity_predicate G n \<tau> F H) A"
  let ?I = "book_leibniz G \<tau> (NApp F A) (NApp H A)"
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)" by (rule book_closed_terms_language[OF fm])
  have hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr \<sigma> \<tau>)" by (rule book_closed_terms_language[OF hm])
  have al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>" by (rule book_closed_terms_language[OF am])
  have fc: "named_fv F = {}" by (rule book_closed_terms_closed[OF fm])
  have hc: "named_fv H = {}" by (rule book_closed_terms_closed[OF hm])
  have ac: "named_fv A = {}" by (rule book_closed_terms_closed[OF am])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_language_App[OF book_function_identity_predicate_language[OF rich nt fl hl] al])
  have il: "book_theory_formula \<Sigma> G ?I" by (rule book_leibniz_language[OF rich book_language_App[OF fl al] book_language_App[OF hl al]])
  have contraction: "named_beta_contract ?R ?I" by (rule book_function_identity_predicate_beta[OF fc hc ac])
  have expansion: "book_H \<Sigma> G (book_imp ?I ?R)"
    by (simp only: book_H_iff_theory[OF rich]; rule book_theory_derivable.Beta[OF il rl],
      rule disjI2, rule named_compatible_step.root, rule contraction)
  have rc: "named_fv ?R = {}"
    by (simp add: book_function_identity_predicate_closed[OF fc hc] ac)
  show ?thesis by (rule apply_H[OF expansion identity rc])
qed

end

text \<open>
  The predicate λn.(Fn=τHn) is typed and closed for closed F,H.
  Its application to a closed A contracts literally to FA=τHA, with
  capture conditions proved. Identity membership therefore gives
  membership of that predicate application in a closed C world, using
  only the original H β axiom and ordinary consequence.
\<close>

end
