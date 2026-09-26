theory Bacon_Book_Lambda_I_Existential_Conversion
  imports Bacon_Book_Environment_Development.Bacon_Book_Minimal_Existential_Syntax Bacon_Book_Lambda_I_Conversion
begin

section \<open>One β step unfolds the literal existential application\<close>

text \<open>
  ∃σ = λX.¬(∀σ y.¬(X y)). For a closed predicate F:σ→t, the
  application ∃σF therefore contracts to ¬(∀σ y.¬(F y)).
  Source: Bacon, Table 4.1, p.93; the witness-completeness setting is
  Proposition 15.4, p.319.

  Representation. We retain the chosen y = book_exists_argument_name G σ.
  Closedness of F discharges literal substitution's free-for condition;
  no binder is renamed while substituting. The raw contraction is proved
  separately from the typed formula implications. These are not an
  operator identity, a semantic truth clause, or an extra proof rule.
  Rebinding the displayed expansion to an arbitrary name is not claimed.
\<close>

text \<open>
  The existential operator of Table 4.1 is a λI term under a rich stock:
  its function variable occurs in the body and the two names differ.
\<close>

lemma book_lambda_I_exists_const:
  assumes rich: "sg_rich G"
  shows "book_lambda_I (book_exists_const G \<sigma>)"
  unfolding book_exists_const_def book_not_def
  by (simp add: book_lambda_I_not_const book_exists_names_distinct[OF rich])

lemma book_lambda_I_exists_application_language:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_formula \<Sigma> G (NApp (book_exists_const G \<sigma>) F)"
  by (rule conjI[OF book_exists_application_language[OF rich predicate]];
    simp add: lambda_I book_lambda_I_exists_const[OF rich])

lemma book_lambda_I_exists_closed_free_for:
  assumes closed: "named_fv F = {}"
  shows "named_free_for F n A"
  using closed by (induction A) auto

lemma book_lambda_I_exists_body_subst:
  assumes rich: "sg_rich G"
  shows "named_subst (book_exists_function_name G \<sigma>) F
      (book_not G (book_all G (book_exists_argument_name G \<sigma>)
        (book_not G (NApp (NVar (book_exists_function_name G \<sigma>))
          (NVar (book_exists_argument_name G \<sigma>)))))) =
    book_not G (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>)))))"
proof -
  let ?X = "book_exists_function_name G \<sigma>"
  let ?y = "book_exists_argument_name G \<sigma>"
  have distinct: "?y \<noteq> ?X" using book_exists_names_distinct[where \<sigma>=\<sigma>, OF rich] by simp
  have operator_fresh: "?X \<notin> named_fv (book_not_const G)"
    by (simp only: book_not_const_closed; simp)
  have operator_fixed: "named_subst ?X F (book_not_const G) = book_not_const G"
    by (rule named_subst_fresh[OF operator_fresh])
  show ?thesis by (simp add: book_not_def book_all_def operator_fixed distinct)
qed

lemma book_lambda_I_exists_beta_contract:
  assumes rich: "sg_rich G" and closed: "named_fv F = {}"
  shows "named_beta_contract (NApp (book_exists_const G \<sigma>) F)
    (book_not G (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))))"
proof -
  let ?X = "book_exists_function_name G \<sigma>"
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?body = "book_not G (book_all G ?y (book_not G (NApp (NVar ?X) (NVar ?y))))"
  have free_for: "named_free_for F ?X ?body" by (rule book_lambda_I_exists_closed_free_for[OF closed])
  have contraction: "named_beta_contract (NApp (NLam ?X ?body) F) (named_subst ?X F ?body)"
    by (rule named_beta_contract.beta[OF free_for])
  show ?thesis using contraction
    by (simp only: book_exists_const_as_all[OF rich] book_lambda_I_exists_body_subst[OF rich])
qed

lemma book_lambda_I_exists_beta_step:
  assumes rich: "sg_rich G" and closed: "named_fv F = {}"
  shows "named_compatible_step named_beta_contract (NApp (book_exists_const G \<sigma>) F)
    (book_not G (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))))"
  by (rule named_compatible_step.root; rule book_lambda_I_exists_beta_contract[OF rich closed])

lemma book_lambda_I_exists_expansion_language:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_formula \<Sigma> G
    (book_not G (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))))"
proof -
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NVar (book_exists_argument_name G \<sigma>)) \<sigma>"
    by (simp only: book_language_var_iff book_exists_argument_name_type[OF rich])
  have application: "book_lambda_I_formula \<Sigma> G (NApp F (NVar (book_exists_argument_name G \<sigma>)))"
    by (rule conjI[OF book_language_App[OF predicate variable]]; simp add: lambda_I)
  have occurs: "book_exists_argument_name G \<sigma> \<in>
    named_fv (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))"
    unfolding book_not_def by simp
  show ?thesis by (rule book_lambda_I_not_language[OF rich
    book_lambda_I_all_language[OF book_lambda_I_not_language[OF rich application] occurs]])
qed

section \<open>The two object-language implications\<close>

text \<open>
  ⊢ (∃σF)→¬∀σy.¬(F y), and ⊢ (¬∀σy.¬(F y))→∃σF.
  Both are instances of the existing immediate β schema with its
  respective orientation. S remains arbitrary; no assumption is discharged.
\<close>

theorem book_lambda_I_exists_unfold:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_derivable \<Sigma> G S
    (book_imp (NApp (book_exists_const G \<sigma>) F)
      (book_not G (book_all G (book_exists_argument_name G \<sigma>)
        (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>)))))))"
  by (rule book_lambda_I_derivable.Beta[
      OF book_lambda_I_exists_application_language[OF rich predicate lambda_I] book_lambda_I_exists_expansion_language[OF rich predicate lambda_I]],
      rule disjI1, rule book_lambda_I_exists_beta_step[OF rich closed])

theorem book_lambda_I_exists_fold:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_not G (book_all G (book_exists_argument_name G \<sigma>)
        (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))))
      (NApp (book_exists_const G \<sigma>) F))"
  by (rule book_lambda_I_derivable.Beta[
      OF book_lambda_I_exists_expansion_language[OF rich predicate lambda_I] book_lambda_I_exists_application_language[OF rich predicate lambda_I]],
      rule disjI2, rule book_lambda_I_exists_beta_step[OF rich closed])

theorem book_lambda_I_exists_conversion_pair:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_derivable \<Sigma> G S
      (book_imp (NApp (book_exists_const G \<sigma>) F)
        (book_not G (book_all G (book_exists_argument_name G \<sigma>)
          (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))))) \<and>
    book_lambda_I_derivable \<Sigma> G S
      (book_imp (book_not G (book_all G (book_exists_argument_name G \<sigma>)
          (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))))
        (NApp (book_exists_const G \<sigma>) F))"
  by (rule conjI[OF book_lambda_I_exists_unfold[OF rich predicate closed lambda_I]
      book_lambda_I_exists_fold[OF rich predicate closed lambda_I]])

end
