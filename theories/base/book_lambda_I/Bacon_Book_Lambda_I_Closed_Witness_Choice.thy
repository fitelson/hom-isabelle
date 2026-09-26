theory Bacon_Book_Lambda_I_Closed_Witness_Choice
  imports Bacon_Book_Lambda_I_Fresh_Constant_Generalization Bacon_Book_Lambda_I_Existential_Conversion Bacon_Book_Lambda_I_Negative_Predicate_Generalization Bacon_Book_Lambda_I_Theory_Consistency Bacon_Book_Lambda_I_Theory_Signature_Conservativity
begin

section \<open>Failure of a closed positive extension yields its negation\<close>

lemma book_lambda_I_closed_inconsistency_not:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and inconsistent: "\<not> book_lambda_I_consistent \<Sigma> G (insert A S)"
  shows "book_lambda_I_derivable \<Sigma> G S (book_not G A)"
proof -
  have contradiction: "book_lambda_I_derivable \<Sigma> G (insert A S) (book_bottom G)"
    using inconsistent unfolding book_lambda_I_consistent_def by blast
  have conditional: "book_lambda_I_derivable \<Sigma> G S (book_imp A (book_bottom G))"
    by (rule book_lambda_I_closed_deduction[OF rich al closed contradiction])
  have folding: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp A (book_bottom G)) (book_not G A))"
    by (rule book_lambda_I_not_fold[OF rich al])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF conditional folding book_lambda_I_not_language[OF rich al]])
qed

section \<open>A consistent choice for one fresh witness\<close>

text \<open>
  Let S be consistent in Σ, let F:σ→t be a CLOSED predicate of Σ,
  and choose c∉Σσ. In Σ[c:σ], at least one of S∪{Fc} and
  S∪{¬∃σF} is consistent. This is the closed-predicate witness-choice
  step needed for Proposition 15.4, p.319, with the open-formula
  qualification made explicit.

  If both extensions failed, closed deduction would give ¬Fc and ∃σF.
  Fresh-constant retraction gives an old-signature proof of ¬Fx for x
  fresh in F. Move that instance to the exact variable used by the literal
  existential operator and generalize. Its result ∀y.¬Fy contradicts
  the β unfolding of ∃σF. Every conclusion and premise of the final
  contradiction is back in Σ.

  S may be infinite and may contain open formulas. Its nonlogical names
  must belong to Σ; no freshness against all variable names of S is
  assumed. The new constant is fresh only at its indicated type. This
  lemma assumes an available c; later carrier enlargement must supply
  such names for arbitrary signatures. It constructs no complete theory
  or model and does not assume that such a construction exists.
\<close>

theorem book_lambda_I_closed_witness_choice:
  assumes rich: "sg_rich G"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
    and premise_names: "\<And>A. A \<in> S \<Longrightarrow> named_in_signature \<Sigma> A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F" and fresh: "c \<notin> \<Sigma> \<sigma>"
  shows "book_lambda_I_consistent (book_add_constant \<Sigma> c \<sigma>) G (insert (NApp F (NConst c \<sigma>)) S) \<or>
    book_lambda_I_consistent (book_add_constant \<Sigma> c \<sigma>) G
      (insert (book_not G (NApp (book_exists_const G \<sigma>) F)) S)"
proof (rule ccontr)
  let ?\<Omega> = "book_add_constant \<Sigma> c \<sigma>"
  let ?Fc = "NApp F (NConst c \<sigma>)"
  let ?E = "NApp (book_exists_const G \<sigma>) F"
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?P = "book_all G ?y (book_not G (NApp F (NVar ?y)))"
  assume neither: "\<not> (book_lambda_I_consistent ?\<Omega> G (insert ?Fc S) \<or>
      book_lambda_I_consistent ?\<Omega> G (insert (book_not G ?E) S))"
  have first_bad: "\<not> book_lambda_I_consistent ?\<Omega> G (insert ?Fc S)"
    and second_bad: "\<not> book_lambda_I_consistent ?\<Omega> G (insert (book_not G ?E) S)"
    using neither by blast+
  have inclusion: "\<Sigma> \<tau> \<subseteq> ?\<Omega> \<tau>" for \<tau> by (rule book_add_constant_subset)
  have enlarged_F: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G F (Arr \<sigma> Prop)"
    by (rule book_lambda_I_language_signature_mono[OF predicate inclusion])
  have witness_constant: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G (NConst c \<sigma>) \<sigma>"
    by (simp add: book_language_const_iff book_add_constant_def)
  have Fc_language: "book_lambda_I_formula ?\<Omega> G ?Fc"
    by (rule conjI[OF book_language_App[OF enlarged_F witness_constant]]; simp add: lambda_I)
  have Fc_closed: "named_fv ?Fc = {}" using closed by simp
  have negative_c: "book_lambda_I_derivable ?\<Omega> G S (book_not G ?Fc)"
    by (rule book_lambda_I_closed_inconsistency_not[OF rich Fc_language Fc_closed first_bad])
  obtain x where xtype: "G x = \<sigma>" and xnames: "x \<notin> named_vars F"
    and negative_x: "book_lambda_I_derivable \<Sigma> G S (book_not G (NApp F (NVar x)))"
    using book_lambda_I_fresh_constant_retraction[where G=G and \<Sigma>=\<Sigma> and \<sigma>=\<sigma>
      and c=c and F=F, OF rich fresh premise_names predicate negative_c] by blast
  have xfree: "x \<notin> named_fv F" using xnames named_fv_subset_vars[where A=F] by blast
  have universal_negative: "book_lambda_I_derivable \<Sigma> G S ?P"
    by (rule book_lambda_I_negative_predicate_generalize[OF rich negative_x predicate xtype xfree])
  have enlarged_E: "book_lambda_I_formula ?\<Omega> G ?E"
    by (rule book_lambda_I_exists_application_language[OF rich enlarged_F lambda_I])
  have E_closed: "named_fv ?E = {}" by (simp only: book_exists_application_fv closed)
  have positive_enlarged: "book_lambda_I_derivable ?\<Omega> G S ?E"
    by (rule book_lambda_I_closed_inconsistency_refutation[OF rich enlarged_E E_closed second_bad])
  have old_E: "book_lambda_I_formula \<Sigma> G ?E"
    by (rule book_lambda_I_exists_application_language[OF rich predicate lambda_I])
  have old_E_names: "named_in_signature \<Sigma> ?E" by (rule book_lambda_I_formula_signature[OF old_E])
  have positive: "book_lambda_I_derivable \<Sigma> G S ?E"
    by (rule book_lambda_I_foreign_constants_eliminate[OF rich positive_enlarged old_E_names];
      rule premise_names; assumption)
  have y_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) \<sigma>"
    by (simp only: book_language_var_iff book_exists_argument_name_type[OF rich])
  have Fy_language: "book_lambda_I_formula \<Sigma> G (NApp F (NVar ?y))"
    by (rule conjI[OF book_language_App[OF predicate y_language]]; simp add: lambda_I)
  have y_occurs: "?y \<in> named_fv (book_not G (NApp F (NVar ?y)))" unfolding book_not_def by simp
  have P_language: "book_lambda_I_formula \<Sigma> G ?P"
    by (rule book_lambda_I_all_language[OF book_lambda_I_not_language[OF rich Fy_language] y_occurs])
  have unfolding_step: "book_lambda_I_derivable \<Sigma> G S (book_imp ?E (book_not G ?P))"
    by (rule book_lambda_I_exists_unfold[OF rich predicate closed lambda_I])
  have negative_P: "book_lambda_I_derivable \<Sigma> G S (book_not G ?P)"
    by (rule book_lambda_I_derivable.MP[OF positive unfolding_step book_lambda_I_not_language[OF rich P_language]])
  have refutation: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_not G ?P) (book_imp ?P (book_bottom G)))"
    by (rule book_lambda_I_not_unfold[OF rich P_language])
  have conditional: "book_lambda_I_derivable \<Sigma> G S (book_imp ?P (book_bottom G))"
    by (rule book_lambda_I_derivable.MP[OF negative_P refutation
      book_lambda_I_imp_language[OF P_language book_lambda_I_bottom_language[OF rich]]])
  have contradiction: "book_lambda_I_derivable \<Sigma> G S (book_bottom G)"
    by (rule book_lambda_I_derivable.MP[OF universal_negative conditional book_lambda_I_bottom_language[OF rich]])
  show False using consistent contradiction unfolding book_lambda_I_consistent_def by blast
qed

end
