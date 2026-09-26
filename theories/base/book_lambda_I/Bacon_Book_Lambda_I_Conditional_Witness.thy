theory Bacon_Book_Lambda_I_Conditional_Witness
  imports Bacon_Book_Lambda_I_Closed_Witness_Choice Bacon_Book_Lambda_I_Closed_Negation_Complete
    Bacon_Book_Environment_Development.Bacon_Book_Conditional_Witness
begin

section \<open>The literal conditional witness formula\<close>

text \<open>
  W(F,c) is (∃σF)→Fc. The existential operator is the actual closed
  λ-definition from Table 4.1; neither ∃ nor W is a new object-language
  constructor. Source role: expressing the two alternatives of Bacon's
  Proposition 15.4, p.319, by one conditional witness axiom.
\<close>

text \<open>
  λI variant. The witness formula and its closedness are those of the
  unrestricted development. Under a rich stock the existential operator
  of Table 4.1 is a λI term, so W(F,c) is a λI term exactly when F is;
  it is a λI formula of Σ under the displayed typing and declaration
  guards.
\<close>

lemma book_lambda_I_witness_axiom:
  assumes rich: "sg_rich G" and lambda_I: "book_lambda_I F"
  shows "book_lambda_I (book_witness_axiom G \<sigma> F c)"
  unfolding book_witness_axiom_def book_imp_def
  by (simp add: book_lambda_I_exists_const[OF rich] lambda_I)

lemma book_lambda_I_witness_axiom_language:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and declared: "c \<in> \<Sigma> \<sigma>" and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_formula \<Sigma> G (book_witness_axiom G \<sigma> F c)"
  by (rule conjI[OF book_witness_axiom_language[OF rich predicate declared]
    book_lambda_I_witness_axiom[OF rich lambda_I]])

section \<open>Consistency of adjoining one fresh conditional witness\<close>

text \<open>
  Suppose S is consistent in Σ, each premise is a formula of Σ,
  F:σ→t is closed, and c∉Σσ. Then S∪{W(F,c)} is consistent
  in Σ[c:σ].

  The checked witness-choice theorem gives a consistent extension by
  either Fc or ¬∃σF. In the positive branch PC1 derives W(F,c).
  In the negative branch the checked explosion schema derives W(F,c).
  Adjoin this consequence without destroying consistency, then discard
  the extra branch assumption by taking a subset.

  S may be open and infinite. This proves consistency preservation for
  one axiom, not conservativity of that axiom, a simultaneous family
  theorem, witness completeness, or model existence. No H or semantic
  premise is used.
\<close>

theorem book_lambda_I_consistent_conditional_witness:
  assumes rich: "sg_rich G"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
    and fresh: "c \<notin> \<Sigma> \<sigma>"
  shows "book_lambda_I_consistent (book_add_constant \<Sigma> c \<sigma>) G
    (insert (book_witness_axiom G \<sigma> F c) S)"
proof -
  let ?\<Omega> = "book_add_constant \<Sigma> c \<sigma>"
  let ?E = "NApp (book_exists_const G \<sigma>) F"
  let ?Fc = "NApp F (NConst c \<sigma>)"
  let ?W = "book_witness_axiom G \<sigma> F c"
  have inclusion: "\<Sigma> \<tau> \<subseteq> ?\<Omega> \<tau>" for \<tau> by (rule book_add_constant_subset)
  have enlarged_language: "book_lambda_I_formula ?\<Omega> G A" if "A \<in> S" for A
    by (rule book_lambda_I_formula_signature_mono[OF language[OF that] inclusion])
  have premise_names: "named_in_signature \<Sigma> A" if "A \<in> S" for A
    by (rule book_lambda_I_formula_signature[OF language[OF that]])
  have enlarged_F: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G F (Arr \<sigma> Prop)"
    by (rule book_lambda_I_language_signature_mono[OF predicate inclusion])
  have witness: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G (NConst c \<sigma>) \<sigma>"
    by (simp add: book_language_const_iff book_add_constant_def)
  have Fc_language: "book_lambda_I_formula ?\<Omega> G ?Fc"
    by (rule conjI[OF book_language_App[OF enlarged_F witness]]; simp add: lambda_I)
  have E_language: "book_lambda_I_formula ?\<Omega> G ?E"
    by (rule book_lambda_I_exists_application_language[OF rich enlarged_F lambda_I])
  have W_language: "book_lambda_I_formula ?\<Omega> G ?W"
    by (rule book_lambda_I_witness_axiom_language[OF rich enlarged_F book_add_constant_member lambda_I])
  have transfer: "book_lambda_I_consistent ?\<Omega> G (insert ?W S)"
    if branch_consistent: "book_lambda_I_consistent ?\<Omega> G (insert B S)"
      and branch_language: "book_lambda_I_formula ?\<Omega> G B"
      and consequence: "book_lambda_I_derivable ?\<Omega> G (insert B S) ?W" for B
  proof -
    have all_language: "book_lambda_I_formula ?\<Omega> G A" if "A \<in> insert B S" for A
      using that branch_language enlarged_language by blast
    have larger_consistent: "book_lambda_I_consistent ?\<Omega> G (insert ?W (insert B S))"
      by (rule book_lambda_I_consistent_insert_consequence[OF branch_consistent consequence all_language])
    have smaller: "insert ?W S \<subseteq> insert ?W (insert B S)" by blast
    show ?thesis by (rule book_lambda_I_consistent_subset[OF larger_consistent smaller])
  qed
  have choice: "book_lambda_I_consistent ?\<Omega> G (insert ?Fc S) \<or>
    book_lambda_I_consistent ?\<Omega> G (insert (book_not G ?E) S)"
    by (rule book_lambda_I_closed_witness_choice[OF rich consistent premise_names predicate closed lambda_I fresh])
  show ?thesis
  proof (rule disjE[OF choice])
    assume positive_consistent: "book_lambda_I_consistent ?\<Omega> G (insert ?Fc S)"
    have positive: "book_lambda_I_derivable ?\<Omega> G (insert ?Fc S) ?Fc"
      by (rule book_lambda_I_derivable.Assumption[OF insertI1 Fc_language])
    have conditional: "book_lambda_I_derivable ?\<Omega> G (insert ?Fc S) (book_imp ?E ?Fc)"
      by (rule book_lambda_I_imp_weaken[OF positive E_language Fc_language])
    have consequence: "book_lambda_I_derivable ?\<Omega> G (insert ?Fc S) ?W"
      using conditional by (simp only: book_witness_axiom_def)
    show ?thesis by (rule transfer[OF positive_consistent Fc_language consequence])
  next
    assume negative_consistent: "book_lambda_I_consistent ?\<Omega> G (insert (book_not G ?E) S)"
    have negative_language: "book_lambda_I_formula ?\<Omega> G (book_not G ?E)"
      by (rule book_lambda_I_not_language[OF rich E_language])
    have negative: "book_lambda_I_derivable ?\<Omega> G (insert (book_not G ?E) S) (book_not G ?E)"
      by (rule book_lambda_I_derivable.Assumption[OF insertI1 negative_language])
    have schema: "book_lambda_I_derivable ?\<Omega> G {}
      (book_imp (book_not G ?E) (book_imp ?E ?Fc))"
      by (rule book_lambda_I_explosion_curried[OF rich E_language Fc_language])
    have schema_lifted: "book_lambda_I_derivable ?\<Omega> G (insert (book_not G ?E) S)
      (book_imp (book_not G ?E) (book_imp ?E ?Fc))"
      by (rule book_lambda_I_derivable_mono[OF schema empty_subsetI])
    have lifted: "book_lambda_I_derivable ?\<Omega> G (insert (book_not G ?E) S)
      (book_imp (book_not G ?E) ?W)"
      using schema_lifted by (simp only: book_witness_axiom_def)
    have consequence: "book_lambda_I_derivable ?\<Omega> G (insert (book_not G ?E) S) ?W"
      by (rule book_lambda_I_derivable.MP[OF negative lifted W_language])
    show ?thesis by (rule transfer[OF negative_consistent negative_language consequence])
  qed
qed

end
