theory Bacon_Book_Lambda_I_Closed_Quantifier_Duality
  imports Bacon_Book_Lambda_I_Quantifier_Proof_Basics Bacon_Book_Lambda_I_Universal_Closure
begin

section \<open>The literal negative predicate\<close>

text \<open>
  Put y=book_exists_argument_name G σ and Q=λy.¬Fy.
  This is actual named syntax, not a primitive complement operation.
  When F:σ→t is closed, Q is also a typed closed predicate.
  Source: the Table 4.1 existential definition and the quantifier
  reasoning needed for the term valuation on pp.320–321.
\<close>

definition book_lambda_I_negated_predicate ::
  "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_lambda_I_negated_predicate G \<sigma> F =
    NLam (book_exists_argument_name G \<sigma>)
      (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>))))"

lemma book_lambda_I_negated_predicate_relevant:
  assumes lambda_I: "book_lambda_I F"
  shows "book_lambda_I (book_lambda_I_negated_predicate G \<sigma> F)"
  unfolding book_lambda_I_negated_predicate_def book_not_def
  by (simp add: book_lambda_I_not_const lambda_I)

lemma book_lambda_I_negated_predicate_language:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and lambda_I: "book_lambda_I F"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_lambda_I_negated_predicate G \<sigma> F) (Arr \<sigma> Prop)"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  have ytype: "G ?y = \<sigma>" by (rule book_exists_argument_name_type[OF rich])
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) \<sigma>"
    by (simp only: book_language_var_iff ytype)
  have Fy: "book_lambda_I_formula \<Sigma> G (NApp F (NVar ?y))"
    by (rule conjI[OF book_language_App[OF predicate variable]]; simp add: lambda_I)
  have body: "book_lambda_I_formula \<Sigma> G (book_not G (NApp F (NVar ?y)))"
    by (rule book_lambda_I_not_language[OF rich Fy])
  have abstraction: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLam ?y (book_not G (NApp F (NVar ?y)))) (Arr (G ?y) Prop)"
    by (rule book_language_Lam[OF conjunct1[OF body]])
  show ?thesis using abstraction by (simp only: book_lambda_I_negated_predicate_def ytype)
qed

lemma book_lambda_I_negated_predicate_closed:
  assumes closed: "named_fv F = {}"
  shows "named_fv (book_lambda_I_negated_predicate G \<sigma> F) = {}"
  by (simp add: book_lambda_I_negated_predicate_def book_not_fv closed)

lemma book_lambda_I_negated_predicate_self_beta:
  "named_compatible_step named_beta_contract
    (book_not G (NApp (book_lambda_I_negated_predicate G \<sigma> F) (NVar (book_exists_argument_name G \<sigma>))))
    (book_not G (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>)))))"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?B = "book_not G (NApp F (NVar ?y))"
  have raw: "named_beta_contract (NApp (NLam ?y ?B) (NVar ?y)) (named_subst ?y (NVar ?y) ?B)"
    by (rule named_beta_contract.beta, rule named_free_for_same_variable)
  have contraction: "named_beta_contract (NApp (book_lambda_I_negated_predicate G \<sigma> F) (NVar ?y)) ?B"
    using raw by (simp only: book_lambda_I_negated_predicate_def named_subst_same_variable)
  have inner_step: "named_compatible_step named_beta_contract
    (NApp (book_lambda_I_negated_predicate G \<sigma> F) (NVar ?y)) ?B"
    by (rule named_compatible_step.root; rule contraction)
  have outer_step: "named_compatible_step named_beta_contract
    (NApp (book_not_const G) (NApp (book_lambda_I_negated_predicate G \<sigma> F) (NVar ?y)))
    (NApp (book_not_const G) ?B)"
    by (rule named_compatible_step.App_right[OF inner_step])
  show ?thesis using outer_step by (simp only: book_not_def)
qed

section \<open>Negated existential application gives its universal negative body\<close>

lemma book_lambda_I_not_exists_all_not:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G Q (Arr \<sigma> Prop)"
    and closed: "named_fv Q = {}" and lambda_I: "book_lambda_I Q"
    and negative: "book_lambda_I_derivable \<Sigma> G S (book_not G (NApp (book_exists_const G \<sigma>) Q))"
  shows "book_lambda_I_derivable \<Sigma> G S
    (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp Q (NVar (book_exists_argument_name G \<sigma>)))))"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?E = "NApp (book_exists_const G \<sigma>) Q"
  let ?P = "book_all G ?y (book_not G (NApp Q (NVar ?y)))"
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) \<sigma>"
    by (simp only: book_language_var_iff book_exists_argument_name_type[OF rich])
  have Qy: "book_lambda_I_formula \<Sigma> G (NApp Q (NVar ?y))"
    by (rule conjI[OF book_language_App[OF predicate variable]]; simp add: lambda_I)
  have occurs: "?y \<in> named_fv (book_not G (NApp Q (NVar ?y)))" unfolding book_not_def by simp
  have pl: "book_lambda_I_formula \<Sigma> G ?P"
    by (rule book_lambda_I_all_language[OF book_lambda_I_not_language[OF rich Qy] occurs])
  have pc: "named_fv ?P = {}" by (simp add: book_all_fv book_not_fv closed)
  have el: "book_lambda_I_formula \<Sigma> G ?E"
    by (rule book_lambda_I_exists_application_language[OF rich predicate lambda_I])
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have contradiction: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S) (book_bottom G)"
  proof -
    have notP: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S) (book_not G ?P)"
      by (rule book_lambda_I_derivable.Assumption[OF insertI1 book_lambda_I_not_language[OF rich pl]])
    have folding: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S) (book_imp (book_not G ?P) ?E)"
      by (rule book_lambda_I_exists_fold[OF rich predicate closed lambda_I])
    have positive_E: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S) ?E"
      by (rule book_lambda_I_derivable.MP[OF notP folding el])
    have negative_E: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S) (book_not G ?E)"
      by (rule book_lambda_I_derivable_mono[OF negative subset_insertI])
    have unfolding_step: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S)
      (book_imp (book_not G ?E) (book_imp ?E (book_bottom G)))"
      by (rule book_lambda_I_not_unfold[OF rich el])
    have conditional: "book_lambda_I_derivable \<Sigma> G (insert (book_not G ?P) S) (book_imp ?E (book_bottom G))"
      by (rule book_lambda_I_derivable.MP[OF negative_E unfolding_step book_lambda_I_imp_language[OF el bottom]])
    show ?thesis by (rule book_lambda_I_derivable.MP[OF positive_E conditional bottom])
  qed
  show ?thesis by (rule book_lambda_I_closed_refutation[OF rich pl pc contradiction])
qed

section \<open>The closed-predicate quantifier duality implication\<close>

text \<open>
  ∅ ⊢ ¬∃σ(λy.¬Fy)→∀σF for closed F:σ→t.
  Under the closed antecedent, obtain ∀y.¬Qy. UI at y and the
  literal β step above give ¬¬Fy. Double-negation elimination and
  theory generalization give ∀y.Fy; η gives ∀σF. Finally discharge
  the CLOSED antecedent. No open-predicate version or model clause
  is inferred from this proof.
\<close>

theorem book_lambda_I_closed_forall_dual:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
  shows "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_not G (NApp (book_exists_const G \<sigma>) (book_lambda_I_negated_predicate G \<sigma> F)))
      (NApp (NLogical (SBAll \<sigma>)) F))"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?Q = "book_lambda_I_negated_predicate G \<sigma> F"
  let ?C = "book_not G (NApp (book_exists_const G \<sigma>) ?Q)"
  let ?B = "NApp F (NVar ?y)"
  let ?P = "book_all G ?y (book_not G (NApp ?Q (NVar ?y)))"
  have ql: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?Q (Arr \<sigma> Prop)"
    by (rule book_lambda_I_negated_predicate_language[OF rich predicate lambda_I])
  have qc: "named_fv ?Q = {}" by (rule book_lambda_I_negated_predicate_closed[OF closed])
  have qr: "book_lambda_I ?Q" by (rule book_lambda_I_negated_predicate_relevant[OF lambda_I])
  have cl: "book_lambda_I_formula \<Sigma> G ?C"
    by (rule book_lambda_I_not_language[OF rich book_lambda_I_exists_application_language[OF rich ql qr]])
  have cc: "named_fv ?C = {}" by (simp only: book_not_fv book_exists_application_fv qc)
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) \<sigma>"
    by (simp only: book_language_var_iff book_exists_argument_name_type[OF rich])
  have bl: "book_lambda_I_formula \<Sigma> G ?B"
    by (rule conjI[OF book_language_App[OF predicate variable]]; simp add: lambda_I)
  have Qy: "book_lambda_I_formula \<Sigma> G (NApp ?Q (NVar ?y))"
    by (rule conjI[OF book_language_App[OF ql variable]]; simp add: qr)
  have nql: "book_lambda_I_formula \<Sigma> G (book_not G (NApp ?Q (NVar ?y)))"
    by (rule book_lambda_I_not_language[OF rich Qy])
  have y_occurs_Q: "?y \<in> named_fv (book_not G (NApp ?Q (NVar ?y)))" unfolding book_not_def by simp
  have y_occurs_B: "?y \<in> named_fv ?B" by simp
  have nnbl: "book_lambda_I_formula \<Sigma> G (book_not G (book_not G ?B))"
    by (rule book_lambda_I_not_language[OF rich book_lambda_I_not_language[OF rich bl]])
  have assumption_C: "book_lambda_I_derivable \<Sigma> G {?C} ?C"
    by (rule book_lambda_I_derivable.Assumption[OF insertI1 cl])
  have universal_negative: "book_lambda_I_derivable \<Sigma> G {?C} ?P"
    by (rule book_lambda_I_not_exists_all_not[OF rich ql qc qr assumption_C])
  have negative_instance: "book_lambda_I_derivable \<Sigma> G {?C} (book_not G (NApp ?Q (NVar ?y)))"
    by (rule book_lambda_I_all_elim_variable[OF universal_negative nql y_occurs_Q])
  have beta: "book_lambda_I_derivable \<Sigma> G {?C}
    (book_imp (book_not G (NApp ?Q (NVar ?y))) (book_not G (book_not G ?B)))"
    by (rule book_lambda_I_derivable.Beta[OF nql nnbl], rule disjI1,
      rule book_lambda_I_negated_predicate_self_beta)
  have double_negative: "book_lambda_I_derivable \<Sigma> G {?C} (book_not G (book_not G ?B))"
    by (rule book_lambda_I_derivable.MP[OF negative_instance beta nnbl])
  have positive: "book_lambda_I_derivable \<Sigma> G {?C} ?B"
    by (rule book_lambda_I_double_negation_elim[OF rich bl double_negative])
  have generalized: "book_lambda_I_derivable \<Sigma> G {?C} (book_all G ?y ?B)"
    by (rule book_lambda_I_generalize[OF rich positive y_occurs_B])
  have eta: "book_lambda_I_derivable \<Sigma> G {?C}
    (book_imp (book_all G ?y ?B) (NApp (NLogical (SBAll \<sigma>)) F))"
    by (rule conjunct2[OF book_lambda_I_forall_eta_pair[OF rich predicate closed lambda_I]])
  have target_language: "book_lambda_I_formula \<Sigma> G (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule conjI[OF book_language_App[OF book_all_operator_language predicate]]; simp add: lambda_I)
  have target: "book_lambda_I_derivable \<Sigma> G {?C} (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule book_lambda_I_derivable.MP[OF generalized eta target_language])
  show ?thesis by (rule book_lambda_I_closed_deduction[OF rich cl cc target])
qed

end
