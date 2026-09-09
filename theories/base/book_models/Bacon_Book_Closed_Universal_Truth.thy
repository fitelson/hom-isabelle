theory Bacon_Book_Closed_Universal_Truth
  imports Bacon_Book_Closed_Universal_Instances Bacon_Book_Closed_Quantifier_Duality
    Bacon_Book_Closed_Witness_Completeness
begin

section \<open>Applying the literal negative predicate to a closed argument\<close>

lemma book_negated_predicate_closed_application_beta:
  assumes predicate_closed: "named_fv F = {}"
    and argument_closed: "named_fv A = {}"
  shows "named_beta_contract (NApp (book_negated_predicate G \<sigma> F) A)
    (book_not G (NApp F A))"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?B = "book_not G (NApp F (NVar ?y))"
  have free_for: "named_free_for A ?y ?B"
    by (rule book_exists_closed_free_for[OF argument_closed])
  have predicate_fresh: "?y \<notin> named_fv F" by (simp add: predicate_closed)
  have predicate_fixed: "named_subst ?y A F = F"
    by (rule named_subst_fresh[OF predicate_fresh])
  have operator_fresh: "?y \<notin> named_fv (book_not_const G)"
    by (simp add: book_not_const_closed)
  have operator_fixed: "named_subst ?y A (book_not_const G) = book_not_const G"
    by (rule named_subst_fresh[OF operator_fresh])
  have substitution: "named_subst ?y A ?B = book_not G (NApp F A)"
    by (simp add: book_not_def predicate_fixed operator_fixed)
  have raw: "named_beta_contract (NApp (NLam ?y ?B) A) (named_subst ?y A ?B)"
    by (rule named_beta_contract.beta[OF free_for])
  show ?thesis using raw by (simp only: book_negated_predicate_def substitution)
qed

section \<open>Closed universal membership and all closed instances\<close>

text \<open>
  For closed F:σ→t, ∀σF∈M iff FA∈M for every closed Σ-term A:σ,
  provided M is maximal closed-consistent and has closed constant witnesses.
  Source role: the universal clause of the term-quotient truth argument,
  Bacon p.321, explicitly repaired to use closed representatives.

  UI gives the forward direction. For the converse use witness
  completeness on Q=λy.¬Fy. Its negative-existential alternative yields
  ∀σF by the proved closed duality. Its witness alternative Qc yields
  ¬Fc by literal β and contradicts the assumed positive instance Fc.
  No valuation or model premise is used, and no all-open decision
  property is attributed to M.
\<close>

theorem book_closed_maximal_forall_iff:
  assumes rich: "sg_rich G"
    and maximal: "book_closed_maximal_extension \<Sigma> G S M"
    and witnesses: "book_closed_constant_witness_complete \<Sigma> G M"
    and predicate: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
  shows "NApp (NLogical (SBAll \<sigma>)) F \<in> M \<longleftrightarrow>
    (\<forall>A\<in>book_closed_terms \<Sigma> G \<sigma>. NApp F A \<in> M)"
proof -
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    by (rule book_closed_terms_language[OF predicate])
  have fc: "named_fv F = {}" by (rule book_closed_terms_closed[OF predicate])
  show ?thesis
  proof
    assume universal: "NApp (NLogical (SBAll \<sigma>)) F \<in> M"
    show "\<forall>A\<in>book_closed_terms \<Sigma> G \<sigma>. NApp F A \<in> M"
    proof (rule ballI)
      fix A
      assume argument: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
      show "NApp F A \<in> M"
        by (rule book_closed_maximal_forall_instance[OF maximal predicate argument universal])
    qed
  next
    assume instances: "\<forall>A\<in>book_closed_terms \<Sigma> G \<sigma>. NApp F A \<in> M"
    let ?Q = "book_negated_predicate G \<sigma> F"
    let ?E = "NApp (book_exists_const G \<sigma>) ?Q"
    let ?U = "NApp (NLogical (SBAll \<sigma>)) F"
    have ql: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?Q (Arr \<sigma> Prop)"
      by (rule book_negated_predicate_language[OF rich fl])
    have qc: "named_fv ?Q = {}" by (rule book_negated_predicate_closed[OF fc])
    have choice: "book_not G ?E \<in> M \<or> (\<exists>c\<in>\<Sigma> \<sigma>. NApp ?Q (NConst c \<sigma>) \<in> M)"
      using witnesses ql qc unfolding book_closed_constant_witness_complete_def by blast
    show "?U \<in> M"
    proof (rule disjE[OF choice])
      assume negative_member: "book_not G ?E \<in> M"
      have negative_language: "book_theory_formula \<Sigma> G (book_not G ?E)"
        by (rule book_not_language[OF rich book_exists_application_language[OF rich ql]])
      have negative: "book_theory_derivable \<Sigma> G M (book_not G ?E)"
        by (rule book_theory_derivable.Assumption[OF negative_member negative_language])
      have ul: "book_theory_formula \<Sigma> G ?U"
        by (rule book_language_App[OF book_all_operator_language fl])
      have uc: "named_fv ?U = {}" by (simp add: fc)
      have dual: "book_theory_derivable \<Sigma> G {} (book_imp (book_not G ?E) ?U)"
        by (rule book_theory_closed_forall_dual[OF rich fl fc])
      have lifted: "book_theory_derivable \<Sigma> G M (book_imp (book_not G ?E) ?U)"
        by (rule book_theory_derivable_mono[OF dual empty_subsetI])
      have derived: "book_theory_derivable \<Sigma> G M ?U"
        by (rule book_theory_derivable.MP[OF negative lifted ul])
      show ?thesis by (rule book_closed_maximal_derivable_member[OF maximal ul uc derived])
    next
      assume witness: "\<exists>c\<in>\<Sigma> \<sigma>. NApp ?Q (NConst c \<sigma>) \<in> M"
      obtain c where declared: "c \<in> \<Sigma> \<sigma>" and member: "NApp ?Q (NConst c \<sigma>) \<in> M"
        using witness by blast
      let ?a = "NConst c \<sigma>"
      have al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?a \<sigma>"
        by (simp add: book_language_const_iff declared)
      have ac: "named_fv ?a = {}" by simp
      have argument: "?a \<in> book_closed_terms \<Sigma> G \<sigma>"
        by (rule book_closed_termsI[OF al ac])
      have positive_member: "NApp F ?a \<in> M" by (rule bspec[OF instances argument])
      have instance_language: "book_theory_formula \<Sigma> G (NApp F ?a)"
        by (rule book_language_App[OF fl al])
      have instance_closed: "named_fv (NApp F ?a) = {}" by (simp add: fc)
      have negative_language: "book_theory_formula \<Sigma> G (book_not G (NApp F ?a))"
        by (rule book_not_language[OF rich instance_language])
      have negative_closed: "named_fv (book_not G (NApp F ?a)) = {}"
        by (simp only: book_not_fv instance_closed)
      have redex_language: "book_theory_formula \<Sigma> G (NApp ?Q ?a)"
        by (rule book_language_App[OF ql al])
      have redex: "book_theory_derivable \<Sigma> G M (NApp ?Q ?a)"
        by (rule book_theory_derivable.Assumption[OF member redex_language])
      have contraction: "named_beta_contract (NApp ?Q ?a) (book_not G (NApp F ?a))"
        by (rule book_negated_predicate_closed_application_beta[OF fc ac])
      have beta: "book_theory_derivable \<Sigma> G M
        (book_imp (NApp ?Q ?a) (book_not G (NApp F ?a)))"
        by (rule book_theory_derivable.Beta[OF redex_language negative_language],
          rule disjI1, rule named_compatible_step.root, rule contraction)
      have negative: "book_theory_derivable \<Sigma> G M (book_not G (NApp F ?a))"
        by (rule book_theory_derivable.MP[OF redex beta negative_language])
      have negative_member: "book_not G (NApp F ?a) \<in> M"
        by (rule book_closed_maximal_derivable_member[OF maximal negative_language negative_closed negative])
      have absent: "NApp F ?a \<notin> M"
        by (rule iffD1[OF book_closed_maximal_negation_iff[
          OF rich maximal instance_language instance_closed] negative_member])
      show ?thesis by (rule FalseE, rule notE[OF absent positive_member])
    qed
  qed
qed

end
