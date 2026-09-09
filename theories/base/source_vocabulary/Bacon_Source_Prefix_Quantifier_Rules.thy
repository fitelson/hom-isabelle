theory Bacon_Source_Prefix_Quantifier_Rules
  imports Bacon_Source_Prefix_Preservation Bacon_Source_Generalization_Translation
begin

section \<open>Supporting the selected variable in Gen and Inst\<close>

text \<open>
  A source Gen or Inst step may bind a variable absent from the conclusion's
  other terms. Its translation must nevertheless make that variable
  available in the finite frame. We enlarge the support bound to include
  its index n, then apply the checked finite-frame rule translation.
  Source: Bacon–Dorr Figure 2 and the discussion of H⁻, pp.7–9.

  Isabelle representation: max N (Suc n) supports both the earlier proof
  and the chosen variable. Typing of P,Q is recovered from the translated
  premise's language membership. No completeness or model argument enters
  either preservation theorem.
\<close>

theorem paper_target_eventual_Gen:
  assumes premise: "paper_target_eventual \<Sigma> G (paper_imp P Q)"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> sfv P"
  shows "paper_target_eventual \<Sigma> G
    (paper_imp P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q))))"
proof -
  obtain N where earlier: "\<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m)
    (paper_to_pterm (paper_imp P Q))"
    using premise unfolding paper_target_eventual_def by (elim exE)
  show ?thesis unfolding paper_target_eventual_def
  proof (rule exI[where x="max N (Suc n)"], intro allI impI)
    fix m
    assume bound: "max N (Suc n) \<le> m"
    have prior: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm (paper_imp P Q))"
      using earlier bound by auto
    have below: "n < m" using bound by arith
    have index: "lookup (source_prefix G m) n = Some \<sigma>"
      using source_prefix_lookup[OF below, where G=G] by (simp only: variable)
    show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm
      (paper_imp P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q)))))"
      by (rule paper_Gen_translation[OF index paper_target_implication_languages(1)[OF prior]
        paper_target_implication_languages(2)[OF prior] fresh prior])
  qed
qed

theorem paper_target_eventual_Inst:
  assumes premise: "paper_target_eventual \<Sigma> G (paper_imp P Q)"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> sfv Q"
  shows "paper_target_eventual \<Sigma> G
    (paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))) Q)"
proof -
  obtain N where earlier: "\<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m)
    (paper_to_pterm (paper_imp P Q))"
    using premise unfolding paper_target_eventual_def by (elim exE)
  show ?thesis unfolding paper_target_eventual_def
  proof (rule exI[where x="max N (Suc n)"], intro allI impI)
    fix m
    assume bound: "max N (Suc n) \<le> m"
    have prior: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm (paper_imp P Q))"
      using earlier bound by auto
    have below: "n < m" using bound by arith
    have index: "lookup (source_prefix G m) n = Some \<sigma>"
      using source_prefix_lookup[OF below, where G=G] by (simp only: variable)
    show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm
      (paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))) Q))"
      by (rule paper_Inst_translation[OF index paper_target_implication_languages(1)[OF prior]
        paper_target_implication_languages(2)[OF prior] fresh prior])
  qed
qed

end
