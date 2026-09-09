theory Bacon_Source_Set_Preservation
  imports Bacon_Source_Local_Deduction Bacon_Source_Target_Local_Conversion
    Bacon_Source_Global_Proof_Preservation
begin

section \<open>Finite variable support for source consequence proofs\<close>

text \<open>
  A local source derivation from S translates into a target derivation
  from the image of S in every sufficiently large finite variable prefix.
  Assumptions and theorem leaves supply their finite bounds; MP takes the
  maximum. The logical rule acting on local assumptions is MP only.
  Source role: finite proofs from sentence sets in Bacon–Dorr Theorem 3.2.

  Isabelle representation: the assumption set may be infinite. Individual
  used assumptions are language-guarded; this intermediate theorem does not
  require every member of S to fit into a single finite frame. The later
  closed-set theorem imposes the necessary closed-language condition.
\<close>

definition paper_target_set_eventual ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_term set \<Rightarrow> 'c paper_term \<Rightarrow> bool" where
  "paper_target_set_eventual \<Sigma> G S A \<longleftrightarrow>
    (\<exists>N. \<forall>m\<ge>N. pH_set_derivable \<Sigma> (source_prefix G m)
      (image paper_to_pterm S) (paper_to_pterm A))"

lemma paper_target_local_implication_languages:
  assumes derivation: "pH_set_derivable \<Sigma> \<Gamma> T (paper_to_pterm (paper_imp A B))"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
proof -
  have target: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm (paper_imp A B)) Prop"
    unfolding pterm_in_language_def
    by (rule conjI[OF pH_set_formula[OF derivation] pH_set_in_signature[OF derivation]])
  have source: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp A B) Prop"
    by (rule iffD1[OF paper_to_pterm_language_iff target])
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    using source by (auto simp: sterm_in_language_def paper_imp_type_iff)
qed

theorem paper_global_derivable_target_eventual:
  assumes derivation: "paper_global_derivable \<Sigma> G S A"
  shows "paper_target_set_eventual \<Sigma> G S A"
  using derivation
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A S)
  show ?case unfolding paper_target_set_eventual_def
  proof (rule exI[where x="source_free_bound A"], intro allI impI)
    fix m
    assume bound: "source_free_bound A \<le> m"
    have source: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G m) A Prop"
      by (rule source_language_in_prefix[OF Assumption.hyps(2) bound])
    have target: "pterm_in_language \<Sigma> (source_prefix G m) (paper_to_pterm A) Prop"
      by (rule iffD2[OF paper_to_pterm_language_iff source])
    have member: "paper_to_pterm A \<in> image paper_to_pterm S" by (rule imageI[OF Assumption.hyps(1)])
    show "pH_set_derivable \<Sigma> (source_prefix G m) (image paper_to_pterm S) (paper_to_pterm A)"
      by (rule pH_set_Assumption[OF member conjunct1[OF target[unfolded pterm_in_language_def]]
        conjunct2[OF target[unfolded pterm_in_language_def]]])
  qed
next
  case (Theorem A S)
  have eventual: "paper_target_eventual \<Sigma> G A"
    by (rule paper_global_H_target_eventual[OF Theorem.hyps])
  obtain N where proofs: "\<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
    using eventual unfolding paper_target_eventual_def by (elim exE)
  show ?case unfolding paper_target_set_eventual_def
  proof (rule exI[where x=N], intro allI impI)
    fix m
    assume "N \<le> m"
    then have theorem_H: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)" using proofs by auto
    show "pH_set_derivable \<Sigma> (source_prefix G m) (image paper_to_pterm S) (paper_to_pterm A)"
      by (rule pH_set_Theorem[OF theorem_H])
  qed
next
  case (MP S A B)
  obtain N where left: "\<forall>m\<ge>N. pH_set_derivable \<Sigma> (source_prefix G m)
    (image paper_to_pterm S) (paper_to_pterm A)"
    using MP.IH(1) unfolding paper_target_set_eventual_def by (elim exE)
  obtain K where right: "\<forall>m\<ge>K. pH_set_derivable \<Sigma> (source_prefix G m)
    (image paper_to_pterm S) (paper_to_pterm (paper_imp A B))"
    using MP.IH(2) unfolding paper_target_set_eventual_def by (elim exE)
  show ?case unfolding paper_target_set_eventual_def
  proof (rule exI[where x="max N K"], intro allI impI)
    fix m
    assume bound: "max N K \<le> m"
    have first: "pH_set_derivable \<Sigma> (source_prefix G m) (image paper_to_pterm S) (paper_to_pterm A)"
      using left bound by auto
    have second: "pH_set_derivable \<Sigma> (source_prefix G m) (image paper_to_pterm S)
      (paper_to_pterm (paper_imp A B))" using right bound by auto
    show "pH_set_derivable \<Sigma> (source_prefix G m) (image paper_to_pterm S) (paper_to_pterm B)"
      by (rule paper_set_MP_translation[OF paper_target_local_implication_languages(1)[OF second]
        paper_target_local_implication_languages(2)[OF second] first second])
  qed
qed

end
