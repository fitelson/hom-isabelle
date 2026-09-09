theory Bacon_Source_Relational_H_Theory_Boxed_Consequences
  imports Bacon_Source_Relational_H_Theory_Boxed_Lists
    Bacon_Source_Relational_H_Theory_Necessitation Bacon_Source_Relational_Language_Inversion
begin

section \<open>Local consequences of premises that imply their own necessities\<close>

text \<open>
  Suppose T contains A→□A for every additional premise A∈Δ.
  If T∪Δ ⊢H P, then T∪Δ ⊢H □P. Finite support selects
  finitely many additional premises. Discharge them into an implication
  in T, necessitate THAT theorem in the original T, then use the
  previously proved iterated K calculation with the boxed premises.

  Source: the finite-premise modal argument in p.52 n.73. The explicit
  premise condition is essential; this is not unrestricted Necessitation
  for local consequence. T and Δ may be infinite.
\<close>

theorem paper_R_H_theory_necessitate_local_consequence:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T"
    and premise_boxes: "\<And>A. A \<in> \<Delta> \<Longrightarrow> named_paper_imp G A (paper_R_named_box G A) \<in> T"
    and derivation: "paper_R_named_derivable \<Sigma> G (T \<union> \<Delta>) P"
  shows "paper_R_named_derivable \<Sigma> G (T \<union> \<Delta>) (paper_R_named_box G P)"
proof -
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule paper_R_named_derivable_language[OF derivation])
  obtain U where finite: "finite U" and support: "U \<subseteq> T \<union> \<Delta>"
    and finite_proof: "paper_R_named_derivable \<Sigma> G U P"
    using paper_R_named_derivable_finite_support[OF derivation] by blast
  have finite_extra: "finite (U \<inter> \<Delta>)" using finite by simp
  obtain As where entries: "set As = U \<inter> \<Delta>"
    using finite_distinct_list[OF finite_extra] by blast
  have extra: "set As \<subseteq> \<Delta>" by (simp only: entries; rule Int_lower2)
  have covered: "U \<subseteq> set As \<union> T" using support by (simp only: entries; blast)
  have reduced: "paper_R_named_derivable \<Sigma> G (set As \<union> T) P"
    by (rule paper_R_named_derivable_mono[OF finite_proof covered])
  have entry_language: "paper_R_in_language \<Sigma> G A Prop" if member: "A \<in> set As" for A
  proof -
    have premise: "named_paper_imp G A (paper_R_named_box G A) \<in> T"
      by (rule premise_boxes[OF subsetD[OF extra member]])
    have language: "paper_R_in_language \<Sigma> G (named_paper_imp G A (paper_R_named_box G A)) Prop"
      by (rule paper_R_H_theory_language[OF theory_h premise])
    show ?thesis by (rule conjunct1[OF paper_R_imp_language_operands[OF rich language]])
  qed
  have formulas: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As"
    using entry_language by (simp add: list_all_iff)
  have discharged: "paper_R_named_derivable \<Sigma> G T (paper_R_imp_list G As P)"
    by (rule paper_R_named_derivable_list_deduction[OF rich formulas reduced])
  have original_theorem: "paper_R_imp_list G As P \<in> T"
    by (rule paper_R_H_theory_local_consequences[OF theory_h discharged subset_refl])
  have boxed_theorem: "paper_R_named_box G (paper_R_imp_list G As P) \<in> T"
    by (rule paper_R_H_theory_necessitation[OF rich theory_h pe original_theorem])
  have boxed_language: "paper_R_in_language \<Sigma> G (paper_R_named_box G (paper_R_imp_list G As P)) Prop"
    by (rule paper_R_H_theory_language[OF theory_h boxed_theorem])
  have boxed_local: "paper_R_named_derivable \<Sigma> G (T \<union> \<Delta>)
      (paper_R_named_box G (paper_R_imp_list G As P))"
    by (rule paper_R_named_derivable.Assumption[OF UnI1[OF boxed_theorem] boxed_language])
  have every_boxed: "paper_R_named_derivable \<Sigma> G (T \<union> \<Delta>) (paper_R_named_box G A)"
    if member: "A \<in> set As" for A
  proof -
    have in_extra: "A \<in> \<Delta>" by (rule subsetD[OF extra member])
    have al: "paper_R_in_language \<Sigma> G A Prop" by (rule entry_language[OF member])
    have implication_member: "named_paper_imp G A (paper_R_named_box G A) \<in> T"
      by (rule premise_boxes[OF in_extra])
    have implication_language: "paper_R_in_language \<Sigma> G (named_paper_imp G A (paper_R_named_box G A)) Prop"
      by (rule paper_R_H_theory_language[OF theory_h implication_member])
    have implication_local: "paper_R_named_derivable \<Sigma> G (T \<union> \<Delta>)
        (named_paper_imp G A (paper_R_named_box G A))"
      by (rule paper_R_named_derivable.Assumption[OF UnI1[OF implication_member] implication_language])
    have assumed: "paper_R_named_derivable \<Sigma> G (T \<union> \<Delta>) A"
      by (rule paper_R_named_derivable.Assumption[OF UnI2[OF in_extra] al])
    show ?thesis by (rule paper_R_named_derivable.MP[OF assumed implication_local paper_R_named_box_language[OF rich al]])
  qed
  show ?thesis by (rule paper_R_H_theory_boxed_list_MP[
    OF rich theory_h pe Un_upper1 formulas pl boxed_local every_boxed])
qed

end
