theory Bacon_Source_PC_Translation
  imports Bacon_Source_Formula_Conversion
begin

section \<open>A literal PC instance converts to its expanded template\<close>

text \<open>
  PC includes each propositional tautology instance (Bacon–Dorr Figure 2).
  Figure 1's → and ↔ remain their literal λ-definitions on the source
  side.  Their translations convert to material bodies using only
  PNeg, PConj, and PDisj.

  Isabelle representation: induction on the propositional template combines
  the guarded connective-expansion lemmas.  The atoms may be arbitrary
  formulas in the declared source language, including open formulas.

  Status: signature-indexed conversion of the literal instance, followed
  below by target H proof transport.  No independent source H relation,
  proof reflection, or completeness transport is supplied by this leaf.
\<close>

lemma source_conversion_refl_language:
  assumes "pterm_in_language \<Sigma> \<Gamma> M \<tau>"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M M"
  by (rule pbeta_eta_equiv_in_signature.Refl[
    OF conjunct1[OF assms[unfolded pterm_in_language_def]]
    conjunct2[OF assms[unfolded pterm_in_language_def]]])

lemma paper_prop_instance_conversion:
  assumes atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P))
    (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
  using atoms
proof (induction P)
  case (SPAtom a)
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
    by (rule SPAtom.prems) simp
  note refl = source_conversion_refl_language[OF iffD2[OF paper_to_pterm_language_iff al]]
  show ?case using refl by simp
next
  case (SPNot P)
  have p: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
    by (rule SPNot.IH; rule SPNot.prems; simp_all)
  show ?case using paper_not_expansion[OF p]
    by (simp only: paper_prop_instance.simps paper_expanded_prop.simps)
next
  case (SPAnd P Q)
  have p: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
    by (rule SPAnd.IH(1); rule SPAnd.prems; simp_all)
  have q: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v Q)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) Q)"
    by (rule SPAnd.IH(2); rule SPAnd.prems; simp_all)
  show ?case using paper_and_expansion[OF p q]
    by (simp only: paper_prop_instance.simps paper_expanded_prop.simps)
next
  case (SPOr P Q)
  have p: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
    by (rule SPOr.IH(1); rule SPOr.prems; simp_all)
  have q: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v Q)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) Q)"
    by (rule SPOr.IH(2); rule SPOr.prems; simp_all)
  show ?case using paper_or_expansion[OF p q]
    by (simp only: paper_prop_instance.simps paper_expanded_prop.simps)
next
  case (SPImp P Q)
  have p: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
    by (rule SPImp.IH(1); rule SPImp.prems; simp_all)
  have q: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v Q)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) Q)"
    by (rule SPImp.IH(2); rule SPImp.prems; simp_all)
  show ?case using paper_imp_expansion[OF p q]
    by (simp only: paper_prop_instance.simps paper_expanded_prop.simps)
next
  case (SPIff P Q)
  have p: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
    by (rule SPIff.IH(1); rule SPIff.prems; simp_all)
  have q: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v Q)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) Q)"
    by (rule SPIff.IH(2); rule SPIff.prems; simp_all)
  show ?case using paper_iff_expansion[OF p q]
    by (simp only: paper_prop_instance.simps paper_expanded_prop.simps)
qed

subsection \<open>Target H proves the literal translation of every paper PC instance\<close>

text \<open>
  If A is a PC instance in ℒ(Σ), then ⊢H ⟦A⟧.
  This uses target PC for the expanded template and Figure 2's contextual
  β/η biconditionals to return to the literal translation.

  Isabelle representation: paper_PC_atoms recovers the typed, in-signature
  atom instances from the unchanged paper_PC predicate.  No extra guard is
  silently added to the source PC definition.

  Status: one source axiom-family preservation result, not full H transport.
\<close>

theorem paper_PC_translation:
  assumes pc: "paper_PC \<Sigma> \<Gamma> A"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm A)"
proof -
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and eq: "A = paper_prop_instance v P"
    and atoms: "\<forall>a\<in>sprop_atoms P. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
    by (rule paper_PC_atoms[OF pc]; rule that; assumption)
  have conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_prop_instance v P)) (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
    by (rule paper_prop_instance_conversion; rule bspec[OF atoms]; assumption)
  have expanded: "pH_proves \<Sigma> \<Gamma> (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
  proof (rule paper_expanded_prop_PC[OF taut])
    fix a
    assume member: "a \<in> sprop_atoms P"
    have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
      by (rule bspec[OF atoms member])
    show "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm (v a)) Prop"
      by (rule iffD2[OF paper_to_pterm_language_iff al])
  qed
  show ?thesis using source_pH_conversion_backward[OF conv expanded] by (simp only: eq)
qed

end
