theory Bacon_Source_Local_Conversion_Transport
  imports Bacon_Source_Local_Deduction Bacon_Source_Variable_Embedding
    Bacon_Source_Renaming_Conversion
begin

section \<open>Literal biconditionals transport local source derivations\<close>

text \<open>
  S ⊢H A and S ⊢H A ↔ B imply S ⊢H B, and conversely for B.
  Source: PC and MP in Bacon–Dorr Figure 2, p.8, using Figure 1's literal
  definitions of implication and biconditional.

  Isabelle representation.  A source PC theorem is inserted as a Theorem
  leaf of paper_global_derivable, followed by two local MP inferences.
  A global equivalence of theoremhood predicates would not justify this
  local result.  No Gen, Inst, or Equivalence rule is applied to local
  assumptions, and the premise set S is unchanged.
\<close>

lemma paper_global_derivable_iff_forward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and proved: "paper_global_derivable \<Sigma> G S A"
    and equivalent: "paper_global_derivable \<Sigma> G S (paper_iff A B)"
  shows "paper_global_derivable \<Sigma> G S B"
proof -
  let ?T = "SPImp (SPAtom 0) (SPImp (SPIff (SPAtom 0) (SPAtom 1)) (SPAtom 1)) :: nat sprop_template"
  have taut: "sprop_tautology ?T" by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have theorem_H: "paper_global_H \<Sigma> G (paper_imp A (paper_imp (paper_iff A B) B))"
    using paper_global_PC_two[OF A B taut] by simp
  have bridge: "paper_global_derivable \<Sigma> G S (paper_imp A (paper_imp (paper_iff A B) B))"
    by (rule paper_global_derivable.Theorem[OF theorem_H])
  have implication: "paper_global_derivable \<Sigma> G S (paper_imp (paper_iff A B) B)"
    by (rule paper_global_derivable.MP[OF proved bridge])
  show ?thesis by (rule paper_global_derivable.MP[OF equivalent implication])
qed

lemma paper_global_derivable_iff_backward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and proved: "paper_global_derivable \<Sigma> G S B"
    and equivalent: "paper_global_derivable \<Sigma> G S (paper_iff A B)"
  shows "paper_global_derivable \<Sigma> G S A"
proof -
  let ?T = "SPImp (SPAtom 1) (SPImp (SPIff (SPAtom 0) (SPAtom 1)) (SPAtom 0)) :: nat sprop_template"
  have taut: "sprop_tautology ?T" by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have theorem_H: "paper_global_H \<Sigma> G (paper_imp B (paper_imp (paper_iff A B) A))"
    using paper_global_PC_two[OF A B taut] by simp
  have bridge: "paper_global_derivable \<Sigma> G S (paper_imp B (paper_imp (paper_iff A B) A))"
    by (rule paper_global_derivable.Theorem[OF theorem_H])
  have implication: "paper_global_derivable \<Sigma> G S (paper_imp (paper_iff A B) A)"
    by (rule paper_global_derivable.MP[OF proved bridge])
  show ?thesis by (rule paper_global_derivable.MP[OF equivalent implication])
qed

lemma paper_global_derivable_equivalent_theorem_iff:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and equivalent: "paper_global_H \<Sigma> G (paper_iff A B)"
  shows "paper_global_derivable \<Sigma> G S A \<longleftrightarrow> paper_global_derivable \<Sigma> G S B"
proof -
  have local_equivalent: "paper_global_derivable \<Sigma> G S (paper_iff A B)"
    by (rule paper_global_derivable.Theorem[OF equivalent])
  show ?thesis
  proof
    assume proved: "paper_global_derivable \<Sigma> G S A"
    show "paper_global_derivable \<Sigma> G S B"
      by (rule paper_global_derivable_iff_forward[OF A B proved local_equivalent])
  next
    assume proved: "paper_global_derivable \<Sigma> G S B"
    show "paper_global_derivable \<Sigma> G S A"
      by (rule paper_global_derivable_iff_backward[OF A B proved local_equivalent])
  qed
qed

section \<open>Guarded source conversion preserves local consequence\<close>

text \<open>
  If A ≡βη B at type t in ℒ(Σ), then local derivability of their
  type-respecting images in G agrees.  Each β/η step supplies an actual
  source biconditional theorem, which is lifted into the local relation.
  Symmetry and transitivity compose these local-consequence equivalences.
  Source: contextual β/η and PC/MP in Figure 2, pp.7–8.

  Status.  Intermediate terms retain their source typing and signature
  guards.  S may be infinite or contain unused ill-formed expressions;
  only guarded assumptions can be used.  No richness, injectivity, target
  consequence, model, or proof-reflection premise is needed.
\<close>

lemma paper_global_derivable_conversion_aux:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<tau> A B"
    and is_prop: "\<tau> = Prop"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_derivable \<Sigma> G S (srename r A) \<longleftrightarrow>
    paper_global_derivable \<Sigma> G S (srename r B)"
  using conversion is_prop map
proof (induction arbitrary: G r rule: sbeta_eta_equiv_in_signature.induct)
  case Refl
  show ?case by (rule refl)
next
  case (Beta \<Gamma> A \<tau> B)
  have at: "has_stype paper_logical_type \<Gamma> A Prop" using Beta.hyps(1) by (simp only: Beta.prems(1))
  have bt: "has_stype paper_logical_type \<Gamma> B Prop" using Beta.hyps(2) by (simp only: Beta.prems(1))
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    unfolding sterm_in_language_def by (rule conjI[OF at Beta.hyps(3)])
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    unfolding sterm_in_language_def by (rule conjI[OF bt Beta.hyps(4)])
  have ag: "sgterm_in_language paper_logical_type \<Sigma> G (srename r A) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF al Beta.prems(2)])
  have bg: "sgterm_in_language paper_logical_type \<Sigma> G (srename r B) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF bl Beta.prems(2)])
  have step: "scompatible_step sbeta_contract (srename r A) (srename r B)"
    by (rule srename_beta_step[where r=r, OF Beta.hyps(5)])
  have biconditional: "paper_global_H \<Sigma> G (paper_iff (srename r A) (srename r B))"
    by (rule paper_global_beta_biconditional[OF ag bg step])
  show ?case by (rule paper_global_derivable_equivalent_theorem_iff[OF ag bg biconditional])
next
  case (Eta \<Gamma> A \<tau> B)
  have at: "has_stype paper_logical_type \<Gamma> A Prop" using Eta.hyps(1) by (simp only: Eta.prems(1))
  have bt: "has_stype paper_logical_type \<Gamma> B Prop" using Eta.hyps(2) by (simp only: Eta.prems(1))
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    unfolding sterm_in_language_def by (rule conjI[OF at Eta.hyps(3)])
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    unfolding sterm_in_language_def by (rule conjI[OF bt Eta.hyps(4)])
  have ag: "sgterm_in_language paper_logical_type \<Sigma> G (srename r A) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF al Eta.prems(2)])
  have bg: "sgterm_in_language paper_logical_type \<Sigma> G (srename r B) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF bl Eta.prems(2)])
  have step: "scompatible_step seta_contract (srename r A) (srename r B)"
    by (rule srename_eta_step[where r=r, OF Eta.hyps(5)])
  have biconditional: "paper_global_H \<Sigma> G (paper_iff (srename r A) (srename r B))"
    by (rule paper_global_eta_biconditional[OF ag bg step])
  show ?case by (rule paper_global_derivable_equivalent_theorem_iff[OF ag bg biconditional])
next
  case (Sym \<Gamma> \<tau> A B)
  have original: "paper_global_derivable \<Sigma> G S (srename r A) \<longleftrightarrow>
    paper_global_derivable \<Sigma> G S (srename r B)"
    by (rule Sym.IH[where G=G and r=r, OF Sym.prems(1,2)])
  show ?case by (rule sym[OF original])
next
  case (Trans \<Gamma> \<tau> A B C)
  have first: "paper_global_derivable \<Sigma> G S (srename r A) \<longleftrightarrow>
    paper_global_derivable \<Sigma> G S (srename r B)"
    by (rule Trans.IH(1)[where G=G and r=r, OF Trans.prems(1,2)])
  have second: "paper_global_derivable \<Sigma> G S (srename r B) \<longleftrightarrow>
    paper_global_derivable \<Sigma> G S (srename r C)"
    by (rule Trans.IH(2)[where G=G and r=r, OF Trans.prems(1,2)])
  show ?case by (rule trans[OF first second])
qed

theorem paper_global_derivable_conversion_iff:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> Prop A B"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_derivable \<Sigma> G S (srename r A) \<longleftrightarrow>
    paper_global_derivable \<Sigma> G S (srename r B)"
  by (rule paper_global_derivable_conversion_aux[where G=G and r=r, OF conversion refl map])

end
