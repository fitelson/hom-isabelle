theory Bacon_Source_Formula_Conversion
  imports Bacon_Source_Defined_Connectives
begin

section \<open>Typed conversion gives a formula biconditional in H\<close>

text \<open>
  Φ[(λv.A)B] ↔ Φ[A[B/v]] and Φ[λv.Fv] ↔ Φ[F] are the
  contextual conversion axioms of Bacon–Dorr Figure 2, p. 8.
  PC and MP combine these biconditionals along a βη chain.

  Isabelle representation: PObjIff and PImp occur here only in target
  proof-level propositional bridges.  They do not replace the literal
  paper implication inside an arbitrary translated term.

  Status: target H proof transport for typed formulas along signature-indexed
  conversion.  Every chain node has type t and belongs to Σ.
\<close>

lemma source_pH_PC:
  assumes typed: "has_ptype \<Gamma> A Prop" and names: "pterm_in_signature \<Sigma> A"
    and truth: "\<And>v. pprop_eval v A"
  shows "pH_proves \<Sigma> \<Gamma> A"
proof (rule pH_proves.PC)
  show "pprop_tautology \<Gamma> A" unfolding pprop_tautology_def
    by (rule conjI[OF typed]; rule allI; rule truth)
  show "pterm_in_signature \<Sigma> A" by (rule names)
qed

lemma source_pH_MP:
  assumes a: "pH_proves \<Sigma> \<Gamma> A" and ab: "pH_proves \<Sigma> \<Gamma> (PImp A B)"
  shows "pH_proves \<Sigma> \<Gamma> B"
proof -
  have names: "pterm_in_signature \<Sigma> (PImp A B)" by (rule pH_proves_in_signature[OF ab])
  have asig: "pterm_in_signature \<Sigma> A" using names by simp
  have bsig: "pterm_in_signature \<Sigma> B" using names by simp
  show ?thesis by (rule pH_proves.MP[OF a ab asig bsig])
qed

lemma source_pH_iff_refl:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
  shows "pH_proves \<Sigma> \<Gamma> (PObjIff A A)"
proof (rule source_pH_PC)
  show "has_ptype \<Gamma> (PObjIff A A) Prop" using A unfolding pterm_in_language_def
    by (auto intro: has_ptype.PConj has_ptype.PImp)
  show "pterm_in_signature \<Sigma> (PObjIff A A)" using A unfolding pterm_in_language_def by simp
  show "\<And>v. pprop_eval v (PObjIff A A)" by simp
qed

lemma source_pH_iff_sym:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    and ab: "pH_proves \<Sigma> \<Gamma> (PObjIff A B)"
  shows "pH_proves \<Sigma> \<Gamma> (PObjIff B A)"
proof -
  have bridge: "pH_proves \<Sigma> \<Gamma> (PImp (PObjIff A B) (PObjIff B A))"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PImp (PObjIff A B) (PObjIff B A)) Prop"
      using A B unfolding pterm_in_language_def
      by (auto intro: has_ptype.PConj has_ptype.PImp)
    show "pterm_in_signature \<Sigma> (PImp (PObjIff A B) (PObjIff B A))"
      using A B unfolding pterm_in_language_def by simp
    show "\<And>v. pprop_eval v (PImp (PObjIff A B) (PObjIff B A))"
      by (simp only: pprop_eval.simps; blast)
  qed
  show ?thesis by (rule source_pH_MP[OF ab bridge])
qed

lemma source_pH_iff_trans:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    and C: "pterm_in_language \<Sigma> \<Gamma> C Prop"
    and ab: "pH_proves \<Sigma> \<Gamma> (PObjIff A B)"
    and bc: "pH_proves \<Sigma> \<Gamma> (PObjIff B C)"
  shows "pH_proves \<Sigma> \<Gamma> (PObjIff A C)"
proof -
  have bridge: "pH_proves \<Sigma> \<Gamma> (PImp (PObjIff A B) (PImp (PObjIff B C) (PObjIff A C)))"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PImp (PObjIff A B) (PImp (PObjIff B C) (PObjIff A C))) Prop"
      using A B C unfolding pterm_in_language_def
      by (auto intro: has_ptype.PConj has_ptype.PImp)
    show "pterm_in_signature \<Sigma> (PImp (PObjIff A B) (PImp (PObjIff B C) (PObjIff A C)))"
      using A B C unfolding pterm_in_language_def by simp
    show "\<And>v. pprop_eval v (PImp (PObjIff A B) (PImp (PObjIff B C) (PObjIff A C)))"
      by (simp only: pprop_eval.simps; blast)
  qed
  show ?thesis by (rule source_pH_MP[OF bc source_pH_MP[OF ab bridge]])
qed

lemma source_conversion_formula_iff_typed:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
  shows "\<tau> = Prop \<Longrightarrow> pH_proves \<Sigma> \<Gamma> (PObjIff M N)"
  using conv
proof (induction rule: pbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> M \<tau>)
  have mt: "has_ptype \<Gamma> M Prop" using Refl.hyps(1) by (simp only: Refl.prems)
  have ml: "pterm_in_language \<Sigma> \<Gamma> M Prop" unfolding pterm_in_language_def
    by (rule conjI[OF mt Refl.hyps(2)])
  show ?case by (rule source_pH_iff_refl[OF ml])
next
  case (Beta \<Gamma> M \<tau> N)
  have mt: "has_ptype \<Gamma> M Prop" using Beta.hyps(1) by (simp only: Beta.prems)
  have nt: "has_ptype \<Gamma> N Prop" using Beta.hyps(2) by (simp only: Beta.prems)
  show ?case by (rule pH_proves.Beta[OF mt nt Beta.hyps(5,3,4)])
next
  case (Eta \<Gamma> M \<tau> N)
  have mt: "has_ptype \<Gamma> M Prop" using Eta.hyps(1) by (simp only: Eta.prems)
  have nt: "has_ptype \<Gamma> N Prop" using Eta.hyps(2) by (simp only: Eta.prems)
  show ?case by (rule pH_proves.Eta[OF mt nt Eta.hyps(5,3,4)])
next
  case (Sym \<Gamma> \<tau> M N)
  have ml: "pterm_in_language \<Sigma> \<Gamma> M Prop"
    using source_conversion_left_language[OF Sym.hyps] by (simp only: Sym.prems)
  have nl: "pterm_in_language \<Sigma> \<Gamma> N Prop"
    using source_conversion_right_language[OF Sym.hyps] by (simp only: Sym.prems)
  show ?case by (rule source_pH_iff_sym[OF ml nl Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> M N P)
  have ml: "pterm_in_language \<Sigma> \<Gamma> M Prop"
    using source_conversion_left_language[OF Trans.hyps(1)] by (simp only: Trans.prems)
  have nl: "pterm_in_language \<Sigma> \<Gamma> N Prop"
    using source_conversion_right_language[OF Trans.hyps(1)] by (simp only: Trans.prems)
  have pl: "pterm_in_language \<Sigma> \<Gamma> P Prop"
    using source_conversion_right_language[OF Trans.hyps(2)] by (simp only: Trans.prems)
  show ?case by (rule source_pH_iff_trans[
    OF ml nl pl Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma source_conversion_formula_iff:
  assumes "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
  shows "pH_proves \<Sigma> \<Gamma> (PObjIff M N)"
  by (rule source_conversion_formula_iff_typed[OF assms refl])

lemma source_pH_conversion_backward:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and proved: "pH_proves \<Sigma> \<Gamma> N"
  shows "pH_proves \<Sigma> \<Gamma> M"
proof -
  note ml = source_conversion_left_language[OF conv]
  note nl = source_conversion_right_language[OF conv]
  have bridge: "pH_proves \<Sigma> \<Gamma> (PImp (PObjIff M N) (PImp N M))"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PImp (PObjIff M N) (PImp N M)) Prop"
      using ml nl unfolding pterm_in_language_def
      by (auto intro: has_ptype.PConj has_ptype.PImp)
    show "pterm_in_signature \<Sigma> (PImp (PObjIff M N) (PImp N M))"
      using ml nl unfolding pterm_in_language_def by simp
    show "\<And>v. pprop_eval v (PImp (PObjIff M N) (PImp N M))"
      by (simp only: pprop_eval.simps; blast)
  qed
  show ?thesis by (rule source_pH_MP[
    OF proved source_pH_MP[OF source_conversion_formula_iff[OF conv] bridge]])
qed

end
