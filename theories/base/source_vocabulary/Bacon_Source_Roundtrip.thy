theory Bacon_Source_Roundtrip
  imports Bacon_Source_Logical_Roundtrip Bacon_Source_Conversion_Contexts
begin

section \<open>The source round trip preserves terms up to guarded conversion\<close>

text \<open>
  Translate a well-typed paper term into the target syntax and then
  re-express it in the paper language. The result is βη-convertible to
  the original source term. The extra logical wrappers are η expansions;
  application and abstraction preserve the conversions.
  Source: Bacon–Dorr's first-class logical constants and contextual η,
  §1.1 and Figure 2, pp.5–8.

  Isabelle representation: the theorem concerns the source round trip
  pterm_to_paper(paper_to_pterm A). It is not a literal equality of raw
  terms or a round-trip identity on every target term. In particular,
  it does not identify target primitive implication with the source's
  defined implication. Every conversion node is typed and belongs to Σ.

  Scope: syntax adequacy in the paper basis, at arbitrary types and
  signatures. Reverse H-proof preservation and a named-variable
  correspondence remain separate obligations.
\<close>

lemma paper_roundtrip_typed:
  assumes typed: "has_stype paper_logical_type \<Gamma> A \<tau>"
    and names: "sterm_in_signature \<Sigma> A"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<tau>
    (pterm_to_paper (paper_to_pterm A)) A"
  using typed names
proof (induction rule: has_stype.induct)
  case (Var \<Gamma> n \<tau>)
  show ?case by (simp only: sterm_translation.simps pterm_to_paper.simps;
    rule sbeta_eta_equiv_in_signature.Refl[OF has_stype.Var[OF Var.hyps]]) simp
next
  case (Const \<Gamma> c \<tau>)
  show ?case by (simp only: sterm_translation.simps pterm_to_paper.simps;
    rule sbeta_eta_equiv_in_signature.Refl[OF has_stype.Const Const.prems])
next
  case (Logical \<Gamma> l)
  show ?case by (simp only: sterm_translation.simps; rule paper_logical_roundtrip)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have ms: "sterm_in_signature \<Sigma> M" and ns: "sterm_in_signature \<Sigma> N"
    using App.prems by simp_all
  have left: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> (Arr \<sigma> \<tau>)
    (pterm_to_paper (paper_to_pterm M)) M" by (rule App.IH(1)[OF ms])
  have right: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<sigma>
    (pterm_to_paper (paper_to_pterm N)) N" by (rule App.IH(2)[OF ns])
  show ?case using sbeta_eta_App[OF left right]
    by (simp only: sterm_translation.simps pterm_to_paper.simps)
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have ms: "sterm_in_signature \<Sigma> M" using Lam.prems by simp
  have body: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) \<tau>
    (pterm_to_paper (paper_to_pterm M)) M" by (rule Lam.IH[OF ms])
  show ?case using sbeta_eta_Lam[OF body]
    by (simp only: sterm_translation.simps pterm_to_paper.simps)
qed

theorem paper_roundtrip_conversion:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<tau>"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<tau>
    (pterm_to_paper (paper_to_pterm A)) A"
  using language unfolding sterm_in_language_def by (metis paper_roundtrip_typed)

end
