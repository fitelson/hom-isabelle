theory Bacon_Source_Closed_Proof_Preservation
  imports Bacon_Source_Global_Proof_Preservation Bacon_Source_Target_Context_Elimination
begin

section \<open>Closed source sentences translate to target theorems\<close>

text \<open>
  A closed theorem of source H translates to a theorem of the target H
  calculus with no free-variable context. A finite prefix first retains
  all variables used in the source derivation; only afterwards do we
  remove the unused context from its closed conclusion.
  Source: Bacon–Dorr Figure 2 and the distinction between H and H⁻,
  pp.7–9.

  Isabelle representation: sfv A = {} is source closedness. The signature
  Σ and arbitrary nonlogical name carrier are unchanged by translation.
  No closed inhabitant is required in Σ. Target context elimination uses
  the represented target Existence machinery, as documented separately;
  the source still has exactly its ten rules.

  Scope: forward proof preservation for the paper's literal first-class
  basis and defined connectives at full F types. This is not reverse
  proof preservation, named-variable/α correspondence, or completeness
  for a separately defined source model class.
\<close>

lemma source_global_closed_language:
  assumes language: "sgterm_in_language L \<Sigma> G A \<tau>"
    and closed: "sfv A = {}"
  shows "sterm_in_language L \<Sigma> [] A \<tau>"
proof -
  have global: "has_sgtype L G A \<tau>" and names: "sterm_in_signature \<Sigma> A"
    using language unfolding sgterm_in_language_def by blast+
  have typed: "has_stype L [] A \<tau>"
    by (rule source_global_to_finite_typing[OF global]) (simp add: closed)
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF typed names])
qed

theorem paper_global_H_closed_preservation:
  assumes derivation: "paper_global_H \<Sigma> G A"
    and closed: "sfv A = {}"
  shows "pH_proves \<Sigma> [] (paper_to_pterm A)"
proof -
  have language: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
    by (rule source_global_closed_language[OF paper_global_H_language[OF derivation] closed])
  have target_language: "pterm_in_language \<Sigma> [] (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff language])
  obtain m where target: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
    by (rule paper_global_H_target_finite_prefix[OF derivation])
  show ?thesis by (rule source_target_closed_context_elimination[OF target_language target])
qed

end
