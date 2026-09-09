theory Bacon_Source_BBK_Roundtrip
  imports Bacon_Source_BBK_Interface Bacon_Source_Roundtrip
begin

section \<open>The source round trip preserves denotation, not merely truth\<close>

text \<open>
  ⟦back(tr(A))⟧ᵍ = ⟦A⟧ᵍ for every typed source term A of ℒ(Σ).
  This follows from the source η computations and Definition 3.1(ii.d).
  Neither renaming coherence nor a truth clause is needed.

  This is the source-side recovery equation for the prospective pair of
  interpretation translations. It does not assert that arbitrary target
  terms containing primitive implication recover their denotations after
  the opposite round trip. No two-sided model isomorphism is claimed.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_roundtrip_denotation:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "denote g (pterm_to_paper (paper_to_pterm A)) = denote g A"
  by (rule denote_beta_eta[OF paper_roundtrip_conversion[OF language] env])

end

end
