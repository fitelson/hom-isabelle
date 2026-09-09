theory Bacon_Source_Named_Conversion_Denotation
  imports Bacon_Source_Named_Completion_Denotation
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha_Conversion
begin

section \<open>Conversion preserves denotation at adequate partial assignments\<close>

text \<open>
  If A ≡βη B within ℒ(Σ), a typed partial assignment adequate for A
  and B gives them the same value. Choose one total typed completion.
  A common proof prefix supports the entire converted derivation; source
  βη invariance then applies at that completion.

  Source: Bacon–Dorr Definition 3.1(ii.d), pp.43–44. The partial g
  need not assign names occurring only in intermediate terms. This is a
  property of the constructed interpretation, not an assumed named-model
  clause. Unrestricted-signature conversion conservativity and the reverse
  named-model transport remain separate obligations.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_named_conversion_denote:
  assumes conversion: "named_beta_eta_in_language paper_logical_type signature G \<sigma> A B"
    and typed: "named_env_typed domain G g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "named_denote G g A = named_denote G g B"
proof -
  let ?h = "SOME h. named_completion domain G g h"
  have completion: "named_completion domain G g ?h"
    by (rule paper_db_named_chosen_completion[OF typed])
  obtain N where frames: "\<forall>m\<ge>N.
    sbeta_eta_equiv_in_signature paper_logical_type signature (source_prefix G m) \<sigma>
      (named_to_source G [] A) (named_to_source G [] B)"
    using named_conversion_prefix_eventual[OF conversion] by (elim exE)
  have selected: "sbeta_eta_equiv_in_signature paper_logical_type signature (source_prefix G N) \<sigma>
    (named_to_source G [] A) (named_to_source G [] B)" using frames by blast
  have env: "pbbk_env_typed domain (source_prefix G N) ?h"
    by (rule paper_global_env_prefix[OF named_completion_typed[OF completion]])
  have equality: "denote ?h (named_to_source G [] A) = denote ?h (named_to_source G [] B)"
    by (rule denote_beta_eta[OF selected env])
  show ?thesis using equality by (simp only: named_denote_def)
qed

corollary paper_db_named_alpha_denote:
  assumes alpha: "named_alpha G A B"
    and language: "named_in_language paper_logical_type signature G A \<sigma>"
    and typed: "named_env_typed domain G g" and adequate: "named_adequate g A"
  shows "named_denote G g A = named_denote G g B"
proof -
  have conversion: "named_beta_eta_in_language paper_logical_type signature G \<sigma> A B"
    by (rule named_alpha_implies_beta_eta[OF alpha language])
  have adequate_B: "named_adequate g B"
    using adequate unfolding named_adequate_def by (simp only: named_alpha_fv[OF alpha])
  show ?thesis by (rule paper_db_named_conversion_denote[OF conversion typed adequate adequate_B])
qed

end

end
