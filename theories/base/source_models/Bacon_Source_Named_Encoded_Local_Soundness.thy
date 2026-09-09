theory Bacon_Source_Named_Encoded_Local_Soundness
  imports Bacon_Source_Named_Encoded_H_Soundness
begin

section \<open>Encoded local H is sound at adequate partial named assignments\<close>

text \<open>
  Suppose the source encodings of S derive the encoding of A. Every typed
  named assignment adequate for S and A that makes S true also makes A
  true. Source role: local consequence and Bacon–Dorr Theorem 3.2.

  S may be infinite and have no common finite free-name bound. Complete
  its one partial assignment once; the completion preserves each assumed
  formula using that formula's own finite support. No uniform prefix or
  countability of S is assumed. This leaf still names the encoded proof
  premise explicitly; native named consequence is transferred separately.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_encoded_local_at_assignment:
  assumes derivation: "paper_global_derivable signature stock (named_to_source stock [] ` S)
      (named_to_source stock [] A)"
    and language: "named_in_language paper_logical_type signature stock A Prop"
    and premise_languages: "\<And>B. B \<in> S \<Longrightarrow> named_in_language paper_logical_type signature stock B Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and premise_adequacy: "\<And>B. B \<in> S \<Longrightarrow> named_adequate g B"
    and premise_truth: "\<And>B. B \<in> S \<Longrightarrow> valuation (denote g B)"
  shows "valuation (denote g A)"
proof -
  obtain h where completion: "named_completion domain stock g h"
    using named_assignment_completion_exists[OF domain_nonempty typed] by (elim exE)
  let ?\<rho> = "\<lambda>n. (stock n, h n)"
  have global_env: "paper_global_env_typed (named_tag_domain domain) stock ?\<rho>"
    by (rule paper_named_completion_global_tagged[OF completion])
  interpret Reverse: paper_db_bbk_structure signature "named_tag_domain domain"
    "named_erased_denote stock model_tag_denote" model_tag_valuation
    by (rule paper_named_to_db_model)
  have source_premises: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho> E)"
    if member: "E \<in> named_to_source stock [] ` S" for E
  proof -
    obtain B where original: "B \<in> S" and encoded: "E = named_to_source stock [] B"
      using member by blast
    have bound: "source_free_bound (named_to_source stock [] B) \<le> source_free_bound (named_to_source stock [] B)"
      by (rule order_refl)
    have transport: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho>
        (named_to_source stock [] B)) = valuation (denote g B)"
      by (rule paper_named_reverse_completion_truth[OF premise_languages[OF original] bound typed
        premise_adequacy[OF original] completion])
    show "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho> E)"
      by (simp only: encoded transport; rule premise_truth[OF original])
  qed
  have source_truth: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho>
      (named_to_source stock [] A))"
    by (rule Reverse.paper_db_global_set_soundness[OF derivation global_env source_premises])
  have bound: "source_free_bound (named_to_source stock [] A) \<le> source_free_bound (named_to_source stock [] A)"
    by (rule order_refl)
  have transport: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho>
      (named_to_source stock [] A)) = valuation (denote g A)"
    by (rule paper_named_reverse_completion_truth[OF language bound typed adequate completion])
  show ?thesis using source_truth by (simp only: transport)
qed

end

end
