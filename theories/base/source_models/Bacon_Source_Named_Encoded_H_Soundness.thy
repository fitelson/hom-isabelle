theory Bacon_Source_Named_Encoded_H_Soundness
  imports Bacon_Source_Named_Reverse_Open_Validity Bacon_Source_BBK_Global_Soundness
begin

section \<open>Encoded source-H theorems hold in every independent named model\<close>

text \<open>
  If the source encoding of a named formula A is an H theorem, then
  M,g ⊨ A for every adequate typed partial assignment g in every
  independent named BBK model M. Source role: the soundness direction
  of Bacon–Dorr Theorem 3.2, pp.44–45, with proof representation explicit.

  Representation: complete g to h, tag h to a globally typed source
  environment, and invoke source-H soundness in the constructed reverse
  model. Completion-truth transport recovers the original named value.
  Status: the proof premise is paper_global_H of named_to_source, not an
  independently defined named-H judgment. No named proof correspondence
  or local-set consequence theorem is asserted in this leaf.
\<close>

context paper_named_bbk_model
begin

lemma paper_named_completion_global_tagged:
  assumes completion: "named_completion domain stock g h"
  shows "paper_global_env_typed (named_tag_domain domain) stock (\<lambda>n. (stock n, h n))"
proof -
  have total: "paper_global_env_typed domain stock h"
    by (rule named_completion_typed[OF completion])
  show ?thesis
  proof (unfold paper_global_env_typed_def, rule allI)
    fix n
    have member: "h n \<in> domain (stock n)"
      by (rule paper_global_env_at[OF total])
    show "(stock n, h n) \<in> named_tag_domain domain (stock n)"
      by (simp only: named_tag_domain_pair_iff; rule conjI[OF refl member])
  qed
qed

theorem paper_named_encoded_H_at_assignment:
  assumes language: "named_in_language paper_logical_type signature stock A Prop"
    and derivation: "paper_global_H signature stock (named_to_source stock [] A)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "valuation (denote g A)"
proof -
  obtain h where completion: "named_completion domain stock g h"
    using named_assignment_completion_exists[OF domain_nonempty typed] by (elim exE)
  let ?\<rho> = "\<lambda>n. (stock n, h n)"
  let ?E = "named_to_source stock [] A"
  have global_env: "paper_global_env_typed (named_tag_domain domain) stock ?\<rho>"
    by (rule paper_named_completion_global_tagged[OF completion])
  interpret Reverse: paper_db_bbk_structure signature "named_tag_domain domain"
    "named_erased_denote stock model_tag_denote" model_tag_valuation
    by (rule paper_named_to_db_model)
  have source_truth: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho> ?E)"
    by (rule Reverse.paper_db_global_H_soundness[OF derivation global_env])
  have bound: "source_free_bound ?E \<le> source_free_bound ?E" by (rule order_refl)
  have recovered: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho> ?E) =
    valuation (denote g A)"
    by (rule paper_named_reverse_completion_truth[OF language bound typed adequate completion])
  show ?thesis using source_truth by (simp only: recovered)
qed

theorem paper_named_encoded_H_soundness:
  assumes language: "named_in_language paper_logical_type signature stock A Prop"
    and derivation: "paper_global_H signature stock (named_to_source stock [] A)"
  shows "named_valid A"
proof (unfold named_valid_def, rule conjI[OF language], intro allI impI)
  fix g
  assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  show "named_satisfies g A"
    unfolding named_satisfies_def
    by (rule paper_named_encoded_H_at_assignment[OF language derivation typed adequate])
qed

end

end
