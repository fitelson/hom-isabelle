theory Bacon_Source_Named_Forward_Validity
  imports Bacon_Source_Named_Tagged_Model
begin

section \<open>Source truth supplies validity in the constructed named model\<close>

text \<open>
  If the encoding of A is true at every globally typed source environment,
  A is valid in the named model constructed from that source structure.
  Source role: the model transfer for Bacon–Dorr Definition 3.1 and
  Theorem 3.2, pp.43–45.

  Complete each adequate partial named assignment only after removing its
  type tags. The resulting source environment is globally typed, and the
  checked completion-truth theorem recovers the named truth value. There
  is no closedness restriction on A and no assumption that the named
  assignment covers every variable. The source-truth premise remains
  explicit; later model-existence results supply it for their sentences.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_named_valid_from_truth:
  assumes rich: "sg_rich G"
    and language: "named_in_language paper_logical_type signature G A Prop"
    and source_truth: "\<And>h. paper_global_env_typed domain G h \<Longrightarrow>
      valuation (denote h (named_to_source G [] A))"
  shows "paper_named_bbk_model.named_valid signature G (named_tag_domain domain)
    (tagged_named_denote G) (\<lambda>v. valuation (snd v)) A"
proof -
  interpret Named: paper_named_bbk_model signature G "named_tag_domain domain"
    "tagged_named_denote G" "\<lambda>v. valuation (snd v)"
    by (rule paper_db_tagged_named_model[OF rich])
  show ?thesis
  proof (unfold Named.named_valid_def, rule conjI[OF language], intro allI impI)
    fix g
    assume typed: "named_env_typed (named_tag_domain domain) G g" and adequate: "named_adequate g A"
    have untagged: "named_env_typed domain G (named_untag_assignment g)"
      by (rule named_untag_assignment_typed[OF typed])
    obtain h where completion: "named_completion domain G (named_untag_assignment g) h"
      using named_assignment_completion_exists[OF domain_nonempty untagged] by (elim exE)
    have truth: "valuation (denote h (named_to_source G [] A))"
      by (rule source_truth[OF named_completion_typed[OF completion]])
    have transported: "valuation (snd (tagged_named_denote G g A)) =
      valuation (denote h (named_to_source G [] A))"
      by (rule paper_db_tagged_named_completion_truth[OF language typed adequate completion])
    show "Named.named_satisfies g A"
      by (simp only: Named.named_satisfies_def transported; rule truth)
  qed
qed

end

end
