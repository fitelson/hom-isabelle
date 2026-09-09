theory Bacon_Source_Named_Tagged_Model
  imports Bacon_Source_Named_BBK_Interface Bacon_Source_Named_Tagged_Quantifiers
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Signature_Conservativity
begin

section \<open>The constructed interpretation satisfies every independent named clause\<close>

text \<open>
  From a finite-frame source structure and a rich named variable stock,
  construct a named BBK model on D′σ = {⟨σ,a⟩ | a ∈ Dσ}.
  Adequate partial assignments are completed only after removing their
  tags; the value is independent of that completion.

  Source: Bacon–Dorr Definition 3.1, pp.43–44. Type tags verify its
  heterogeneous application clause without assuming that the old domains
  are disjoint. Signature conservativity verifies raw typed βη conversion
  of Σ-endpoints without requiring intermediate terms to remain in Σ or
  the partial assignment to cover their free names.

  Status: a checked model construction, not a definition of named models
  through finite-frame models. The independent model predicate has its
  own clauses. The carrier changes to otype × value; the converse named
  interpretation and named-H soundness/completeness remain separate.
\<close>

lemma named_binary_logical_adequate:
  assumes left: "named_adequate g A" and right: "named_adequate g B"
  shows "named_adequate g (NApp (NApp (NLogical l) A) B)"
  using left right unfolding named_adequate_def by auto

context paper_db_bbk_structure
begin

lemma paper_db_tagged_named_raw_conversion:
  assumes rich: "sg_rich G"
    and raw: "named_raw_beta_eta paper_logical_type G \<sigma> A B"
    and left: "named_in_language paper_logical_type signature G A \<sigma>"
    and right: "named_in_language paper_logical_type signature G B \<sigma>"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "tagged_named_denote G g A = tagged_named_denote G g B"
  by (rule paper_db_tagged_named_conversion[OF
    named_raw_to_signature[OF rich raw left right] typed adequate_A adequate_B])

theorem paper_db_tagged_named_model:
  assumes rich: "sg_rich G"
  shows "paper_named_bbk_model signature G (named_tag_domain domain)
    (tagged_named_denote G) (\<lambda>v. valuation (snd v))"
  apply unfold_locales
              apply (rule rich)
             apply (rule named_tag_domain_nonempty, rule domain_nonempty)
            apply (rule tagged_named_denote_type; assumption)
           apply (rule tagged_named_denote_var; assumption)
          apply (rule paper_db_tagged_named_application_cong; assumption)
         apply (rule paper_db_tagged_named_locality; assumption)
        apply (rule paper_db_tagged_named_raw_conversion[OF rich]; assumption)
       apply (rule paper_db_tagged_named_neg_truth; assumption)
      apply (rule paper_db_tagged_named_conj_truth; (assumption | (rule named_binary_logical_adequate; assumption)))
     apply (rule paper_db_tagged_named_disj_truth; (assumption | (rule named_binary_logical_adequate; assumption)))
    apply (rule paper_db_tagged_named_forall_truth; assumption)
   apply (rule paper_db_tagged_named_exists_truth; assumption)
  apply (rule paper_db_tagged_named_identity_truth; (assumption | (rule named_binary_logical_adequate; assumption)))
  done

theorem paper_db_tagged_named_completion_truth:
  assumes language: "named_in_language paper_logical_type signature G A Prop"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g A"
    and completion: "named_completion domain G (named_untag_assignment g) h"
  shows "valuation (snd (tagged_named_denote G g A)) =
    valuation (denote h (named_to_source G [] A))"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have equality: "named_denote G (named_untag_assignment g) A = denote h (named_to_source G [] A)"
    by (rule paper_db_named_denote_completion[OF language old_typed old_adequate completion])
  show ?thesis by (simp only: tagged_named_denote_def snd_conv equality)
qed

end

corollary paper_db_named_model_exists:
  fixes D :: "otype \<Rightarrow> 'v set"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> 'v"
  assumes source_model: "paper_db_bbk_structure \<Sigma> D J V" and rich: "sg_rich G"
  shows "\<exists>J' :: (otype \<times> 'v) named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> (otype \<times> 'v).
    paper_named_bbk_model \<Sigma> G (named_tag_domain D) J' (\<lambda>v. V (snd v))"
proof -
  interpret Source: paper_db_bbk_structure \<Sigma> D J V by (rule source_model)
  show ?thesis by (rule exI[where x="Source.tagged_named_denote G"])
    (rule Source.paper_db_tagged_named_model[OF rich])
qed

end
