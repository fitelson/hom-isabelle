theory Bacon_Source_Named_Model_Type_Tagging_Model
  imports Bacon_Source_Named_Model_Type_Tagging_Truth
begin

section \<open>A truth-preserving tagged copy of each named model\<close>

text \<open>
  Every named BBK model has a tagged named BBK model with the same
  signature, variable stock, and valid formulas. Source: the clauses of
  Bacon–Dorr Definition 3.1, pp.43–44.

  Representation: the new carrier is otype × value, with D′σ the tagged
  copy of Dσ. Tagging and untagging give inverse maps on typed adequate
  partial assignments. Truth agrees on these corresponding assignments,
  including for open formulas. Validity quantifies over all such
  assignments, not just total assignments or a chosen completion.

  Status: this construction starts from an arbitrary independent named
  model. It is not a converse from named to de Bruijn models, and proves
  no Γ-erasure, chart-independence, H completeness, or change-of-stock
  result. Disjointness is a property of the constructed domains only.
\<close>

context paper_named_bbk_model
begin

theorem model_type_tagging:
  "paper_named_bbk_model signature stock (named_tag_domain domain)
    model_tag_denote model_tag_valuation"
  apply unfold_locales
              apply (rule stock_rich)
             apply (rule named_tag_domain_nonempty, rule domain_nonempty)
            apply (rule model_tag_denote_type; assumption)
           apply (rule model_tag_denote_var; assumption)
          apply (rule model_tag_denote_application; assumption)
         apply (rule model_tag_denote_locality; assumption)
        apply (rule model_tag_denote_beta_eta; assumption)
       apply (rule model_tag_neg; assumption)
      apply (rule model_tag_conj; assumption)
     apply (rule model_tag_disj; assumption)
    apply (rule model_tag_forall; assumption)
   apply (rule model_tag_exists; assumption)
  apply (rule model_tag_identity; assumption)
  done

lemma model_tag_truth_tag_assignment:
  "model_tag_valuation (model_tag_denote (named_tag_assignment stock g) A) =
    valuation (denote g A)"
  by (simp only: model_tag_truth named_untag_tag_assignment)

theorem model_tag_valid_iff:
  "paper_named_bbk_model.named_valid signature stock (named_tag_domain domain)
    model_tag_denote model_tag_valuation A \<longleftrightarrow> named_valid A"
proof -
  interpret Tagged: paper_named_bbk_model signature stock "named_tag_domain domain"
    model_tag_denote model_tag_valuation by (rule model_type_tagging)
  show ?thesis
  proof
    assume tagged_valid: "Tagged.named_valid A"
    have language: "named_in_language paper_logical_type signature stock A Prop"
      using tagged_valid unfolding Tagged.named_valid_def by (rule conjunct1)
    have tagged_truth: "\<And>g. named_env_typed (named_tag_domain domain) stock g \<Longrightarrow>
      named_adequate g A \<Longrightarrow> model_tag_valuation (model_tag_denote g A)"
      using tagged_valid unfolding Tagged.named_valid_def Tagged.named_satisfies_def by blast
    show "named_valid A"
    proof (unfold named_valid_def, rule conjI[OF language], intro allI impI)
      fix g
      assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
      have tt: "named_env_typed (named_tag_domain domain) stock (named_tag_assignment stock g)"
        by (rule named_tag_assignment_typed[OF typed])
      have ta: "named_adequate (named_tag_assignment stock g) A"
        by (rule iffD2[OF named_tag_assignment_adequate adequate])
      have truth: "model_tag_valuation (model_tag_denote (named_tag_assignment stock g) A)"
        by (rule tagged_truth[OF tt ta])
      show "named_satisfies g A"
        using truth by (simp only: named_satisfies_def model_tag_truth_tag_assignment)
    qed
  next
    assume original_valid: "named_valid A"
    have language: "named_in_language paper_logical_type signature stock A Prop"
      using original_valid unfolding named_valid_def by (rule conjunct1)
    have original_truth: "\<And>g. named_env_typed domain stock g \<Longrightarrow>
      named_adequate g A \<Longrightarrow> valuation (denote g A)"
      using original_valid unfolding named_valid_def named_satisfies_def by blast
    show "Tagged.named_valid A"
    proof (unfold Tagged.named_valid_def, rule conjI[OF language], intro allI impI)
      fix g
      assume typed: "named_env_typed (named_tag_domain domain) stock g" and adequate: "named_adequate g A"
      have ut: "named_env_typed domain stock (named_untag_assignment g)"
        by (rule named_untag_assignment_typed[OF typed])
      have ua: "named_adequate (named_untag_assignment g) A"
        by (rule iffD2[OF named_untag_assignment_adequate adequate])
      have truth: "valuation (denote (named_untag_assignment g) A)"
        by (rule original_truth[OF ut ua])
      show "Tagged.named_satisfies g A"
        using truth by (simp only: Tagged.named_satisfies_def model_tag_truth)
    qed
  qed
qed

end

end
