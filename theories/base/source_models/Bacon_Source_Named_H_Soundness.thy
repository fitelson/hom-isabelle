theory Bacon_Source_Named_H_Soundness
  imports Bacon_Source_Named_Encoded_Local_Soundness
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Local_Forward
begin

section \<open>The independent named H calculus is sound in named BBK models\<close>

text \<open>
  Every theorem of the independently declared named H calculus is valid
  in every independent named BBK model. Local derivability preserves truth
  at a typed partial assignment adequate for the premises and conclusion.
  Source: Bacon–Dorr Figure 2 and Theorem 3.2, pp.8,44–45.

  The native ten-rule proof relation is first translated by a syntactic
  induction. The separately proved reverse model and open assignment
  transport then apply encoded soundness. Thus no validity predicate is
  built into the named proof definition. Local premise sets may be infinite;
  no common finite free-variable bound is required.

  Scope: the represented full F language at arbitrary signatures, using
  the named model's rich stock. Reverse proof preservation, named
  completeness, the R restriction, and the book's different general models
  remain separate results.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_H_at_assignment:
  assumes derivation: "paper_named_H signature stock A"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "valuation (denote g A)"
  by (rule paper_named_encoded_H_at_assignment[OF paper_named_H_language[OF derivation]
    paper_named_H_encoding[OF derivation stock_rich] typed adequate])

theorem paper_named_H_soundness:
  assumes derivation: "paper_named_H signature stock A"
  shows "named_valid A"
  by (rule paper_named_encoded_H_soundness[OF paper_named_H_language[OF derivation]
    paper_named_H_encoding[OF derivation stock_rich]])

theorem paper_named_local_soundness:
  assumes derivation: "paper_named_derivable signature stock S A"
    and premise_languages: "\<And>B. B \<in> S \<Longrightarrow> named_in_language paper_logical_type signature stock B Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and premise_adequacy: "\<And>B. B \<in> S \<Longrightarrow> named_adequate g B"
    and premise_truth: "\<And>B. B \<in> S \<Longrightarrow> valuation (denote g B)"
  shows "valuation (denote g A)"
  by (rule paper_named_encoded_local_at_assignment[OF paper_named_derivable_encoding[OF derivation stock_rich]
    paper_named_derivable_language[OF derivation] premise_languages typed adequate premise_adequacy premise_truth])

end

end
