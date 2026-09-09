theory Bacon_Source_Relational_Local_Soundness
  imports Bacon_Source_Relational_Local_Supported_Soundness
begin

section \<open>Soundness under the original adequate partial assignment\<close>

text \<open>
  If S⊢HᴿA, a typed assignment g is adequate for A and each
  usable premise, and those premises are true under g, then A is true
  under g. Source: pp.7–8 and Theorem 3.2, pp.44–45.

  Complete g only at missing R-typed names. The resulting option-valued
  assignment covers the intermediate formulas. Locality preserves each
  premise already covered by g and returns the conclusion to g.
  S may be infinite and contain open formulas; non-R entries impose
  no condition. No F completion, F model, global deduction theorem,
  consistency assumption or model-existence result is used.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_named_derivable_soundness:
  assumes derivation: "paper_R_named_derivable signature stock S A"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and premise_adequacy: "\<And>B. B \<in> S \<Longrightarrow> paper_R_in_language signature stock B Prop \<Longrightarrow>
      named_adequate g B"
    and premise_truth: "\<And>B. B \<in> S \<Longrightarrow> paper_R_in_language signature stock B Prop \<Longrightarrow>
      valuation (denote g B)"
  shows "valuation (denote g A)"
proof -
  let ?k = "paper_R_complete_assignment domain stock g"
  have kt: "named_env_typed domain stock ?k" by (rule paper_R_completed_assignment_typed[OF typed])
  have covering: "named_adequate ?k B" if "paper_R_in_language signature stock B Prop" for B
    by (rule paper_R_complete_assignment_language_adequate[OF that])
  have premise_values: "valuation (denote ?k B)"
    if member: "B \<in> S" and language: "paper_R_in_language signature stock B Prop" for B
  proof -
    have ba: "named_adequate g B" by (rule premise_adequacy[OF member language])
    have true_B: "valuation (denote g B)" by (rule premise_truth[OF member language])
    show ?thesis by (simp only: paper_R_completed_assignment_denote[OF language typed ba]; rule true_B)
  qed
  have result: "valuation (denote ?k A)"
    by (rule paper_R_named_derivable_supported_soundness[OF derivation kt covering premise_values])
  have language: "paper_R_in_language signature stock A Prop"
    by (rule paper_R_named_derivable_language[OF derivation])
  show ?thesis using result by (simp only: paper_R_completed_assignment_denote[OF language typed adequate])
qed

section \<open>A finite sufficient premise support for each derivation\<close>

text \<open>
  Each derivation has a finite T⊆S such that adequacy and truth are
  needed only for T's R-language premises. This combines syntactic
  finite support with the preceding soundness theorem. It does not
  assert semantic compactness, completeness or a satisfying model.
\<close>

theorem paper_R_named_derivable_finite_semantic_support:
  assumes derivation: "paper_R_named_derivable signature stock S A"
  obtains T where "finite T" "T \<subseteq> S"
    "\<And>g. named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
      (\<And>B. B \<in> T \<Longrightarrow> paper_R_in_language signature stock B Prop \<Longrightarrow>
        named_adequate g B \<and> valuation (denote g B)) \<Longrightarrow> valuation (denote g A)"
proof -
  obtain T where finite: "finite T" and subset: "T \<subseteq> S"
    and supported: "paper_R_named_derivable signature stock T A"
    using paper_R_named_derivable_finite_support[OF derivation] by blast
  have sound: "valuation (denote g A)"
    if typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
      and premise_values: "\<And>B. B \<in> T \<Longrightarrow> paper_R_in_language signature stock B Prop \<Longrightarrow>
        named_adequate g B \<and> valuation (denote g B)" for g
  proof (rule paper_R_named_derivable_soundness[OF supported typed adequate])
    fix B
    assume member: "B \<in> T" and language: "paper_R_in_language signature stock B Prop"
    show "named_adequate g B" by (rule conjunct1[OF premise_values[OF member language]])
  next
    fix B
    assume member: "B \<in> T" and language: "paper_R_in_language signature stock B Prop"
    show "valuation (denote g B)" by (rule conjunct2[OF premise_values[OF member language]])
  qed
  show thesis by (rule that[OF finite subset sound])
qed

end

end
