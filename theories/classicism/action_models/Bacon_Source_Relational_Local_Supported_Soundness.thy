theory Bacon_Source_Relational_Local_Supported_Soundness
  imports Bacon_Source_Relational_Local_Consequence Bacon_Source_Relational_H_Soundness
begin

section \<open>Local consequence at an assignment covering R formulas\<close>

text \<open>
  If S⊢HᴿA and all usable premises hold under g, then A holds
  under g, provided g covers every intermediate R formula.
  Source: the local-consequence convention of pp.7–8 and the
  soundness direction of Theorem 3.2, pp.44–45.

  This induction has only assumption, theorem and MP cases. It does
  not generalize open assumptions. Premise truth is guarded by R-language
  membership: malformed or non-R entries of S cannot be assumption
  leaves and impose no semantic requirement. The coverage premise will
  be discharged by R-supported partial-assignment completion separately.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_named_derivable_supported_soundness:
  assumes derivation: "paper_R_named_derivable signature stock S A"
    and typed: "named_env_typed domain stock g"
    and covering: "\<And>B. paper_R_in_language signature stock B Prop \<Longrightarrow> named_adequate g B"
    and premise_values: "\<And>B. B \<in> S \<Longrightarrow> paper_R_in_language signature stock B Prop \<Longrightarrow>
      valuation (denote g B)"
  shows "valuation (denote g A)"
  using derivation premise_values
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1,2)])
next
  case (Theorem A S)
  have language: "paper_R_in_language signature stock A Prop"
    by (rule paper_R_named_H_language[OF Theorem.hyps])
  have valid: "paper_R_valid A" by (rule paper_R_named_H_soundness[OF Theorem.hyps])
  show ?case by (rule paper_R_validE[OF valid typed covering[OF language]])
next
  case (MP S A B)
  have al: "paper_R_in_language signature stock A Prop"
    by (rule paper_R_named_derivable_language[OF MP.hyps(1)])
  have aa: "named_adequate g A" by (rule covering[OF al])
  have ba: "named_adequate g B" by (rule covering[OF MP.hyps(3)])
  have antecedent: "valuation (denote g A)" by (rule MP.IH(1)[OF MP.prems])
  have implication: "valuation (denote g (named_paper_imp stock A B))" by (rule MP.IH(2)[OF MP.prems])
  have conditional: "valuation (denote g A) \<longrightarrow> valuation (denote g B)"
    by (rule iffD1[OF paper_R_named_paper_imp_truth[OF al MP.hyps(3) typed aa ba] implication])
  show ?case by (rule mp[OF conditional antecedent])
qed

end

end
