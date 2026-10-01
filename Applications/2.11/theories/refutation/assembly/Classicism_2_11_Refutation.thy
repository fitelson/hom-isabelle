theory Classicism_2_11_Refutation
  imports Classicism_2_11_Hypotheses
    "Classicism_2_11_Semantics.Classicism_2_11_Rigid_Semantics"
    "Classicism_2_11_Rigidity.Classicism_2_11_Rigidity_Transfer"
begin

section \<open>Proposition 2.11 does not hold\<close>

text \<open>
  Proposition 2.11 (Classicism, 1 July 2022 draft, p.30): □Atomicity,
  Boolean Completeness, and BF jointly imply Rigid Comprehension.
  "Jointly imply" is derivability in the smallest H-theory containing
  Classicism and the hypothesis instances (c211_proves; pp.7, 12).

  The concrete action model validates every Classicism theorem and every
  hypothesis instance (□Atomicity and Boolean Completeness at every
  relational type, BF at every R type and formula), but the Rigid
  Comprehension instance for properties of propositions is false at its
  root. By soundness of c211_proves, that instance is not derivable.
\<close>

abbreviation c211_model :: "'c ssignature \<Rightarrow> bool" where
  "c211_model S \<equiv> paper_ZF_action_model S c211_G (explode raw_W) pa_Ar Fst Snd pa_compose pa_id
    raw_root paper_D paper_T paper_I"

theorem c211_conclusion_not_valid: "\<not> c211_concrete_valid S c211_conclusion"
  unfolding c211_conclusion_def
  by (rule c211_RC_not_valid[OF concrete_paper_standard_model c211_concrete_pRC_false])

theorem c211_countermodel:
  shows "c211_model S"
    and "\<And>A. paper_R_classicism_proves S c211_G A \<Longrightarrow> c211_concrete_valid S A"
    and "\<And>A. A \<in> c211_hypotheses S \<Longrightarrow> c211_concrete_valid S A"
    and "paper_R_in_language S c211_G c211_conclusion Prop"
    and "\<not> c211_concrete_valid S c211_conclusion"
proof -
  show "c211_model S" by (rule concrete_paper_standard_model)
  show "c211_concrete_valid S A" if "paper_R_classicism_proves S c211_G A" for A
    by (rule c211_soundness[OF concrete_paper_standard_model _
      c211_proves_classicism_mono[where Ax="{}", OF that]]) simp
  show "c211_concrete_valid S A" if "A \<in> c211_hypotheses S" for A
    by (rule c211_hypotheses_valid[OF that])
  show "paper_R_in_language S c211_G c211_conclusion Prop" by (rule c211_conclusion_language)
  show "\<not> c211_concrete_valid S c211_conclusion" by (rule c211_conclusion_not_valid)
qed

theorem proposition_2_11_refuted:
  "\<not> c211_proves S c211_G (c211_hypotheses S) c211_conclusion"
  by (rule c211_underivable[OF concrete_paper_standard_model
      ballI[OF c211_hypotheses_valid] c211_conclusion_not_valid])

end
