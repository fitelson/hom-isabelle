theory Bacon_Source_Relational_Local_Consequence
  imports Bacon_Source_Relational_H
begin

section \<open>Local R consequence and finite premise support\<close>

text \<open>
  S⊢HᴿA uses assumptions, Hᴿ theorems and modus ponens.
  Source: Bacon–Dorr pp.7–8. Gen and Inst apply inside theoremhood;
  they are not unrestricted rules on formulas assumed in S.
  Every intermediate formula remains in R.

  The following finite-support theorem is syntactic. It allows an
  arbitrary premise set S and does not assert compactness or model
  existence. No F theoremhood, semantic validity or consistency
  principle defines this local consequence relation.
\<close>

inductive paper_R_named_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    'c paper_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop \<Longrightarrow>
    paper_R_named_derivable \<Sigma> G S A"
| Theorem: "paper_R_named_H \<Sigma> G A \<Longrightarrow> paper_R_named_derivable \<Sigma> G S A"
| MP: "paper_R_named_derivable \<Sigma> G S A \<Longrightarrow>
    paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B) \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> paper_R_named_derivable \<Sigma> G S B"

lemma paper_R_named_derivable_language:
  "paper_R_named_derivable \<Sigma> G S A \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
  by (induction rule: paper_R_named_derivable.induct)
    (auto intro: paper_R_named_H_language)

lemma paper_R_named_derivable_mono:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A" and subset: "S \<subseteq> T"
  shows "paper_R_named_derivable \<Sigma> G T A"
  using derivation subset
  by (induction rule: paper_R_named_derivable.induct)
    (blast intro: paper_R_named_derivable.intros)+

theorem paper_R_named_derivable_finite_support:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A"
  shows "\<exists>T. finite T \<and> T \<subseteq> S \<and> paper_R_named_derivable \<Sigma> G T A"
  using derivation
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  have single: "paper_R_named_derivable \<Sigma> G {A} A"
    by (rule paper_R_named_derivable.Assumption; (rule singletonI | rule Assumption.hyps(2)))
  show ?case using single Assumption.hyps(1) by (intro exI[where x="{A}"]) auto
next
  case (Theorem A S)
  have empty: "paper_R_named_derivable \<Sigma> G {} A"
    by (rule paper_R_named_derivable.Theorem[OF Theorem.hyps])
  show ?case using empty by (intro exI[where x="{}"]) simp
next
  case (MP S A B)
  obtain T where tf: "finite T" and ts: "T \<subseteq> S"
    and tp: "paper_R_named_derivable \<Sigma> G T A" using MP.IH(1) by blast
  obtain U where uf: "finite U" and us: "U \<subseteq> S"
    and up: "paper_R_named_derivable \<Sigma> G U (named_paper_imp G A B)"
    using MP.IH(2) by blast
  have first: "paper_R_named_derivable \<Sigma> G (T \<union> U) A"
    by (rule paper_R_named_derivable_mono[OF tp Un_upper1])
  have second: "paper_R_named_derivable \<Sigma> G (T \<union> U) (named_paper_imp G A B)"
    by (rule paper_R_named_derivable_mono[OF up Un_upper2])
  have result: "paper_R_named_derivable \<Sigma> G (T \<union> U) B"
    by (rule paper_R_named_derivable.MP[OF first second MP.hyps(3)])
  show ?case using tf uf ts us result by (intro exI[where x="T \<union> U"]) auto
qed

end
