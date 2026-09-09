theory Bacon_Source_Relational_Local_Retraction
  imports Bacon_Source_Relational_H_Retraction Bacon_Source_Relational_Local_Consequence
begin

section \<open>Retract a finite local proof while retaining its premise set\<close>

text \<open>
  Every member of S whose constants belong to Ω is fixed by retraction.
  Thus a local Σ proof from S retracts to an Ω proof from the SAME S.
  The conclusion may contain foreign constants and is retracted.
  The finite avoidance set follows the proof, including H-theorem
  subproofs, not the union of free variables of the possibly infinite S.
  Only Assumption, Theorem and MP are used locally; no local Gen/Inst
  rule is introduced. Source role: Theorem 3.2, p.45 n.64.
\<close>

definition paper_R_local_retraction_support where
  "paper_R_local_retraction_support \<Omega> G S A N \<longleftrightarrow>
    finite N \<and> named_vars A \<subseteq> N \<and>
    (\<forall>v. (\<forall>\<rho>. paper_R_type \<rho> \<longrightarrow> G (v \<rho>) = \<rho>) \<longrightarrow>
      (\<forall>\<rho>. v \<rho> \<notin> N) \<longrightarrow>
      paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A))"

lemma paper_R_local_retraction_supportI:
  assumes finite: "finite N" and names: "named_vars A \<subseteq> N"
    and transform: "\<And>v. (\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>) \<Longrightarrow>
      (\<And>\<rho>. v \<rho> \<notin> N) \<Longrightarrow> paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
  shows "paper_R_local_retraction_support \<Omega> G S A N"
  using finite names transform unfolding paper_R_local_retraction_support_def by blast

lemma paper_R_local_retraction_support_finite:
  "paper_R_local_retraction_support \<Omega> G S A N \<Longrightarrow> finite N"
  unfolding paper_R_local_retraction_support_def by blast

lemma paper_R_local_retraction_support_apply:
  assumes support: "paper_R_local_retraction_support \<Omega> G S A N"
    and stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
    and fresh: "\<And>\<rho>. v \<rho> \<notin> N"
  shows "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
  using support stock fresh unfolding paper_R_local_retraction_support_def by blast

theorem paper_R_named_derivable_retraction_support:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A"
    and names: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Omega> B"
  shows "\<exists>N. paper_R_local_retraction_support \<Omega> G S A N"
  using derivation names
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  show ?case
  proof (rule exI[where x="named_vars A"], rule paper_R_local_retraction_supportI[OF named_vars_finite subset_refl])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> named_vars A"
    have declared: "named_in_signature \<Omega> A" by (rule Assumption.prems[OF Assumption.hyps(1)])
    have fixed: "named_retract \<Omega> v A = A" by (rule named_retract_fixed[OF declared])
    have language: "paper_R_in_language \<Omega> G A Prop"
      using Assumption.hyps(2) declared unfolding paper_R_in_language_def by blast
    show "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
      by (simp only: fixed; rule paper_R_named_derivable.Assumption[OF Assumption.hyps(1) language])
  qed
next
  case (Theorem A S)
  obtain N where support: "paper_R_H_retraction_support \<Omega> G A N"
    using paper_R_named_H_retraction_support[where \<Omega>=\<Omega>, OF Theorem.hyps] by blast
  have finite: "finite N" by (rule paper_R_H_retraction_support_finite[OF support])
  have names: "named_vars A \<subseteq> N" using support unfolding paper_R_H_retraction_support_def by blast
  show ?case
  proof (rule exI[where x=N], rule paper_R_local_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> N"
    show "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
      by (rule paper_R_named_derivable.Theorem[OF paper_R_H_retraction_support_apply[OF support stock fresh]])
  qed
next
  case (MP S A B)
  obtain N where first: "paper_R_local_retraction_support \<Omega> G S A N" using MP.IH(1)[OF MP.prems] by blast
  obtain K where second: "paper_R_local_retraction_support \<Omega> G S (named_paper_imp G A B) K"
    using MP.IH(2)[OF MP.prems] by blast
  let ?U = "N \<union> K \<union> named_vars B"
  have finite: "finite ?U" using paper_R_local_retraction_support_finite[OF first]
    paper_R_local_retraction_support_finite[OF second] by (simp add: named_vars_finite)
  have names: "named_vars B \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule paper_R_local_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> ?U"
    have fn: "\<And>\<rho>. v \<rho> \<notin> N" and fk: "\<And>\<rho>. v \<rho> \<notin> K" using fresh by blast+
    have antecedent: "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
      by (rule paper_R_local_retraction_support_apply[OF first stock fn])
    have implication: "paper_R_named_derivable \<Omega> G S
      (named_paper_imp G (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using paper_R_local_retraction_support_apply[OF second stock fk] by (simp only: paper_R_retract_imp)
    show "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v B)"
      by (rule paper_R_named_derivable.MP[OF antecedent implication paper_R_retract_from_language[OF MP.hyps(3) stock]])
  qed
qed

end
