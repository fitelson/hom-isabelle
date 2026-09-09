theory Bacon_Source_Relational_H_Retraction
  imports Bacon_Source_Relational_H_Retraction_Support
begin

section \<open>All ten native H constructors survive whole-proof fresh retraction\<close>

text \<open>
  The finite avoidance set follows the entire derivation. Contextual β/η
  include both endpoint name sets; MP unions its subproof supports; Gen
  and Inst also reserve their eigenvariable. PC retains its original
  Boolean template and needs no typing of unused atom assignments.
  Source role: fresh witnesses in Theorem 3.2, p.45 n.64, using exactly
  Figure 2's ten native R rules. No F proof, model, closed inhabitant,
  richness, signature inclusion or cardinality assumption is used.
\<close>

theorem paper_R_named_H_retraction_support:
  assumes derivation: "paper_R_named_H \<Sigma> G A"
  shows "\<exists>N. paper_R_H_retraction_support \<Omega> G A N"
  using derivation
proof (induction rule: paper_R_named_H.induct)
  case (PC A)
  show ?case
  proof (rule paper_R_H_retraction_at_names)
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> named_vars A"
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v A)"
      by (rule paper_R_named_H.PC[OF paper_R_retract_PC[OF PC.hyps stock]])
  qed
next
  case (UI \<sigma> F A)
  show ?case
  proof (rule paper_R_H_retraction_at_names)
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> named_vars (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A))"
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A)))"
      unfolding paper_R_retract_imp paper_R_retract_primitive named_retract.simps
      by (rule paper_R_named_H.UI; use paper_R_retract_from_language[OF UI.hyps stock]
        in \<open>simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps\<close>)
  qed
next
  case (EG F A \<sigma>)
  show ?case
  proof (rule paper_R_H_retraction_at_names)
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> named_vars (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F))"
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F)))"
      unfolding paper_R_retract_imp paper_R_retract_primitive named_retract.simps
      by (rule paper_R_named_H.EG; use paper_R_retract_from_language[OF EG.hyps stock]
        in \<open>simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps\<close>)
  qed
next
  case (Ref \<sigma> A)
  show ?case
  proof (rule paper_R_H_retraction_at_names)
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> named_vars (named_paper_eq \<sigma> A A)"
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v (named_paper_eq \<sigma> A A))"
      unfolding paper_R_retract_primitive
      by (rule paper_R_named_H.Ref; use paper_R_retract_from_language[OF Ref.hyps stock]
        in \<open>simp only: paper_R_retract_primitive\<close>)
  qed
next
  case (LL \<sigma> A B F)
  show ?case
  proof (rule paper_R_H_retraction_at_names)
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> named_vars
        (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B)))"
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v
        (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B))))"
      unfolding paper_R_retract_imp paper_R_retract_primitive named_retract.simps
      by (rule paper_R_named_H.LL; use paper_R_retract_from_language[OF LL.hyps stock]
        in \<open>simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps\<close>)
  qed
next
  case (Beta A B)
  let ?N = "named_vars A \<union> named_vars B \<union> named_vars (named_paper_iff G A B)"
  have finite: "finite ?N" by (simp add: named_vars_finite)
  have names: "named_vars (named_paper_iff G A B) \<subseteq> ?N" by blast
  show ?case
  proof (rule exI[where x="?N"], rule paper_R_H_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> ?N"
    have avoid: "\<And>\<rho>. v \<rho> \<notin> named_vars A \<union> named_vars B" using fresh by blast
    have step: "named_compatible_step named_beta_contract (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
      by (rule named_retract_beta_step[OF Beta.hyps(3) avoid])
    have whole: "paper_R_in_language \<Omega> G
        (named_paper_iff G (named_retract \<Omega> v A) (named_retract \<Omega> v B)) Prop"
      using paper_R_retract_from_language[OF Beta.hyps(4) stock] by (simp only: paper_R_retract_iff)
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v (named_paper_iff G A B))"
      by (simp only: paper_R_retract_iff; rule paper_R_named_H.Beta[OF
        paper_R_retract_from_language[OF Beta.hyps(1) stock]
        paper_R_retract_from_language[OF Beta.hyps(2) stock] step whole])
  qed
next
  case (Eta A B)
  let ?N = "named_vars A \<union> named_vars B \<union> named_vars (named_paper_iff G A B)"
  have finite: "finite ?N" by (simp add: named_vars_finite)
  have names: "named_vars (named_paper_iff G A B) \<subseteq> ?N" by blast
  show ?case
  proof (rule exI[where x="?N"], rule paper_R_H_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> ?N"
    have avoid: "\<And>\<rho>. v \<rho> \<notin> named_vars A \<union> named_vars B" using fresh by blast
    have step: "named_compatible_step named_eta_contract (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
      by (rule named_retract_eta_step[OF Eta.hyps(3) avoid])
    have whole: "paper_R_in_language \<Omega> G
        (named_paper_iff G (named_retract \<Omega> v A) (named_retract \<Omega> v B)) Prop"
      using paper_R_retract_from_language[OF Eta.hyps(4) stock] by (simp only: paper_R_retract_iff)
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v (named_paper_iff G A B))"
      by (simp only: paper_R_retract_iff; rule paper_R_named_H.Eta[OF
        paper_R_retract_from_language[OF Eta.hyps(1) stock]
        paper_R_retract_from_language[OF Eta.hyps(2) stock] step whole])
  qed
next
  case (MP A B)
  obtain N where first: "paper_R_H_retraction_support \<Omega> G A N" using MP.IH(1) by blast
  obtain K where second: "paper_R_H_retraction_support \<Omega> G (named_paper_imp G A B) K" using MP.IH(2) by blast
  let ?U = "N \<union> K \<union> named_vars B"
  have finite: "finite ?U" using paper_R_H_retraction_support_finite[OF first]
    paper_R_H_retraction_support_finite[OF second] by (simp add: named_vars_finite)
  have names: "named_vars B \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule paper_R_H_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> ?U"
    have fn: "\<And>\<rho>. v \<rho> \<notin> N" and fk: "\<And>\<rho>. v \<rho> \<notin> K" using fresh by blast+
    have antecedent: "paper_R_named_H \<Omega> G (named_retract \<Omega> v A)"
      by (rule paper_R_H_retraction_support_apply[OF first stock fn])
    have implication: "paper_R_named_H \<Omega> G (named_paper_imp G (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using paper_R_H_retraction_support_apply[OF second stock fk] by (simp only: paper_R_retract_imp)
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v B)"
      by (rule paper_R_named_H.MP[OF antecedent implication paper_R_retract_from_language[OF MP.hyps(3) stock]])
  qed
next
  case (Gen P Q n \<sigma>)
  obtain N where support: "paper_R_H_retraction_support \<Omega> G (named_paper_imp G P Q) N" using Gen.IH by blast
  let ?A = "named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))"
  let ?U = "insert n (N \<union> named_vars ?A)"
  have finite: "finite ?U" using paper_R_H_retraction_support_finite[OF support] by (simp add: named_vars_finite)
  have names: "named_vars ?A \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule paper_R_H_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> ?U"
    have fn: "\<And>\<rho>. v \<rho> \<notin> N" and vn: "\<And>\<rho>. v \<rho> \<noteq> n" using fresh by blast+
    have old: "paper_R_named_H \<Omega> G (named_paper_imp G (named_retract \<Omega> v P) (named_retract \<Omega> v Q))"
      using paper_R_H_retraction_support_apply[OF support stock fn] by (simp only: paper_R_retract_imp)
    have nf: "n \<notin> named_fv (named_retract \<Omega> v P)" by (rule named_retract_fresh[OF Gen.hyps(3) vn])
    have language: "paper_R_in_language \<Omega> G
      (named_paper_imp G (named_retract \<Omega> v P) (named_paper_all \<sigma> (NLam n (named_retract \<Omega> v Q)))) Prop"
      using paper_R_retract_from_language[OF Gen.hyps(4) stock]
      by (simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps)
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v ?A)"
      by (simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps;
        rule paper_R_named_H.Gen[OF old Gen.hyps(2) nf language])
  qed
next
  case (Inst P Q n \<sigma>)
  obtain N where support: "paper_R_H_retraction_support \<Omega> G (named_paper_imp G P Q) N" using Inst.IH by blast
  let ?A = "named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q"
  let ?U = "insert n (N \<union> named_vars ?A)"
  have finite: "finite ?U" using paper_R_H_retraction_support_finite[OF support] by (simp add: named_vars_finite)
  have names: "named_vars ?A \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule paper_R_H_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
      and fresh: "\<And>\<rho>. v \<rho> \<notin> ?U"
    have fn: "\<And>\<rho>. v \<rho> \<notin> N" and vn: "\<And>\<rho>. v \<rho> \<noteq> n" using fresh by blast+
    have old: "paper_R_named_H \<Omega> G (named_paper_imp G (named_retract \<Omega> v P) (named_retract \<Omega> v Q))"
      using paper_R_H_retraction_support_apply[OF support stock fn] by (simp only: paper_R_retract_imp)
    have nf: "n \<notin> named_fv (named_retract \<Omega> v Q)" by (rule named_retract_fresh[OF Inst.hyps(3) vn])
    have language: "paper_R_in_language \<Omega> G
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n (named_retract \<Omega> v P))) (named_retract \<Omega> v Q)) Prop"
      using paper_R_retract_from_language[OF Inst.hyps(4) stock]
      by (simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps)
    show "paper_R_named_H \<Omega> G (named_retract \<Omega> v ?A)"
      by (simp only: paper_R_retract_imp paper_R_retract_primitive named_retract.simps;
        rule paper_R_named_H.Inst[OF old Inst.hyps(2) nf language])
  qed
qed

end
