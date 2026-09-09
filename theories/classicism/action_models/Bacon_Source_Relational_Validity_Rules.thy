theory Bacon_Source_Relational_Validity_Rules
  imports Bacon_Source_Relational_Validity_Basics
begin

section \<open>MP, Gen and Inst preserve validity in independent R models\<close>

text \<open>
  If A and A→B hold, B holds. If P→Q holds and n∉FV(P),
  then P→∀n.Q holds; if n∉FV(Q), then ∃n.P→Q holds.
  Source: Figure 2, p.8, and the soundness direction of Theorem 3.2,
  pp.44–45. Every operand retains its independent R-language guard.

  MP extends an assignment to cover its intermediate premise, then
  returns to the original conclusion by locality. This extension is
  supported on R names, not a total assignment on all F names.
  Gen and Inst need only a typed update at the displayed binder.
  No F model, F proof theorem, arbitrary substitution principle or
  proof-theoretic assumption appears in these validity closure laws.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_valid_MP:
  assumes al: "paper_R_in_language signature stock A Prop"
    and bl: "paper_R_in_language signature stock B Prop"
    and av: "paper_R_valid A" and implication: "paper_R_valid (named_paper_imp stock A B)"
  shows "paper_R_valid B"
proof (rule paper_R_validI[OF bl])
  fix g
  assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g B"
  let ?k = "paper_R_complete_assignment domain stock g"
  have kt: "named_env_typed domain stock ?k" by (rule paper_R_completed_assignment_typed[OF typed])
  have ka: "named_adequate ?k A" by (rule paper_R_complete_assignment_language_adequate[OF al])
  have kb: "named_adequate ?k B" by (rule paper_R_complete_assignment_language_adequate[OF bl])
  have ki: "named_adequate ?k (named_paper_imp stock A B)"
    by (rule iffD2[OF paper_R_imp_adequate_iff conjI[OF ka kb]])
  have antecedent: "valuation (denote ?k A)" by (rule paper_R_validE[OF av kt ka])
  have whole: "valuation (denote ?k (named_paper_imp stock A B))"
    by (rule paper_R_validE[OF implication kt ki])
  have conditional: "valuation (denote ?k A) \<longrightarrow> valuation (denote ?k B)"
    by (rule iffD1[OF paper_R_named_paper_imp_truth[OF al bl kt ka kb] whole])
  have result: "valuation (denote ?k B)" by (rule mp[OF conditional antecedent])
  show "valuation (denote g B)" using result
    by (simp only: paper_R_completed_assignment_denote[OF bl typed adequate])
qed

theorem paper_R_valid_Gen:
  assumes pl: "paper_R_in_language signature stock P Prop" and ql: "paper_R_in_language signature stock Q Prop"
    and nt: "stock n = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh: "n \<notin> named_fv P"
    and premise: "paper_R_valid (named_paper_imp stock P Q)"
  shows "paper_R_valid (named_paper_imp stock P (named_paper_all \<sigma> (NLam n Q)))"
proof -
  have all_language: "paper_R_in_language signature stock (named_paper_all \<sigma> (NLam n Q)) Prop"
    unfolding named_paper_all_def by (rule paper_R_binder_quantifier_language[OF ql nt rt]; simp)
  have language: "paper_R_in_language signature stock
      (named_paper_imp stock P (named_paper_all \<sigma> (NLam n Q))) Prop"
    by (rule paper_R_named_paper_imp_language[OF stock_rich pl all_language])
  show ?thesis
  proof (rule paper_R_validI[OF language])
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_imp stock P (named_paper_all \<sigma> (NLam n Q)))"
    have pa: "named_adequate g P" and all_adequate: "named_adequate g (named_paper_all \<sigma> (NLam n Q))"
      using adequate by (auto simp only: paper_R_imp_adequate_iff)
    have binder_adequate: "named_adequate g (NLam n Q)"
      using all_adequate by (simp only: named_adequate_def named_paper_primitive_fv)
    have conditional: "valuation (denote g P) \<longrightarrow> valuation (denote g (named_paper_all \<sigma> (NLam n Q)))"
    proof
      assume true_P: "valuation (denote g P)"
      have every: "\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) Q)"
      proof (intro ballI)
        fix a
        assume am: "a \<in> domain \<sigma>"
        have an: "a \<in> domain (stock n)" using am by (simp only: nt)
        have updated: "named_env_typed domain stock (g(n := Some a))"
          by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed an])
        have up: "named_adequate (g(n := Some a)) P" by (rule named_adequate_update[OF pa])
        have uq: "named_adequate (g(n := Some a)) Q"
          by (rule iffD2[OF named_binder_update_adequate_iff binder_adequate])
        have ui: "named_adequate (g(n := Some a)) (named_paper_imp stock P Q)"
          by (rule iffD2[OF paper_R_imp_adequate_iff conjI[OF up uq]])
        have valid_premise: "valuation (denote (g(n := Some a)) (named_paper_imp stock P Q))"
          by (rule paper_R_validE[OF premise updated ui])
        have implication: "valuation (denote (g(n := Some a)) P) \<longrightarrow> valuation (denote (g(n := Some a)) Q)"
          by (rule iffD1[OF paper_R_named_paper_imp_truth[OF pl ql updated up uq] valid_premise])
        have updated_P: "valuation (denote (g(n := Some a)) P)"
          by (simp only: paper_R_fresh_update_denote[OF pl typed pa an fresh]; rule true_P)
        show "valuation (denote (g(n := Some a)) Q)" by (rule mp[OF implication updated_P])
      qed
      show "valuation (denote g (named_paper_all \<sigma> (NLam n Q)))"
        by (rule iffD2[OF paper_R_forall_binder_truth[OF ql nt rt typed binder_adequate] every])
    qed
    show "valuation (denote g (named_paper_imp stock P (named_paper_all \<sigma> (NLam n Q))))"
      by (rule iffD2[OF paper_R_named_paper_imp_truth[OF pl all_language typed pa all_adequate] conditional])
  qed
qed

theorem paper_R_valid_Inst:
  assumes pl: "paper_R_in_language signature stock P Prop" and ql: "paper_R_in_language signature stock Q Prop"
    and nt: "stock n = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh: "n \<notin> named_fv Q"
    and premise: "paper_R_valid (named_paper_imp stock P Q)"
  shows "paper_R_valid (named_paper_imp stock (named_paper_ex \<sigma> (NLam n P)) Q)"
proof -
  have ex_language: "paper_R_in_language signature stock (named_paper_ex \<sigma> (NLam n P)) Prop"
    unfolding named_paper_ex_def by (rule paper_R_binder_quantifier_language[OF pl nt rt]; simp)
  have language: "paper_R_in_language signature stock
      (named_paper_imp stock (named_paper_ex \<sigma> (NLam n P)) Q) Prop"
    by (rule paper_R_named_paper_imp_language[OF stock_rich ex_language ql])
  show ?thesis
  proof (rule paper_R_validI[OF language])
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_imp stock (named_paper_ex \<sigma> (NLam n P)) Q)"
    have ex_adequate: "named_adequate g (named_paper_ex \<sigma> (NLam n P))" and qa: "named_adequate g Q"
      using adequate by (auto simp only: paper_R_imp_adequate_iff)
    have binder_adequate: "named_adequate g (NLam n P)"
      using ex_adequate by (simp only: named_adequate_def named_paper_primitive_fv)
    have conditional: "valuation (denote g (named_paper_ex \<sigma> (NLam n P))) \<longrightarrow> valuation (denote g Q)"
    proof
      assume true_exists: "valuation (denote g (named_paper_ex \<sigma> (NLam n P)))"
      have some: "\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) P)"
        by (rule iffD1[OF paper_R_exists_binder_truth[OF pl nt rt typed binder_adequate] true_exists])
      obtain a where am: "a \<in> domain \<sigma>" and true_P: "valuation (denote (g(n := Some a)) P)"
        using some by (elim bexE)
      have an: "a \<in> domain (stock n)" using am by (simp only: nt)
      have updated: "named_env_typed domain stock (g(n := Some a))"
        by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed an])
      have up: "named_adequate (g(n := Some a)) P"
        by (rule iffD2[OF named_binder_update_adequate_iff binder_adequate])
      have uq: "named_adequate (g(n := Some a)) Q" by (rule named_adequate_update[OF qa])
      have ui: "named_adequate (g(n := Some a)) (named_paper_imp stock P Q)"
        by (rule iffD2[OF paper_R_imp_adequate_iff conjI[OF up uq]])
      have valid_premise: "valuation (denote (g(n := Some a)) (named_paper_imp stock P Q))"
        by (rule paper_R_validE[OF premise updated ui])
      have implication: "valuation (denote (g(n := Some a)) P) \<longrightarrow> valuation (denote (g(n := Some a)) Q)"
        by (rule iffD1[OF paper_R_named_paper_imp_truth[OF pl ql updated up uq] valid_premise])
      have updated_Q: "valuation (denote (g(n := Some a)) Q)" by (rule mp[OF implication true_P])
      show "valuation (denote g Q)" using updated_Q
        by (simp only: paper_R_fresh_update_denote[OF ql typed qa an fresh])
    qed
    show "valuation (denote g (named_paper_imp stock (named_paper_ex \<sigma> (NLam n P)) Q))"
      by (rule iffD2[OF paper_R_named_paper_imp_truth[OF ex_language ql typed ex_adequate qa] conditional])
  qed
qed

end

end
