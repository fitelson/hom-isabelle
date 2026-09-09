theory Bacon_Source_Relational_Separating_Consistency
  imports Bacon_Source_Relational_H_Theory_Boxed_Consequences
    Bacon_Source_Relational_H_Theory_Modal_PE Bacon_Source_Relational_Identity_Stability
    Bacon_Source_Relational_Local_Validity Bacon_Source_Relational_Consistency
begin

section \<open>The separating negation is consistent with true stable premises\<close>

text \<open>
  M validates T and Δ, but gives P and Q different proposition values
  under a typed adequate assignment. If T is an H-theory closed under
  PE and every E∈Δ satisfies E→□E∈T, then
  T∪Δ∪{¬(P↔Q)} is H-consistent.

  If P↔Q were locally derivable from T∪Δ, the preceding finite
  argument would derive □(P↔Q). Modalized PE would give P=Q,
  contradicting M's actual identity clause. The consistent-negation
  lemma then supplies the conclusion.

  Source: the central consistency argument of p.51–52 n.73. M is
  required to validate only T and the positive premises Δ, never the
  separating negation. This conditional theorem does not construct a
  naming expansion, prove that a theory extension preserves PE, or
  construct a separating homomorphism.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_separating_negation_consistent:
  assumes theory_h: "paper_R_H_theory signature stock T"
    and pe: "paper_R_PE_closed signature stock T"
    and premise_boxes: "\<And>E. E \<in> \<Delta> \<Longrightarrow>
      named_paper_imp stock E (paper_R_named_box stock E) \<in> T"
    and theory_valid: "\<And>E. E \<in> T \<Longrightarrow> paper_R_valid E"
    and extra_valid: "\<And>E. E \<in> \<Delta> \<Longrightarrow> paper_R_valid E"
    and pl: "paper_R_in_language signature stock P Prop"
    and ql: "paper_R_in_language signature stock Q Prop"
    and typed: "named_env_typed domain stock g"
    and pa: "named_adequate g P" and qa: "named_adequate g Q"
    and different: "denote g P \<noteq> denote g Q"
  shows "paper_R_named_consistent signature stock
    (insert (named_paper_not (named_paper_iff stock P Q)) (T \<union> \<Delta>))"
proof -
  let ?S = "T \<union> \<Delta>"
  let ?I = "named_paper_iff stock P Q"
  let ?E = "named_paper_eq Prop P Q"
  have il: "paper_R_in_language signature stock ?I Prop"
    by (rule paper_R_named_paper_iff_language[OF stock_rich pl ql])
  have el: "paper_R_in_language signature stock ?E Prop"
    by (rule paper_R_named_identity_language[OF pl ql])
  have underivable: "\<not> paper_R_named_derivable signature stock ?S ?I"
  proof
    assume proof_I: "paper_R_named_derivable signature stock ?S ?I"
    have boxed: "paper_R_named_derivable signature stock ?S (paper_R_named_box stock ?I)"
      by (rule paper_R_H_theory_necessitate_local_consequence[OF stock_rich theory_h pe premise_boxes proof_I])
    have modal_member: "named_paper_imp stock (paper_R_named_box stock ?I) ?E \<in> T"
      by (rule paper_R_H_theory_modal_PE[OF stock_rich theory_h pe pl ql])
    have modal_language: "paper_R_in_language signature stock
        (named_paper_imp stock (paper_R_named_box stock ?I) ?E) Prop"
      by (rule paper_R_H_theory_language[OF theory_h modal_member])
    have modal_local: "paper_R_named_derivable signature stock ?S
        (named_paper_imp stock (paper_R_named_box stock ?I) ?E)"
      by (rule paper_R_named_derivable.Assumption[OF UnI1[OF modal_member] modal_language])
    have equality: "paper_R_named_derivable signature stock ?S ?E"
      by (rule paper_R_named_derivable.MP[OF boxed modal_local el])
    have valid_equality: "paper_R_valid ?E"
    proof (rule paper_R_named_derivable_valid[OF equality])
      fix A
      assume "A \<in> ?S"
      then show "paper_R_valid A" using theory_valid extra_valid by blast
    qed
    have adequate: "named_adequate g ?E"
      using pa qa by (auto simp: named_adequate_def named_paper_primitive_fv)
    have true_equality: "valuation (denote g ?E)" by (rule paper_R_validE[OF valid_equality typed adequate])
    have same: "denote g P = denote g Q"
      by (rule iffD1[OF valuation_identity[OF pl ql typed pa qa]];
        use true_equality in \<open>simp only: named_paper_eq_def\<close>)
    show False using different same by contradiction
  qed
  show ?thesis by (rule paper_R_named_consistent_insert_not[OF stock_rich il underivable])
qed

corollary paper_R_identity_diagram_separating_consistent:
  assumes theory_h: "paper_R_H_theory signature stock T"
    and pe: "paper_R_PE_closed signature stock T"
    and identities: "\<And>E. E \<in> \<Delta> \<Longrightarrow> \<exists>\<sigma> A B.
      E = named_paper_eq \<sigma> A B \<and> paper_R_in_language signature stock A \<sigma> \<and>
      paper_R_in_language signature stock B \<sigma>"
    and theory_valid: "\<And>E. E \<in> T \<Longrightarrow> paper_R_valid E"
    and diagram_valid: "\<And>E. E \<in> \<Delta> \<Longrightarrow> paper_R_valid E"
    and pl: "paper_R_in_language signature stock P Prop"
    and ql: "paper_R_in_language signature stock Q Prop"
    and typed: "named_env_typed domain stock g"
    and pa: "named_adequate g P" and qa: "named_adequate g Q"
    and different: "denote g P \<noteq> denote g Q"
  shows "paper_R_named_consistent signature stock
    (insert (named_paper_not (named_paper_iff stock P Q)) (T \<union> \<Delta>))"
proof (rule paper_R_separating_negation_consistent[
    OF theory_h pe _ theory_valid diagram_valid pl ql typed pa qa different])
  fix E
  assume member: "E \<in> \<Delta>"
  obtain \<sigma> A B where shape: "E = named_paper_eq \<sigma> A B"
    and al: "paper_R_in_language signature stock A \<sigma>" and bl: "paper_R_in_language signature stock B \<sigma>"
    using identities[OF member] by blast
  show "named_paper_imp stock E (paper_R_named_box stock E) \<in> T"
    by (simp only: shape; rule paper_R_H_theory_identity_stability[OF stock_rich theory_h pe al bl])
qed

end

end
