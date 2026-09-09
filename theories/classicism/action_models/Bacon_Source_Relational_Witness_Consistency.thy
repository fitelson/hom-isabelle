theory Bacon_Source_Relational_Witness_Consistency
  imports Bacon_Source_Relational_Witness_Propositional Bacon_Source_Relational_Witness_Eta
    Bacon_Source_Relational_Local_Signature_Conservativity
begin

section \<open>One genuinely fresh conditional witness preserves consistency\<close>

text \<open>
  For closed F:σ→t, adjoin Wc=(∃σF→Fc) with c∉Ωσ. If a
  contradiction follows, first discharge Wc and derive ¬Wc from S.
  Only then retract the proof to Ω, fixing every original premise.
  The fresh σ variable x gives ¬(E→Fx), hence E and Fx→¬E.
  The proved local Inst rule is applicable because the premises and E
  are closed. It gives (∃x.Fx)→¬E; contextual η and E then yield ¬E.

  Source: the fresh-witness step of Theorem 3.2, p.45 n.64.
  No local Gen/Inst constructor, semantic model, F theorem, countability
  or closed inhabitant is assumed. S may be infinite. This one-step
  theorem assumes the displayed fresh name; supplying fresh names for
  arbitrary signatures and assembling witness families remain separate.
\<close>

theorem paper_R_named_consistent_fresh_witness:
  assumes rich: "paper_R_rich G" and closed_S: "paper_R_closed_theory \<Omega> G S"
    and consistent: "paper_R_named_consistent \<Omega> G S"
    and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and closed_F: "named_fv F = {}" and fresh_c: "c \<notin> \<Omega> \<sigma>"
  shows "paper_R_named_consistent (paper_R_add_constant \<Omega> \<sigma> c) G
    (insert (paper_R_witness_axiom G \<sigma> F c) S)"
proof (rule paper_R_named_consistentI)
  fix A
  let ?\<Sigma> = "paper_R_add_constant \<Omega> \<sigma> c"
  let ?W = "paper_R_witness_axiom G \<sigma> F c"
  let ?E = "named_paper_ex \<sigma> F"
  assume positive: "paper_R_named_derivable ?\<Sigma> G (insert ?W S) A"
    and negative: "paper_R_named_derivable ?\<Sigma> G (insert ?W S) (named_paper_not A)"
  have wl: "paper_R_in_language ?\<Sigma> G ?W Prop" by (rule paper_R_witness_language[OF rich predicate])
  have failed: "paper_R_named_derivable ?\<Sigma> G S (named_paper_not ?W)"
    by (rule paper_R_named_derivable_not_intro[OF rich wl positive negative])
  have premise_names: "named_in_signature \<Omega> B" if member: "B \<in> S" for B
  proof -
    have language: "paper_R_in_language \<Omega> G B Prop"
      by (rule paper_R_sentence_language[OF paper_R_closed_theory_member[OF closed_S member]])
    show ?thesis using language unfolding paper_R_in_language_def by blast
  qed
  obtain N where support: "paper_R_local_retraction_support \<Omega> G S (named_paper_not ?W) N"
    using paper_R_named_derivable_retraction_support[OF failed premise_names] by blast
  have finite: "finite N" by (rule paper_R_local_retraction_support_finite[OF support])
  obtain v where stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
    and fresh: "\<And>\<rho>. v \<rho> \<notin> N"
    by (rule paper_R_rich_retraction_family[OF rich finite]; rule that; assumption)
  let ?x = "v \<sigma>"
  let ?B = "NApp F (NVar ?x)"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have xt: "G ?x = \<sigma>" by (rule stock[OF rt])
  have fn: "named_in_signature \<Omega> F" using predicate unfolding paper_R_in_language_def by blast
  have retracted: "paper_R_named_derivable \<Omega> G S (named_paper_not (named_paper_imp G ?E ?B))"
    using paper_R_local_retraction_support_apply[OF support stock fresh]
    by (simp only: paper_R_retract_primitive paper_R_witness_retract[OF fn fresh_c])
  have el: "paper_R_in_language \<Omega> G ?E Prop" by (rule paper_R_predicate_exists_language[OF predicate])
  have vl: "paper_R_in_language \<Omega> G (NVar ?x) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Omega> and G=G and n="?x", OF xt rt])
  have bl: "paper_R_in_language \<Omega> G ?B Prop" by (rule paper_R_language_App[OF predicate vl])
  have components: "paper_R_named_derivable \<Omega> G S ?E \<and>
      paper_R_named_derivable \<Omega> G S (named_paper_imp G ?B (named_paper_not ?E))"
    by (rule paper_R_named_derivable_not_imp_components[OF rich el bl retracted])
  have nel: "paper_R_in_language \<Omega> G (named_paper_not ?E) Prop" by (rule paper_R_named_not_language[OF el])
  have nef: "?x \<notin> named_fv (named_paper_not ?E)"
    by (simp only: named_paper_primitive_fv closed_F; simp)
  have source_premises: "paper_R_in_language \<Omega> G C Prop \<and> ?x \<notin> named_fv C" if member: "C \<in> S" for C
  proof -
    have sentence: "paper_R_sentence \<Omega> G C" by (rule paper_R_closed_theory_member[OF closed_S member])
    show ?thesis using paper_R_sentence_language[OF sentence] paper_R_sentence_closed[OF sentence] by simp
  qed
  let ?L = "named_paper_ex \<sigma> (NLam ?x ?B)"
  have instantiated: "paper_R_named_derivable \<Omega> G S (named_paper_imp G ?L (named_paper_not ?E))"
    by (rule paper_R_named_derivable_Inst[OF rich bl nel xt rt nef source_premises conjunct2[OF components]])
  have xf: "?x \<notin> named_fv F" by (simp only: closed_F; simp)
  have expanded: "paper_R_named_H \<Omega> G (named_paper_imp G ?E ?L)"
    by (rule paper_R_named_H_exists_eta_expand[OF rich predicate xt xf])
  have ll: "paper_R_in_language \<Omega> G ?L Prop" by (rule paper_R_local_exists_binder_language[OF bl xt rt])
  have exists_expanded: "paper_R_named_derivable \<Omega> G S ?L"
    by (rule paper_R_named_derivable.MP[OF conjunct1[OF components] paper_R_named_derivable.Theorem[OF expanded] ll])
  have negated: "paper_R_named_derivable \<Omega> G S (named_paper_not ?E)"
    by (rule paper_R_named_derivable.MP[OF exists_expanded instantiated nel])
  show False by (rule paper_R_named_consistentD[OF consistent conjunct1[OF components] negated])
qed

end
