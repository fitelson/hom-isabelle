theory Bacon_Source_Relational_Henkin_Union_Consistency
  imports Bacon_Source_Relational_Henkin_Full_Premises Bacon_Source_Relational_Henkin_Stage_Consistency
begin

section \<open>Each stage stays consistent in the FULL signature\<close>

text \<open>
  Consistency in Σₖ alone does not yet exclude proofs using later
  constants. First apply the proved native signature-conservativity
  theorem: every premise of Tₖ belongs to Σₖ, so consistency of
  Tₖ transfers to Σ∞. This step uses the actual stage theorem,
  not an additional full-signature consistency premise.
  Source: Theorem 3.2, footnote 64, p.45.
\<close>

lemma paper_R_henkin_stage_consistent_full_signature:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "paper_R_named_consistent (paper_R_henkin_full_signature \<Sigma> G) G (paper_R_henkin_premises \<Sigma> G S k)"
proof -
  let ?T = "paper_R_henkin_premises \<Sigma> G S k"
  have stage_consistent: "paper_R_named_consistent (paper_R_henkin_signature \<Sigma> G k) G ?T"
    by (rule paper_R_henkin_premises_consistent[OF rich source consistent])
  have stage_closed: "paper_R_closed_theory (paper_R_henkin_signature \<Sigma> G k) G ?T"
    by (rule paper_R_henkin_premises_closed[OF rich source])
  have names: "named_in_signature (paper_R_henkin_signature \<Sigma> G k) A" if member: "A \<in> ?T" for A
  proof -
    have sentence: "paper_R_sentence (paper_R_henkin_signature \<Sigma> G k) G A"
      by (rule paper_R_closed_theory_member[OF stage_closed member])
    have language: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G A Prop"
      by (rule paper_R_sentence_language[OF sentence])
    show ?thesis using language unfolding paper_R_in_language_def by (rule conjunct2)
  qed
  show ?thesis by (rule paper_R_named_consistent_signature_transport[
    where \<Omega>="paper_R_henkin_signature \<Sigma> G k" and \<Sigma>="paper_R_henkin_full_signature \<Sigma> G"
      and G=G and S="?T", OF rich stage_consistent names])
qed

section \<open>Finite support proves consistency of the actual union\<close>

theorem paper_R_henkin_full_premises_consistent:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "paper_R_named_consistent (paper_R_henkin_full_signature \<Sigma> G) G (paper_R_henkin_full_premises \<Sigma> G S)"
proof (rule iffD2[OF paper_R_named_consistent_finite_character], intro allI impI)
  fix U
  assume finite: "finite U" and subset: "U \<subseteq> paper_R_henkin_full_premises \<Sigma> G S"
  obtain k where stage: "U \<subseteq> paper_R_henkin_premises \<Sigma> G S k"
    using paper_R_henkin_finite_premises_stage_bound[OF finite subset] by blast
  have stage_consistent: "paper_R_named_consistent (paper_R_henkin_full_signature \<Sigma> G) G
    (paper_R_henkin_premises \<Sigma> G S k)"
    by (rule paper_R_henkin_stage_consistent_full_signature[OF rich source consistent])
  show "paper_R_named_consistent (paper_R_henkin_full_signature \<Sigma> G) G U"
    by (rule paper_R_named_consistent_mono[
      where \<Sigma>="paper_R_henkin_full_signature \<Sigma> G" and G=G
        and S=U and T="paper_R_henkin_premises \<Sigma> G S k", OF stage_consistent stage])
qed

end
