theory Bacon_Source_Relational_Box_Truth
  imports Bacon_Source_Relational_Box_Syntax Bacon_Source_Relational_Identity_Axiom_Truth
begin

section \<open>Truth of the literal Figure 1 necessity operator\<close>

text \<open>
  □P is the application of λp.(p=ₜ(p∨¬p)), not a primitive
  modal operator. Its β contraction identifies its denotation with
  that of P=ₜ(P∨¬P). The independent BBK identity clause then
  gives the truth condition below, under the original typed adequate
  partial assignment. No Necessitation, PE, or C premise is used.
  Source: Figure 1, p.6, and Definition 3.1, pp.43–44.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_named_box_denote:
  assumes language: "paper_R_in_language signature stock P Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g P"
  shows "denote g (paper_R_named_box stock P) =
    denote g (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))"
proof -
  let ?B = "paper_R_named_box stock P"
  let ?E = "named_paper_eq Prop P (named_paper_or P (named_paper_not P))"
  have bl: "paper_R_in_language signature stock ?B Prop"
    by (rule paper_R_named_box_language[OF stock_rich language])
  have el: "paper_R_in_language signature stock ?E Prop"
    by (rule paper_R_named_eq_language[OF language
      paper_R_named_or_language[OF language paper_R_named_not_language[OF language]]])
  have bt: "paper_R_has_type stock ?B Prop" and et: "paper_R_has_type stock ?E Prop"
    using bl el unfolding paper_R_in_language_def by blast+
  have raw: "paper_R_raw_beta_eta stock Prop ?B ?E"
    by (rule paper_R_raw_beta_eta.Beta[OF bt et paper_R_named_box_beta])
  have ba: "named_adequate g ?B" using adequate
    by (simp only: named_adequate_def paper_R_named_box_fv)
  have ea: "named_adequate g ?E" using adequate
    by (simp add: named_adequate_def named_paper_primitive_fv)
  show ?thesis by (rule denote_beta_eta[OF raw bl el typed ba ea])
qed

theorem paper_R_named_box_truth:
  assumes language: "paper_R_in_language signature stock P Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g P"
  shows "valuation (denote g (paper_R_named_box stock P)) =
    (denote g P = denote g (named_paper_or P (named_paper_not P)))"
proof -
  have tl: "paper_R_in_language signature stock (named_paper_or P (named_paper_not P)) Prop"
    by (rule paper_R_named_or_language[OF language paper_R_named_not_language[OF language]])
  have ta: "named_adequate g (named_paper_or P (named_paper_not P))"
    using adequate by (simp add: named_adequate_def named_paper_primitive_fv)
  show ?thesis by (simp only: paper_R_named_box_denote[OF language typed adequate] named_paper_eq_def;
    rule valuation_identity[OF language tl typed adequate ta])
qed

lemma paper_R_named_tautology_truth:
  assumes language: "paper_R_in_language signature stock P Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g P"
  shows "valuation (denote g (named_paper_or P (named_paper_not P)))"
proof -
  have nl: "paper_R_in_language signature stock (named_paper_not P) Prop"
    by (rule paper_R_named_not_language[OF language])
  have na: "named_adequate g (named_paper_not P)"
    using adequate by (simp add: named_adequate_def named_paper_primitive_fv)
  show ?thesis by (simp only: paper_R_named_or_truth[OF language nl typed adequate na]
    paper_R_named_not_truth[OF language typed adequate]; blast)
qed

end

end
