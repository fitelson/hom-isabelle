theory Bacon_Source_Relational_Tautology_Profile
  imports Bacon_Source_Relational_Box_Truth Bacon_Source_Relational_Subcategory
    Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>A tautology is true after every outgoing homomorphism\<close>

lemma paper_R_outgoing_tautology_truth:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and language: "paper_R_in_language \<Sigma> G P Prop"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g P"
    and arrow: "h \<in> Arrows" and origin: "paper_arrow_source h = M"
  shows "paper_bbk_valuation (paper_arrow_target h)
    (paper_arrow_map h Prop (paper_bbk_denote M g (named_paper_or P (named_paper_not P))))"
proof -
  let ?N = "paper_arrow_target h"
  let ?A = "named_paper_or P (named_paper_not P)"
  let ?k = "paper_hom_assignment G (paper_arrow_map h) g"
  have selected: "h \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    by (rule paper_R_bbk_subcategory_arrow[OF category arrow])
  have target: "?N \<in> Obj"
    by (rule paper_typed_arrows_target[OF paper_R_bbk_arrows_typed[OF selected]])
  have target_valid: "paper_R_bbk_data_valid \<Sigma> G ?N"
    by (rule paper_R_bbk_subcategory_models[OF category target])
  interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain ?N"
    "paper_bbk_denote ?N" "paper_bbk_valuation ?N"
    by (rule paper_R_bbk_data_model[OF target_valid])
  have hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
    (paper_bbk_domain ?N) (paper_bbk_denote ?N) (paper_arrow_map h)"
    using paper_R_bbk_data_morphism_raw[OF paper_R_bbk_arrows_morphism[OF selected]]
    by (simp only: origin)
  have kt: "named_env_typed (paper_bbk_domain ?N) G ?k"
    by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
  have ka: "named_adequate ?k P"
    by (rule paper_R_bbk_homomorphism_assignment_adequate[OF adequate])
  have al: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_or_language[OF language paper_R_named_not_language[OF language]])
  have aa: "named_adequate g ?A" using adequate
    by (simp add: named_adequate_def named_paper_primitive_fv)
  have image_value: "paper_arrow_map h Prop (paper_bbk_denote M g ?A) = paper_bbk_denote ?N ?k ?A"
    by (rule paper_R_bbk_homomorphism_denote[OF hom al typed aa])
  show ?thesis by (simp only: image_value; rule Target.paper_R_named_tautology_truth[OF language kt ka])
qed

theorem paper_R_tautology_profile:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and language: "paper_R_in_language \<Sigma> G P Prop"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g P"
  shows "paper_bbk_truth_profile_on Arrows M
      (paper_bbk_denote M g (named_paper_or P (named_paper_not P))) =
    paper_outgoing Arrows paper_arrow_source M"
proof (rule equalityI)
  show "paper_bbk_truth_profile_on Arrows M
      (paper_bbk_denote M g (named_paper_or P (named_paper_not P))) \<subseteq>
    paper_outgoing Arrows paper_arrow_source M"
    by (rule paper_bbk_truth_profile_on_outgoing)
next
  show "paper_outgoing Arrows paper_arrow_source M \<subseteq>
    paper_bbk_truth_profile_on Arrows M (paper_bbk_denote M g (named_paper_or P (named_paper_not P)))"
  proof
    fix h
    assume outgoing: "h \<in> paper_outgoing Arrows paper_arrow_source M"
    have arrow: "h \<in> Arrows" and origin: "paper_arrow_source h = M"
      using outgoing by (auto simp only: paper_outgoing_member)
    have truth: "paper_bbk_valuation (paper_arrow_target h)
      (paper_arrow_map h Prop (paper_bbk_denote M g (named_paper_or P (named_paper_not P))))"
      by (rule paper_R_outgoing_tautology_truth[OF category language typed adequate arrow origin])
    show "h \<in> paper_bbk_truth_profile_on Arrows M
      (paper_bbk_denote M g (named_paper_or P (named_paper_not P)))"
      by (simp only: paper_bbk_truth_profile_on_member; rule conjI[OF arrow conjI[OF origin truth]])
  qed
qed

text \<open>
  This uses denotation preservation to evaluate the tautology anew
  at the target; it does not transport source truth along an arrow.
  No quasi-Fregeanness is needed for this direction. Sources:
  Definitions 3.1 and 3.10, and the modal reading used in n.73.
\<close>

end
