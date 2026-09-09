theory Bacon_Source_ZF_Action_H_Soundness
  imports Bacon_Source_ZF_Action_BBK_Model
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_H_Soundness
begin

section \<open>Native R-H truth in every supplied action model\<close>

text \<open>
  At each root arrow h, Proposition 3.21 constructs the independent
  R-BBK model Mₕ from the actual action interpreter. Native R-H
  soundness applies to that constructed model, and the direct truth
  comparison returns A,h,g ⊩ P. Source: the transition from C.6
  to C.7, p.71, using Theorem 3.2, pp.44–45.

  The only model premise below is the generic action model. The
  R-BBK certificate is a theorem, not an additional hypothesis. No
  F soundness theorem or C derivability relation is used.
\<close>

theorem paper_ZF_action_model_H_truth:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and derivation: "paper_R_named_H \<Sigma> G A"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g A"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g A"
proof -
  let ?D = "paper_ZF_action_bbk_domain D (target h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  have named_typed: "named_env_typed ?D G g"
    using typed by (simp only: paper_ZF_action_bbk_env_iff)
  have language: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_named_H_language[OF derivation])
  have valid: "M.paper_R_valid A" by (rule M.paper_R_named_H_soundness[OF derivation])
  have truth: "?V (?J g A)" by (rule M.paper_R_validE[OF valid named_typed adequate])
  show ?thesis by (rule iffD2[OF paper_ZF_action_bbk_holds_iff[
    OF model language arrow origin named_typed adequate] truth])
qed

section \<open>A proved literal biconditional gives uniform truth agreement\<close>

text \<open>
  The ↔ below is the source's closed λ-defined operator, applied to
  P and Q. Its R-BBK truth law is derived, not stipulated. Its free
  variables are exactly FV(P)∪FV(Q), so endpoint adequacy is sufficient.
  This provides the uniform-truth premise needed by the semantic
  proposition-separation and vector-abstraction ingredients of C.7.
\<close>

theorem paper_ZF_action_model_H_iff_truth:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and derivation: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g P" and adequate_right: "named_adequate g Q"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g P =
    paper_ZF_action_holds Ar source target compose identity D T I G h g Q"
proof -
  let ?D = "paper_ZF_action_bbk_domain D (target h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  have named_typed: "named_env_typed ?D G g"
    using typed by (simp only: paper_ZF_action_bbk_env_iff)
  have language: "paper_R_in_language \<Sigma> G (named_paper_iff G P Q) Prop"
    by (rule paper_R_named_H_language[OF derivation])
  have adequate: "named_adequate g (named_paper_iff G P Q)"
    using adequate_left adequate_right by (auto simp: named_adequate_def named_paper_defined_fv)
  have holds: "paper_ZF_action_holds Ar source target compose identity D T I G h g (named_paper_iff G P Q)"
    by (rule paper_ZF_action_model_H_truth[OF model derivation arrow origin typed adequate])
  have truth: "?V (?J g (named_paper_iff G P Q))"
    by (rule iffD1[OF paper_ZF_action_bbk_holds_iff[
      OF model language arrow origin named_typed adequate] holds])
  have material: "?V (?J g (named_paper_iff G P Q)) = (?V (?J g P) = ?V (?J g Q))"
    by (rule M.paper_R_named_paper_iff_truth[OF left right named_typed adequate_left adequate_right])
  have equal: "?V (?J g P) = ?V (?J g Q)" using truth material by blast
  show ?thesis by (simp only:
    paper_ZF_action_bbk_holds_iff[OF model left arrow origin named_typed adequate_left]
    paper_ZF_action_bbk_holds_iff[OF model right arrow origin named_typed adequate_right] equal)
qed

end
