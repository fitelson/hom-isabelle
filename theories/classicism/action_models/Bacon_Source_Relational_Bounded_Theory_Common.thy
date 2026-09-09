theory Bacon_Source_Relational_Bounded_Theory_Common
  imports Bacon_Source_Relational_Bounded_Theory_Countermodel
    Bacon_Source_Relational_Common_Theory
begin

section \<open>The common theory of all bounded T-models is exactly T\<close>

theorem paper_R_bounded_models_common_theory:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
  shows "paper_R_common_theory \<Sigma> G (paper_R_bounded_theory_models \<Sigma> G U T) = T"
proof (rule set_eqI)
  fix P
  show "(P \<in> paper_R_common_theory \<Sigma> G (paper_R_bounded_theory_models \<Sigma> G U T)) = (P \<in> T)"
  proof
    assume common: "P \<in> paper_R_common_theory \<Sigma> G (paper_R_bounded_theory_models \<Sigma> G U T)"
    have language: "paper_R_in_language \<Sigma> G P Prop"
      by (rule paper_R_common_theory_language[OF common])
    show "P \<in> T"
    proof (rule ccontr)
      assume absent: "P \<notin> T"
      obtain M where object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
        and fails: "\<not> paper_R_bbk_model.paper_R_valid \<Sigma> G
          (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) P"
        using paper_R_bounded_theory_countermodel[OF infinite names rich theory_h language absent] by blast
      interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
        "paper_bbk_denote M" "paper_bbk_valuation M"
        by (rule paper_R_bbk_data_model[OF paper_R_bounded_theory_models_valid[OF object]])
      have valid: "Model.paper_R_valid P"
      proof (rule Model.paper_R_validI[OF language])
        fix g
        assume typed: "named_env_typed (paper_bbk_domain M) G g" and adequate: "named_adequate g P"
        show "paper_bbk_valuation M (paper_bbk_denote M g P)"
          by (rule paper_R_common_theory_truth[OF common object typed adequate])
      qed
      show False using fails valid by contradiction
    qed
  next
    assume member: "P \<in> T"
    have language: "paper_R_in_language \<Sigma> G P Prop"
      by (rule paper_R_H_theory_language[OF theory_h member])
    show "P \<in> paper_R_common_theory \<Sigma> G (paper_R_bounded_theory_models \<Sigma> G U T)"
    proof (rule paper_R_common_theoryI[OF language])
      fix M g
      assume object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
        and typed: "named_env_typed (paper_bbk_domain M) G g" and adequate: "named_adequate g P"
      interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
        "paper_bbk_denote M" "paper_bbk_valuation M"
        by (rule paper_R_bbk_data_model[OF paper_R_bounded_theory_models_valid[OF object]])
      have valid: "Model.paper_R_valid P" by (rule paper_R_bounded_theory_models_truth[OF object member])
      show "paper_bbk_valuation M (paper_bbk_denote M g P)"
        by (rule Model.paper_R_validE[OF valid typed adequate])
    qed
  qed
qed

text \<open>
  This includes open formulas under every typed adequate assignment.
  The original H-theory closure, not arbitrary local consistency of
  open premises, justifies the closed-sentence countermodel reduction.
  No PE or C assumption is used here. If T is inconsistent, the
  object set can be empty and both sides contain every R formula.
  Source role: the common-theory characterization in Theorem 3.12.
\<close>

end
