theory Bacon_Source_Relational_Common_H
  imports Bacon_Source_Relational_Common_Theory Bacon_Source_Relational_H_Soundness
begin

section \<open>The common theory contains H and is closed under MP\<close>

text \<open>
  Every Hᴿ theorem belongs to the common theory of a collection
  of R BBK models. That common theory is closed under modus ponens.
  Source: Theorem 3.2 and the soundness argument of Theorem 3.12,
  pp.44–45 and p.51.

  Both results quantify over independently validated R models.
  No arrows or separation condition is needed here; those conditions
  enter the separate Propositional Equivalence and Functionality
  closure results. Neither fact identifies a proof presentation
  with Classicism without the remaining presentation theorem.
\<close>

theorem paper_R_common_contains_H:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
    and derivation: "paper_R_named_H \<Sigma> G A"
  shows "A \<in> paper_R_common_theory \<Sigma> G Obj"
proof (rule paper_R_common_theoryI[OF paper_R_named_H_language[OF derivation]])
  fix M g
  assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF models[OF object]])
  show "paper_bbk_valuation M (paper_bbk_denote M g A)"
    by (rule Model.paper_R_validE[OF Model.paper_R_named_H_soundness[OF derivation] typed adequate])
qed

theorem paper_R_common_MP:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
    and first: "A \<in> paper_R_common_theory \<Sigma> G Obj"
    and second: "named_paper_imp G A B \<in> paper_R_common_theory \<Sigma> G Obj"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "B \<in> paper_R_common_theory \<Sigma> G Obj"
proof (rule paper_R_common_theoryI[OF bl])
  fix M g
  assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g B"
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF models[OF object]])
  have local_valid: "Model.paper_R_valid P" if common: "P \<in> paper_R_common_theory \<Sigma> G Obj" for P
  proof (rule Model.paper_R_validI[OF paper_R_common_theory_language[OF common]])
    fix k
    assume kt: "named_env_typed (paper_bbk_domain M) G k" and pa: "named_adequate k P"
    show "paper_bbk_valuation M (paper_bbk_denote M k P)"
      by (rule paper_R_common_theory_truth[OF common object kt pa])
  qed
  have bv: "Model.paper_R_valid B"
    by (rule Model.paper_R_valid_MP[
      OF paper_R_common_theory_language[OF first] bl local_valid[OF first] local_valid[OF second]])
  show "paper_bbk_valuation M (paper_bbk_denote M g B)"
    by (rule Model.paper_R_validE[OF bv typed adequate])
qed

end
