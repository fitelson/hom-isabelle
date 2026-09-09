theory Bacon_Source_Relational_Classicism_Counterexample
  imports Bacon_Source_Relational_Bounded_Classicism_Category
    Bacon_Source_Relational_Bounded_Theory_Countermodel
begin

section \<open>A bounded C countermodel with its actual counterassignment\<close>

theorem paper_R_bounded_classicism_counterexample:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
    and missing: "\<not> paper_R_classicism_proves \<Sigma> G A"
  obtains Root g where "Root \<in> paper_R_bounded_classicism_models \<Sigma> G U"
    "named_env_typed (paper_bbk_domain Root) G g" "named_adequate g A"
    "\<not> paper_bbk_valuation Root (paper_bbk_denote Root g A)"
proof -
  have absent: "A \<notin> {P. paper_R_classicism_proves \<Sigma> G P}"
    using missing by simp
  obtain Root where object: "Root \<in> paper_R_bounded_classicism_models \<Sigma> G U"
    and fails: "\<not> paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain Root) (paper_bbk_denote Root) (paper_bbk_valuation Root) A"
    using paper_R_bounded_theory_countermodel[
      OF infinite names rich paper_R_classicism_is_H_theory language absent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain Root"
    "paper_bbk_denote Root" "paper_bbk_valuation Root"
    by (rule paper_R_bbk_data_model[OF paper_R_bounded_theory_models_valid[OF object]])
  have counterassignment: "\<exists>g. named_env_typed (paper_bbk_domain Root) G g \<and>
    named_adequate g A \<and> \<not> paper_bbk_valuation Root (paper_bbk_denote Root g A)"
    using fails language unfolding Model.paper_R_valid_def Model.paper_R_satisfies_def by blast
  then obtain g where typed: "named_env_typed (paper_bbk_domain Root) G g"
    and adequate: "named_adequate g A"
    and false_at: "\<not> paper_bbk_valuation Root (paper_bbk_denote Root g A)" by blast
  show thesis by (rule that[OF object typed adequate false_at])
qed

text \<open>
  Non-theoremhood yields an actual normalized bounded model of C
  and a typed adequate partial assignment at which A is false.
  The assignment is extracted from failure of global validity, not
  assumed total or replaced by the empty assignment when A is open.
  No separate consistency premise is needed. Source role: the root
  countermodel in the completeness construction of Theorem 3.23.
\<close>

end
