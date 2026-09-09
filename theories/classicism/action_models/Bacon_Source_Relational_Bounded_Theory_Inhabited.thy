theory Bacon_Source_Relational_Bounded_Theory_Inhabited
  imports Bacon_Source_Relational_Bounded_Theory_Models
    Bacon_Source_Relational_H_Theory_Bounded_Model
begin

section \<open>A consistent H-theory has an object in its bounded model category\<close>

theorem paper_R_bounded_theory_models_nonempty:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and consistent: "paper_R_named_consistent \<Sigma> G T"
  shows "paper_R_bounded_theory_models \<Sigma> G U T \<noteq> {}"
proof -
  obtain D J V where model: "paper_R_bbk_model \<Sigma> G D J V"
    and bound: "(\<Union>\<sigma>. D \<sigma>) \<subseteq> U"
    and valid: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_H_theory_bounded_model_existence[OF infinite names rich theory_h consistent] by blast
  let ?M = "\<lparr>paper_bbk_domain=D, paper_bbk_denote=J, paper_bbk_valuation=V\<rparr>"
  have record_valid: "paper_R_bbk_data_valid \<Sigma> G ?M"
    using model by (simp add: paper_R_bbk_data_valid_def)
  have record_bound: "(\<Union>\<sigma>. paper_bbk_domain ?M \<sigma>) \<subseteq> U" using bound by simp
  have record_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
    (paper_bbk_domain ?M) (paper_bbk_denote ?M) (paper_bbk_valuation ?M) A" using valid by simp
  have member: "paper_R_bbk_normalize \<Sigma> G ?M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    by (rule paper_R_bounded_theory_models_normalize[OF record_valid record_bound record_truth])
  show ?thesis using member by blast
qed

text \<open>
  The target record is constructed by bounded H-theory model existence
  and normalized only afterward. This separate inhabitation result
  requires consistency; the structural category and quasi-Fregeanness
  theorems do not. Source: Theorem 3.2 and the p.52 bounded category.
\<close>

end
