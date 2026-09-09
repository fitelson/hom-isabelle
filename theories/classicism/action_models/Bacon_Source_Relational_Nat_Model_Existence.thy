theory Bacon_Source_Relational_Nat_Model_Existence
  imports Bacon_Source_Relational_Countable_Model_Existence Bacon_Source_Relational_Recoding_Validity
begin

section \<open>Countable signatures have R-BBK models with domains in ℕ\<close>

text \<open>
  Countable ⋃σΣσ and closed H-consistency of S give an actual
  model with countable U=⋃σDσ. Choose f:U↪ℕ and apply the
  carrier-recoding theorem to all its structural and truth clauses.
  The result has literal domains D′σ⊆ℕ and validates every sentence
  of S in the original signature.

  Source: the moreover clause of Bacon–Dorr Theorem 3.2, pp.44–45.
  We count admitted names only, not their ambient HOL type. The
  injection is required only on U, not on the surrounding powerset
  carrier. No model, witness theory or consistency bridge is assumed.
\<close>

theorem paper_R_BBK_nat_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes names: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)" and rich: "paper_R_rich G"
    and sentences: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> nat set.
    \<exists>J :: nat named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  obtain D :: "otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set"
    and J and V where model: "paper_R_bbk_model \<Sigma> G D J V"
    and countable: "countable (\<Union>\<sigma>. D \<sigma>)"
    and valid: "\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_BBK_countable_union_model_existence[OF names rich sentences consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  obtain f :: "('c paper_R_henkin_name) paper_named_term set \<Rightarrow> nat"
    where injective: "inj_on f (\<Union>\<sigma>. D \<sigma>)" by (rule countableE[OF countable])
  have coded: "paper_R_bbk_model \<Sigma> G (paper_R_recode_domain f D)
      (Model.paper_R_recode_denote f) (Model.paper_R_recode_valuation f)"
    by (rule Model.paper_R_recode_model[OF injective])
  have coded_valid: "\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_R_recode_domain f D) (Model.paper_R_recode_denote f) (Model.paper_R_recode_valuation f) A"
  proof (intro ballI)
    fix A
    assume member: "A \<in> S"
    have original: "Model.paper_R_valid A" by (rule bspec[OF valid member])
    show "paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_R_recode_domain f D)
        (Model.paper_R_recode_denote f) (Model.paper_R_recode_valuation f) A"
      by (rule iffD2[OF Model.paper_R_recode_valid_iff[OF injective] original])
  qed
  show ?thesis by (rule exI[where x="paper_R_recode_domain f D"],
    rule exI[where x="Model.paper_R_recode_denote f"],
    rule exI[where x="Model.paper_R_recode_valuation f"], rule conjI[OF coded coded_valid])
qed

end
