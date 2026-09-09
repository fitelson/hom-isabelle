theory Bacon_Source_Relational_Bounded_Model_Existence
  imports Bacon_Source_Relational_Henkin_Cardinal_Signature
    Bacon_Source_Relational_Identity_Cardinal_Domains
    Bacon_Source_Relational_Countable_Model_Existence Bacon_Source_Relational_Recoding_Validity
begin

section \<open>Model existence on any sufficiently large infinite carrier\<close>

text \<open>
  Let U be infinite with |⋃σΣσ|≤|U|. Every closed H-consistent
  R sentence set S has an original-signature BBK model with ⋃σDσ⊆U.
  First construct the actual Henkin extension and its identity-class
  model. Bound its admitted names, syntax and actual class values by
  |U|, then recode using an injection on those values into U.

  Source role: the cardinal refinement for the fixed-carrier construction
  in p.51 n.73 and p.52, based on Theorem 3.2. The explicit signature
  bound is essential for arbitrary sentence sets. Neither the whole
  ambient class carrier nor the original name type is assumed countable
  or embeddable into U. No model or Henkin theory is supplied as a premise.
\<close>

theorem paper_R_BBK_bounded_model_existence:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and sentences: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> 'u set.
    \<exists>J :: 'u named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'u.
    \<exists>V :: 'u \<Rightarrow> bool. paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<Union>\<sigma>. D \<sigma>) \<subseteq> U \<and>
      (\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  let ?\<Omega> = "paper_R_henkin_full_signature \<Sigma> G"
  obtain M where extends: "image (paper_R_constant_map ROriginal) S \<subseteq> M"
    and Henkin: "paper_R_closed_Henkin_theory ?\<Omega> G M"
    using paper_R_closed_Henkin_extension_exists[OF rich sentences consistent] by blast
  let ?D = "paper_R_identity_domain ?\<Omega> G M"
  let ?J = "paper_R_constant_pullback_denote ROriginal (paper_R_identity_denote ?\<Omega> G M)"
  let ?V = "paper_R_identity_valuation M"
  have realization: "paper_R_bbk_model \<Sigma> G ?D ?J ?V \<and>
      (\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G ?D ?J ?V A)"
    by (rule paper_R_Henkin_original_model_realizes[OF rich sentences Henkin extends])
  interpret Model: paper_R_bbk_model \<Sigma> G ?D ?J ?V by (rule conjunct1[OF realization])
  have full_names: "card_of (\<Union>\<sigma>. ?\<Omega> \<sigma>) \<le>o card_of U"
    by (rule paper_R_henkin_full_names_cardinal_bound[OF infinite names])
  have bound: "card_of (\<Union>\<sigma>. ?D \<sigma>) \<le>o card_of U"
    by (rule paper_R_identity_domains_cardinal_bound[OF infinite full_names])
  obtain f :: "('c paper_R_henkin_name) paper_named_term set \<Rightarrow> 'u"
    where injective: "inj_on f (\<Union>\<sigma>. ?D \<sigma>)" and image: "f ` (\<Union>\<sigma>. ?D \<sigma>) \<subseteq> U"
    using bound unfolding card_of_ordLeq[symmetric] by blast
  have coded: "paper_R_bbk_model \<Sigma> G (paper_R_recode_domain f ?D)
      (Model.paper_R_recode_denote f) (Model.paper_R_recode_valuation f)"
    by (rule Model.paper_R_recode_model[OF injective])
  have subset: "(\<Union>\<sigma>. paper_R_recode_domain f ?D \<sigma>) \<subseteq> U"
    by (simp only: paper_R_recode_domain_union; rule image)
  have valid: "\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_R_recode_domain f ?D) (Model.paper_R_recode_denote f) (Model.paper_R_recode_valuation f) A"
  proof (intro ballI)
    fix A
    assume member: "A \<in> S"
    have original: "Model.paper_R_valid A" by (rule bspec[OF conjunct2[OF realization] member])
    show "paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_R_recode_domain f ?D)
        (Model.paper_R_recode_denote f) (Model.paper_R_recode_valuation f) A"
      by (rule iffD2[OF Model.paper_R_recode_valid_iff[OF injective] original])
  qed
  show ?thesis by (rule exI[where x="paper_R_recode_domain f ?D"],
    rule exI[where x="Model.paper_R_recode_denote f"], rule exI[where x="Model.paper_R_recode_valuation f"],
    rule conjI[OF coded conjI[OF subset valid]])
qed

end
