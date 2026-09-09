theory Bacon_Source_Relational_Countable_Model_Existence
  imports Bacon_Source_Relational_Model_Existence Bacon_Source_Relational_Identity_Countable_Domains
    Bacon_Source_Relational_Henkin_Countable_Signature
begin

section \<open>The explicit original-signature model associated with a Henkin extension\<close>

lemma paper_R_Henkin_original_model_realizes:
  assumes rich: "paper_R_rich G" and sentences: "paper_R_closed_theory \<Sigma> G S"
    and Henkin: "paper_R_closed_Henkin_theory (paper_R_henkin_full_signature \<Sigma> G) G M"
    and extends: "image (paper_R_constant_map ROriginal) S \<subseteq> M"
  shows "paper_R_bbk_model \<Sigma> G (paper_R_identity_domain (paper_R_henkin_full_signature \<Sigma> G) G M)
      (paper_R_constant_pullback_denote ROriginal (paper_R_identity_denote (paper_R_henkin_full_signature \<Sigma> G) G M))
      (paper_R_identity_valuation M) \<and>
    (\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_R_identity_domain (paper_R_henkin_full_signature \<Sigma> G) G M)
      (paper_R_constant_pullback_denote ROriginal (paper_R_identity_denote (paper_R_henkin_full_signature \<Sigma> G) G M))
      (paper_R_identity_valuation M) A)"
proof -
  let ?\<Omega> = "paper_R_henkin_full_signature \<Sigma> G"
  let ?D = "paper_R_identity_domain ?\<Omega> G M"
  let ?K = "paper_R_identity_denote ?\<Omega> G M"
  let ?J = "paper_R_constant_pullback_denote ROriginal ?K"
  let ?V = "paper_R_identity_valuation M"
  have canonical: "paper_R_bbk_model ?\<Omega> G ?D ?K ?V" by (rule paper_R_identity_bbk_model[OF rich Henkin])
  have maps: "ROriginal c \<in> ?\<Omega> \<rho>" if "c \<in> \<Sigma> \<rho>" for \<rho> c
    by (simp only: paper_R_henkin_full_original_iff; rule that)
  have model: "paper_R_bbk_model \<Sigma> G ?D ?J ?V" by (rule paper_R_bbk_constant_pullback[OF canonical maps])
  interpret Model: paper_R_bbk_model \<Sigma> G ?D ?J ?V by (rule model)
  have valid: "Model.paper_R_valid A" if member: "A \<in> S" for A
  proof -
    let ?B = "paper_R_constant_map ROriginal A"
    have sentence: "paper_R_sentence \<Sigma> G A" by (rule paper_R_closed_theory_member[OF sentences member])
    have al: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_sentence_language[OF sentence])
    have ac: "named_fv A = {}" by (rule paper_R_sentence_closed[OF sentence])
    have bl: "paper_R_in_language ?\<Omega> G ?B Prop" by (rule paper_R_constant_map_language[OF al maps])
    have bc: "named_fv ?B = {}" by (simp only: paper_R_constant_map_fv ac)
    have closed_term: "?B \<in> paper_R_closed_terms ?\<Omega> G Prop" by (rule paper_R_closed_termsI[OF bl bc])
    have in_M: "?B \<in> M" by (rule subsetD[OF extends imageI[OF member]])
    have truth: "?V (?J g A)" for g
    proof -
      have denotation: "?J g A = paper_R_identity_class ?\<Omega> G M Prop ?B"
        by (simp only: paper_R_constant_pullback_denote_def paper_R_identity_denote_closed[OF bl bc])
      show ?thesis by (simp only: denotation; rule iffD2[OF paper_R_identity_valuation_class[OF rich Henkin closed_term] in_M])
    qed
    show ?thesis unfolding Model.paper_R_valid_def Model.paper_R_satisfies_def
      by (rule conjI[OF al], intro allI impI; rule truth)
  qed
  show ?thesis by (rule conjI[OF model], intro ballI; rule valid; assumption)
qed

section \<open>Countable declared signatures give a model with countable domain union\<close>

text \<open>
  Count the admitted expanded signature, construct the actual Henkin
  theory, and use its explicit canonical class domains. The pullback to
  Σ does not change those domains. Source: the countable refinement in
  Theorem 3.2, pp.44–45. The ambient constant-name carrier remains
  unrestricted, and no Henkin theory or model is supplied as a premise.

  This theorem counts the union of the model's actual domain values.
  It does not count the surrounding powerset-valued HOL carrier and
  does not itself recode the domains as literal subsets of ℕ; the
  subsequent Nat_Model_Existence theory supplies that carrier change.
\<close>

theorem paper_R_BBK_countable_union_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes names: "countable (\<Union>\<rho>. \<Sigma> \<rho>)" and rich: "paper_R_rich G"
    and sentences: "paper_R_closed_theory \<Sigma> G S" and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
    \<exists>J :: (('c paper_R_henkin_name) paper_named_term set) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set.
    \<exists>V :: (('c paper_R_henkin_name) paper_named_term set) \<Rightarrow> bool.
      paper_R_bbk_model \<Sigma> G D J V \<and> countable (\<Union>\<rho>. D \<rho>) \<and>
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
  have full_names: "countable (\<Union>\<rho>. ?\<Omega> \<rho>)" by (rule paper_R_henkin_full_names_countable[OF names])
  have domains: "countable (\<Union>\<rho>. ?D \<rho>)" by (rule paper_R_identity_domains_countable[OF full_names])
  show ?thesis by (rule exI[where x="?D"], rule exI[where x="?J"], rule exI[where x="?V"],
    rule conjI[OF conjunct1[OF realization] conjI[OF domains conjunct2[OF realization]]])
qed

end
