theory Bacon_Source_Relational_Model_Existence
  imports Bacon_Source_Relational_Closed_Henkin_Extension Bacon_Source_Relational_Identity_Model
    Bacon_Source_Relational_BBK_Constant_Pullback
begin

section \<open>Every native H-consistent R sentence set has an original-signature BBK model\<close>

text \<open>
  From closed, syntactically Hᴿ-consistent S⊆ℒᴿ(Σ), construct the
  full witness signature Σ∞ and a closed Henkin theory M containing
  Original[S]. Its theorem-identity classes give an actual independent
  R-BBK model. Pull the interpretation back along Original, retaining
  the domains, valuation and variable stock. Each original sentence is
  true under every typed adequate partial assignment.

  This is the sentence-set model-existence direction of Theorem 3.2,
  pp.44–45, with the explicit construction of footnote 64. Neither a
  Henkin theory nor a model is a premise. The witness carrier is the
  HOL type of sets of named terms over the expanded constant-name
  datatype; no countability of the original names, signature or S is
  assumed. A countable-carrier refinement and any stronger open-premise
  or Classicism completeness claim are separate obligations.
\<close>

theorem paper_R_BBK_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes rich: "paper_R_rich G" and sentences: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
    \<exists>J :: (('c paper_R_henkin_name) paper_named_term set) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set.
    \<exists>V :: (('c paper_R_henkin_name) paper_named_term set) \<Rightarrow> bool.
      paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<forall>A\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  let ?\<Omega> = "paper_R_henkin_full_signature \<Sigma> G"
  obtain M where extends: "image (paper_R_constant_map ROriginal) S \<subseteq> M"
    and Henkin: "paper_R_closed_Henkin_theory ?\<Omega> G M"
    using paper_R_closed_Henkin_extension_exists[OF rich sentences consistent] by blast
  let ?D = "paper_R_identity_domain ?\<Omega> G M"
  let ?K = "paper_R_identity_denote ?\<Omega> G M"
  let ?V = "paper_R_identity_valuation M"
  let ?J = "paper_R_constant_pullback_denote ROriginal ?K"
  have canonical: "paper_R_bbk_model ?\<Omega> G ?D ?K ?V"
    by (rule paper_R_identity_bbk_model[OF rich Henkin])
  have maps: "ROriginal c \<in> ?\<Omega> \<rho>" if "c \<in> \<Sigma> \<rho>" for \<rho> c
    by (simp only: paper_R_henkin_full_original_iff; rule that)
  have original_model: "paper_R_bbk_model \<Sigma> G ?D ?J ?V"
    by (rule paper_R_bbk_constant_pullback[OF canonical maps])
  interpret Model: paper_R_bbk_model \<Sigma> G ?D ?J ?V by (rule original_model)
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
      have class_truth: "?V (paper_R_identity_class ?\<Omega> G M Prop ?B)"
        by (rule iffD2[OF paper_R_identity_valuation_class[OF rich Henkin closed_term] in_M])
      show ?thesis by (simp only: denotation; rule class_truth)
    qed
    show ?thesis unfolding Model.paper_R_valid_def Model.paper_R_satisfies_def
      by (rule conjI[OF al], intro allI impI; rule truth)
  qed
  have all_sentences: "\<forall>A\<in>S. Model.paper_R_valid A" by (intro ballI; rule valid; assumption)
  show ?thesis by (rule exI[where x="?D"], rule exI[where x="?J"], rule exI[where x="?V"],
    rule conjI[OF original_model all_sentences])
qed

end
