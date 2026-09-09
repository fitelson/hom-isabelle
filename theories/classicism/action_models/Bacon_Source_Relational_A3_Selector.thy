theory Bacon_Source_Relational_A3_Selector
  imports Bacon_Source_Relational_Classicism_A2_H Bacon_Source_Relational_Conversion_Congruence
begin

definition paper_R_A3_selector where
  "paper_R_A3_selector B X =
    named_paper_or (named_paper_and B X) (named_paper_and (named_paper_not B) (named_paper_not X))"

definition paper_R_A3_vector_context where
  "paper_R_A3_vector_context ns B K =
    named_lam_vec ns (paper_R_A3_selector B (named_app_vec K (map NVar ns)))"

lemma paper_R_A3_selector_language:
  assumes bl: "paper_R_in_language \<Sigma> G B Prop" and xl: "paper_R_in_language \<Sigma> G X Prop"
  shows "paper_R_in_language \<Sigma> G (paper_R_A3_selector B X) Prop"
  unfolding paper_R_A3_selector_def
  by (rule paper_R_named_or_language[OF paper_R_named_and_language[OF bl xl]
    paper_R_named_and_language[OF paper_R_named_not_language[OF bl] paper_R_named_not_language[OF xl]]])

lemma paper_R_A3_vector_language:
  assumes bl: "paper_R_in_language \<Sigma> G B Prop"
    and kl: "paper_R_in_language \<Sigma> G K (paper_type_vector (map G ns) Prop)"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_in_language \<Sigma> G (paper_R_A3_vector_context ns B K) (paper_type_vector (map G ns) Prop)"
proof -
  have application: "paper_R_in_language \<Sigma> G (named_app_vec K (map NVar ns)) Prop"
    by (rule paper_R_named_app_vec_language[OF paper_R_named_vector_variables_language[OF binders] kl])
  show ?thesis unfolding paper_R_A3_vector_context_def
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_A3_selector_language[OF bl application] binders])
qed

section \<open>Actual R conversion in both occurrences of the selector input\<close>

lemma paper_R_raw_A3_selector:
  fixes B :: "'c paper_named_term"
  assumes bt: "paper_R_has_type G B Prop" and conversion: "paper_R_raw_beta_eta G Prop X Y"
  shows "paper_R_raw_beta_eta G Prop (paper_R_A3_selector B X) (paper_R_A3_selector B Y)"
proof -
  have and_type: "paper_R_has_type G (NLogical SAnd :: 'c paper_named_term) (Arr Prop (Arr Prop Prop))"
    using paper_R_has_type.Logical[where G=G and l=SAnd] by simp
  have or_type: "paper_R_has_type G (NLogical SOr :: 'c paper_named_term) (Arr Prop (Arr Prop Prop))"
    using paper_R_has_type.Logical[where G=G and l=SOr] by simp
  have not_type: "paper_R_has_type G (NLogical SNot :: 'c paper_named_term) (Arr Prop Prop)"
    using paper_R_has_type.Logical[where G=G and l=SNot] by simp
  have positive_head: "paper_R_has_type G (NApp (NLogical SAnd) B) (Arr Prop Prop)"
    by (rule paper_R_has_type.App[OF and_type bt])
  have positive: "paper_R_raw_beta_eta G Prop
    (NApp (NApp (NLogical SAnd) B) X) (NApp (NApp (NLogical SAnd) B) Y)"
    by (rule paper_R_raw_beta_eta_App_right[OF conversion positive_head])
  have negation: "paper_R_raw_beta_eta G Prop (NApp (NLogical SNot) X) (NApp (NLogical SNot) Y)"
    by (rule paper_R_raw_beta_eta_App_right[OF conversion not_type])
  have negative_head: "paper_R_has_type G
    (NApp (NLogical SAnd) (NApp (NLogical SNot) B)) (Arr Prop Prop)"
    by (rule paper_R_has_type.App[OF and_type paper_R_has_type.App[OF not_type bt]])
  have negative: "paper_R_raw_beta_eta G Prop
    (NApp (NApp (NLogical SAnd) (NApp (NLogical SNot) B)) (NApp (NLogical SNot) X))
    (NApp (NApp (NLogical SAnd) (NApp (NLogical SNot) B)) (NApp (NLogical SNot) Y))"
    by (rule paper_R_raw_beta_eta_App_right[OF negation negative_head])
  have disjunction_head: "paper_R_raw_beta_eta G (Arr Prop Prop)
    (NApp (NLogical SOr) (NApp (NApp (NLogical SAnd) B) X))
    (NApp (NLogical SOr) (NApp (NApp (NLogical SAnd) B) Y))"
    by (rule paper_R_raw_beta_eta_App_right[OF positive or_type])
  show ?thesis unfolding paper_R_A3_selector_def named_paper_or_def named_paper_and_def named_paper_not_def
    by (rule paper_R_raw_beta_eta_App[OF disjunction_head negative])
qed

theorem paper_R_named_H_A3_self_identity:
  assumes rich: "paper_R_rich G" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and al: "paper_R_in_language \<Sigma> G A Prop" and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (paper_R_A3_vector_context ns B (named_lam_vec ns A)) (named_lam_vec ns (paper_R_A3_selector B A)))"
proof -
  have bt: "paper_R_has_type G B Prop" using bl unfolding paper_R_in_language_def by (rule conjunct1)
  have self: "paper_R_raw_beta_eta G Prop (named_app_vec (named_lam_vec ns A) (map NVar ns)) A"
    by (rule paper_R_named_lam_vec_self_beta[OF al binders]; simp)
  have body: "paper_R_raw_beta_eta G Prop
    (paper_R_A3_selector B (named_app_vec (named_lam_vec ns A) (map NVar ns))) (paper_R_A3_selector B A)"
    by (rule paper_R_raw_A3_selector[OF bt self])
  have conversion: "paper_R_raw_beta_eta G (paper_type_vector (map G ns) Prop)
    (paper_R_A3_vector_context ns B (named_lam_vec ns A)) (named_lam_vec ns (paper_R_A3_selector B A))"
    unfolding paper_R_A3_vector_context_def by (rule paper_R_raw_beta_eta_lam_vec[OF body binders]; simp)
  have left: "paper_R_in_language \<Sigma> G (paper_R_A3_vector_context ns B (named_lam_vec ns A))
    (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_A3_vector_language[OF bl paper_R_named_lam_vec_prop_language[OF al binders] binders])
  have right: "paper_R_in_language \<Sigma> G (named_lam_vec ns (paper_R_A3_selector B A))
    (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_A3_selector_language[OF bl al] binders])
  show ?thesis by (rule paper_R_named_H_raw_conversion_identity[OF rich conversion left right])
qed

text \<open>
  The selector is the literal p.67 expression (B∧X)∨(¬B∧¬X).
  The two X occurrences are converted separately through typed App
  contexts, then under the displayed R prefix. No identity abstraction,
  Equivalence rule, or semantic Boolean operation is assumed.
\<close>

end
