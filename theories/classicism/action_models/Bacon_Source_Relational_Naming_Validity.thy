theory Bacon_Source_Relational_Naming_Validity
  imports Bacon_Source_Relational_Naming_Model Bacon_Source_Relational_Constant_Map
begin

section \<open>The old-language embedding preserves exactly typing and adequacy\<close>

lemma paper_R_naming_old_type_iff:
  fixes A :: "'c paper_named_term"
  shows "paper_R_has_type G (map_named_term Inl id A :: ('c + 'v) paper_named_term) \<tau> \<longleftrightarrow> paper_R_has_type G A \<tau>"
proof
  assume typed: "paper_R_has_type G (map_named_term Inl id A :: ('c + 'v) paper_named_term) \<tau>"
  have replacement: "paper_R_has_type G (paper_R_naming_replace (\<lambda>_ :: otype \<times> 'v. 0) (map_named_term Inl id A)) \<tau>"
  proof (rule paper_R_naming_replace_type[where x="\<lambda>_ :: otype \<times> 'v. 0", OF typed])
    show "\<forall>k\<in>paper_R_naming_support (map_named_term Inl id A :: ('c + 'v) paper_named_term). G ((\<lambda>_. 0) k) = fst k"
      by (simp only: paper_R_naming_support_old_embedding ball_empty)
  qed
  show "paper_R_has_type G A \<tau>" using replacement by (simp only: paper_R_naming_replace_old)
next
  assume typed: "paper_R_has_type G A \<tau>"
  show "paper_R_has_type G (map_named_term Inl id A :: ('c + 'v) paper_named_term) \<tau>"
    by (rule paper_R_constant_map_type[OF typed])
qed

lemma paper_R_naming_old_language_iff:
  "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (map_named_term Inl id A) \<tau> \<longleftrightarrow>
    paper_R_in_language \<Sigma> G A \<tau>"
  by (simp only: paper_R_in_language_def paper_R_naming_old_type_iff paper_R_naming_old_signature)

lemma paper_R_naming_old_adequate_iff:
  "named_adequate g (map_named_term Inl id A) \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def paper_R_constant_map_fv)

section \<open>Validity of old formulas is preserved and reflected\<close>

text \<open>
  The actual naming model has exactly the original D, G and V. Every
  old formula has the same denotation under the same partial assignment,
  and its free variables and language membership are unchanged by Inl.
  Thus validity is equivalent, including for open formulas under all
  typed adequate assignments. Source: the naming extension M⁺ of
  p.51 n.73 and the validity convention following Definition 3.1.

  An image of an originally valid theory is consequently valid in M⁺.
  This is not an assertion that its image is closed under Propositional
  Equivalence, substitution, or any other enlarged-language proof rule.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_valid_iff:
  "paper_R_bbk_model.paper_R_valid (paper_R_naming_signature signature domain) stock domain
    paper_R_naming_denote valuation (map_named_term Inl id A) \<longleftrightarrow> paper_R_valid A"
proof -
  interpret Expanded: paper_R_bbk_model "paper_R_naming_signature signature domain" stock domain
    paper_R_naming_denote valuation by (rule paper_R_naming_model)
  show ?thesis
    unfolding Expanded.paper_R_valid_def paper_R_valid_def
      Expanded.paper_R_satisfies_def paper_R_satisfies_def
    by (simp only: paper_R_naming_old_language_iff paper_R_naming_old_adequate_iff paper_R_naming_denote_old)
qed

theorem paper_R_naming_valid_image_iff:
  "(\<forall>B\<in>map_named_term Inl id ` T.
      paper_R_bbk_model.paper_R_valid (paper_R_naming_signature signature domain) stock domain
        paper_R_naming_denote valuation B) \<longleftrightarrow> (\<forall>A\<in>T. paper_R_valid A)"
  by (simp only: ball_simps paper_R_naming_valid_iff)

corollary paper_R_naming_valid_image:
  assumes valid: "\<forall>A\<in>T. paper_R_valid A"
  shows "\<forall>B\<in>map_named_term Inl id ` T.
    paper_R_bbk_model.paper_R_valid (paper_R_naming_signature signature domain) stock domain
      paper_R_naming_denote valuation B"
  by (rule iffD2[OF paper_R_naming_valid_image_iff valid])

end

end
