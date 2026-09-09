theory Bacon_Source_Subcategory
  imports Bacon_Source_Category
begin

section \<open>A composition-closed selection of arrows forms a category\<close>

text \<open>
  Keep a category's objects and select arrows B⊆Arr containing every
  identity and closed under composition. The resulting objects, arrows
  and inherited operations form a category.
  Source: Bacon–Dorr §3.3, p.49, following the homomorphism definition.

  This is the structural step for restricting typed maps to the maps
  that preserve BBK interpretations. The latter closure conditions must
  be proved separately; they are explicit hypotheses here. No model,
  denotation, valuation, injectivity or intensionality is assumed.
\<close>

context paper_category
begin

theorem paper_category_restrict_arrows:
  assumes inclusion: "B \<subseteq> arrows"
    and identities: "\<And>A. A \<in> objects \<Longrightarrow> identity A \<in> B"
    and composition: "\<And>f g. f \<in> B \<Longrightarrow> g \<in> B \<Longrightarrow> target f = source g \<Longrightarrow>
      compose g f \<in> B"
  shows "paper_category objects B source target compose identity"
proof -
  have lift: "f \<in> arrows" if "f \<in> B" for f by (rule subsetD[OF inclusion that])
  have sources: "source f \<in> objects" if "f \<in> B" for f
    by (rule source_object[OF lift[OF that]])
  have targets: "target f \<in> objects" if "f \<in> B" for f
    by (rule target_object[OF lift[OF that]])
  have compose_sources: "source (compose g f) = source f"
    if "f \<in> B" "g \<in> B" "target f = source g" for f g
    by (rule compose_source[OF lift[OF that(1)] lift[OF that(2)] that(3)])
  have compose_targets: "target (compose g f) = target g"
    if "f \<in> B" "g \<in> B" "target f = source g" for f g
    by (rule compose_target[OF lift[OF that(1)] lift[OF that(2)] that(3)])
  have associative: "compose h (compose g f) = compose (compose h g) f"
    if "f \<in> B" "g \<in> B" "h \<in> B" "target f = source g" "target g = source h" for f g h
    by (rule compose_assoc[OF lift[OF that(1)] lift[OF that(2)] lift[OF that(3)] that(4,5)])
  have left_identity: "compose (identity (target f)) f = f" if "f \<in> B" for f
    by (rule identity_left[OF lift[OF that]])
  have right_identity: "compose f (identity (source f)) = f" if "f \<in> B" for f
    by (rule identity_right[OF lift[OF that]])
  show ?thesis
    by unfold_locales
      (auto intro: sources targets identities identity_source identity_target
        composition compose_sources compose_targets associative left_identity right_identity)
qed

end

end
