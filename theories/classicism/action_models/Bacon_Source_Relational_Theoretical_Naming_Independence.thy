theory Bacon_Source_Relational_Theoretical_Naming_Independence
  imports Bacon_Source_Relational_Theoretical_Naming_Coordinate
    Bacon_Source_Relational_Naming_Chart_Mixing
begin

section \<open>Fresh chart choice does not affect H-theory membership\<close>

text \<open>
  First interpolate between charts whose finite images are disjoint,
  using one-coordinate substitution at each step. For arbitrary charts,
  choose a third chart avoiding both images and all original variable
  names. This compares replacements by membership in the ORIGINAL
  H-theory T, not by denotation in a supplied model.

  Source role: the finite fresh-parameter extension needed in p.51
  n.73. Only the finite typed support of the individual formula is
  charted. There is no global injection of new names into the stock,
  no freshness requirement against T, and no PE or C premise.
\<close>

lemma paper_R_theoretical_naming_disjoint:
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and first: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) y"
    and disjoint: "image x (paper_R_naming_support A) \<inter> image y (paper_R_naming_support A) = {}"
  shows "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow> (paper_R_naming_replace y A \<in> T)"
proof -
  let ?K = "paper_R_naming_support A"
  have finite_changes: "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow>
      (paper_R_naming_replace (paper_R_naming_mix L x y) A \<in> T)"
    if finite: "finite L" and support: "L \<subseteq> ?K" for L
    using finite support
  proof (induction rule: finite_induct)
    case empty
    show ?case by simp
  next
    case (insert k L)
    have key: "k \<in> ?K" and smaller: "L \<subseteq> ?K" using insert.prems by auto
    have previous: "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow>
        (paper_R_naming_replace (paper_R_naming_mix L x y) A \<in> T)"
      by (rule insert.IH[OF smaller])
    have before: "paper_R_naming_chart G ?K (named_vars A) (paper_R_naming_mix L x y)"
      by (rule paper_R_naming_mix_chart[OF first second disjoint])
    have after: "paper_R_naming_chart G ?K (named_vars A) (paper_R_naming_mix (insert k L) x y)"
      by (rule paper_R_naming_mix_chart[OF first second disjoint])
    have agree: "paper_R_naming_mix (insert k L) x y j = paper_R_naming_mix L x y j"
      if member: "j \<in> ?K" and different: "j \<noteq> k" for j
      using different by (simp add: paper_R_naming_mix_def)
    have coordinate: "(paper_R_naming_replace (paper_R_naming_mix L x y) A \<in> T) \<longleftrightarrow>
        (paper_R_naming_replace (paper_R_naming_mix (insert k L) x y) A \<in> T)"
      by (rule paper_R_theoretical_naming_coordinate_iff[
        OF rich theory_h language before after key agree])
    show ?case using previous coordinate by blast
  qed
  have complete: "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow>
      (paper_R_naming_replace (paper_R_naming_mix ?K x y) A \<in> T)"
    by (rule finite_changes[OF paper_R_naming_support_finite subset_refl])
  have agree: "paper_R_naming_mix ?K x y k = y k" if "k \<in> ?K" for k
    using that by (simp add: paper_R_naming_mix_def)
  have replacement: "paper_R_naming_replace (paper_R_naming_mix ?K x y) A = paper_R_naming_replace y A"
    by (rule paper_R_naming_replace_chart_agreement[OF agree])
  show ?thesis using complete by (simp only: replacement)
qed

theorem paper_R_theoretical_naming_independent:
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and first: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) y"
  shows "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow> (paper_R_naming_replace y A \<in> T)"
proof -
  let ?K = "paper_R_naming_support A"
  let ?N = "named_vars A \<union> image x ?K \<union> image y ?K"
  have finite: "finite ?N" by (simp add: named_vars_finite paper_R_naming_support_finite)
  have original_type: "paper_R_has_type G A Prop"
    using language unfolding paper_R_in_language_def by blast
  have types: "\<forall>k\<in>?K. paper_R_type (fst k)"
    by (rule paper_R_naming_support_R_types[OF original_type])
  obtain z where third: "paper_R_naming_chart G ?K ?N z"
    using paper_R_naming_chart_exists[OF rich paper_R_naming_support_finite types finite] by blast
  have restricted: "paper_R_naming_chart G ?K (named_vars A) z"
    by (rule paper_R_naming_chart_restrict[OF third subset_refl]) blast
  have xz: "image x ?K \<inter> image z ?K = {}" and yz: "image y ?K \<inter> image z ?K = {}"
    using third unfolding paper_R_naming_chart_def by blast+
  have left: "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow> (paper_R_naming_replace z A \<in> T)"
    by (rule paper_R_theoretical_naming_disjoint[OF rich theory_h language first restricted xz])
  have right: "(paper_R_naming_replace y A \<in> T) \<longleftrightarrow> (paper_R_naming_replace z A \<in> T)"
    by (rule paper_R_theoretical_naming_disjoint[OF rich theory_h language second restricted yz])
  show ?thesis using left right by blast
qed

end
