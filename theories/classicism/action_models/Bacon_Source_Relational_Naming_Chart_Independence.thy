theory Bacon_Source_Relational_Naming_Chart_Independence
  imports Bacon_Source_Relational_Naming_Chart_Mixing
    Bacon_Source_Relational_Naming_Coordinate_Denotation
begin

section \<open>Finite chart choice does not affect the interpreted value\<close>

text \<open>
  First change finitely many coordinates between charts with disjoint
  images. Arbitrary charts are compared through a third chart avoiding
  both images and all original variable names. Only the finitely many
  typed new names in the term are assigned temporary variables.
  Source role: the naming extension ℒ_M in p.51 n.73.

  The interpretation below is still parametrized by a chart. This leaf
  proves independence of that parameter on meaningful inputs; it does
  not assume or construct the full expanded-model predicate.
\<close>

context paper_R_bbk_model
begin

definition paper_R_naming_chart_denote ::
  "((otype \<times> 'v) \<Rightarrow> nat) \<Rightarrow> 'v named_assignment \<Rightarrow>
    ('c + 'v) paper_named_term \<Rightarrow> 'v" where
  "paper_R_naming_chart_denote x g A =
    denote (paper_R_naming_override (paper_R_naming_support A) x g) (paper_R_naming_replace x A)"

lemma paper_R_naming_disjoint_charts_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and first: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) y"
    and disjoint: "x ` paper_R_naming_support A \<inter> y ` paper_R_naming_support A = {}"
  shows "paper_R_naming_chart_denote x g A = paper_R_naming_chart_denote y g A"
proof -
  let ?K = "paper_R_naming_support A"
  have finite_changes: "paper_R_naming_chart_denote (paper_R_naming_mix L x y) g A =
      paper_R_naming_chart_denote x g A" if finite: "finite L" and support: "L \<subseteq> ?K" for L
    using finite support
  proof (induction rule: finite_induct)
    case empty
    show ?case by simp
  next
    case (insert k L)
    have key: "k \<in> ?K" and smaller: "L \<subseteq> ?K" using insert.prems by auto
    have previous: "paper_R_naming_chart_denote (paper_R_naming_mix L x y) g A =
        paper_R_naming_chart_denote x g A" by (rule insert.IH[OF smaller])
    have before: "paper_R_naming_chart stock ?K (named_vars A) (paper_R_naming_mix L x y)"
      by (rule paper_R_naming_mix_chart[OF first second disjoint])
    have after: "paper_R_naming_chart stock ?K (named_vars A) (paper_R_naming_mix (insert k L) x y)"
      by (rule paper_R_naming_mix_chart[OF first second disjoint])
    have agree: "paper_R_naming_mix (insert k L) x y j = paper_R_naming_mix L x y j"
      if member: "j \<in> ?K" and different: "j \<noteq> k" for j
      using different by (simp add: paper_R_naming_mix_def)
    have coordinate: "paper_R_naming_chart_denote (paper_R_naming_mix (insert k L) x y) g A =
        paper_R_naming_chart_denote (paper_R_naming_mix L x y) g A"
      unfolding paper_R_naming_chart_denote_def
      by (rule paper_R_naming_chart_coordinate_denote[OF language typed adequate before after key agree])
    show ?case by (rule trans[OF coordinate previous])
  qed
  have complete: "paper_R_naming_chart_denote (paper_R_naming_mix ?K x y) g A =
      paper_R_naming_chart_denote x g A"
    by (rule finite_changes[OF paper_R_naming_support_finite subset_refl])
  have mixed: "paper_R_naming_chart stock ?K (named_vars A) (paper_R_naming_mix ?K x y)"
    by (rule paper_R_naming_mix_chart[OF first second disjoint])
  have agree: "paper_R_naming_mix ?K x y k = y k" if "k \<in> ?K" for k
    using that by (simp add: paper_R_naming_mix_def)
  have replacement: "paper_R_naming_replace (paper_R_naming_mix ?K x y) A = paper_R_naming_replace y A"
    by (rule paper_R_naming_replace_chart_agreement[OF agree])
  have assignment: "paper_R_naming_override ?K (paper_R_naming_mix ?K x y) g = paper_R_naming_override ?K y g"
    by (rule paper_R_naming_override_chart_agreement[
      OF paper_R_naming_chart_injective[OF mixed] paper_R_naming_chart_injective[OF second] agree])
  show ?thesis using complete by (simp only: paper_R_naming_chart_denote_def replacement assignment)
qed

theorem paper_R_naming_chart_denote_independent:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and first: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) y"
  shows "paper_R_naming_chart_denote x g A = paper_R_naming_chart_denote y g A"
proof -
  let ?K = "paper_R_naming_support A"
  let ?N = "named_vars A \<union> x ` ?K \<union> y ` ?K"
  have finite: "finite ?N" by (simp add: named_vars_finite paper_R_naming_support_finite)
  have original_type: "paper_R_has_type stock A \<tau>"
    using language unfolding paper_R_in_language_def by blast
  have types: "\<forall>k\<in>?K. paper_R_type (fst k)"
    by (rule paper_R_naming_support_R_types[OF original_type])
  obtain z where third: "paper_R_naming_chart stock ?K ?N z"
    using paper_R_naming_chart_exists[OF stock_rich paper_R_naming_support_finite types finite] by blast
  have restricted: "paper_R_naming_chart stock ?K (named_vars A) z"
    by (rule paper_R_naming_chart_restrict[OF third subset_refl]) blast
  have xz: "x ` ?K \<inter> z ` ?K = {}" and yz: "y ` ?K \<inter> z ` ?K = {}"
    using third unfolding paper_R_naming_chart_def by blast+
  have left: "paper_R_naming_chart_denote x g A = paper_R_naming_chart_denote z g A"
    by (rule paper_R_naming_disjoint_charts_denote[OF language typed adequate first restricted xz])
  have right: "paper_R_naming_chart_denote y g A = paper_R_naming_chart_denote z g A"
    by (rule paper_R_naming_disjoint_charts_denote[OF language typed adequate second restricted yz])
  show ?thesis using left right by simp
qed

end

end
