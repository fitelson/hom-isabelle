theory Bacon_Source_Named_Tagged_Quantifiers
  imports Bacon_Source_Named_Tagged_Truth Bacon_Source_Named_Denotation_Quantifiers
begin

section \<open>Quantification over explicitly tagged domains\<close>

text \<open>
  Quantifying over D′σ = {⟨σ,a⟩ | a ∈ Dσ} is equivalent to quantifying
  over the old values a. Updating a tagged partial assignment by ⟨σ,a⟩
  becomes the old update by a when its tags are removed.
  Source: Bacon–Dorr Definition 3.1(iii.d–e), pp.43–44.
  Status: the two clauses below are constructed in the weak source
  structure. Original-domain disjointness, a named model, and unrestricted
  conversion conservativity are not premises.
\<close>

lemma named_tag_domain_ball_snd:
  "(\<forall>v \<in> named_tag_domain D \<sigma>. P (snd v)) = (\<forall>a \<in> D \<sigma>. P a)"
proof
  assume all_tagged: "\<forall>v \<in> named_tag_domain D \<sigma>. P (snd v)"
  show "\<forall>a \<in> D \<sigma>. P a"
  proof (intro ballI)
    fix a
    assume member: "a \<in> D \<sigma>"
    have tagged: "(\<sigma>, a) \<in> named_tag_domain D \<sigma>"
      using member by (simp add: named_tag_domain_pair_iff)
    have "P (snd (\<sigma>, a))" by (rule bspec[OF all_tagged tagged])
    then show "P a" by (simp only: snd_conv)
  qed
next
  assume all_old: "\<forall>a \<in> D \<sigma>. P a"
  show "\<forall>v \<in> named_tag_domain D \<sigma>. P (snd v)"
  proof (intro ballI)
    fix v
    assume member: "v \<in> named_tag_domain D \<sigma>"
    show "P (snd v)" by (rule bspec[OF all_old named_tag_domain_snd[OF member]])
  qed
qed

lemma named_tag_domain_bex_snd:
  "(\<exists>v \<in> named_tag_domain D \<sigma>. P (snd v)) = (\<exists>a \<in> D \<sigma>. P a)"
proof
  assume some_tagged: "\<exists>v \<in> named_tag_domain D \<sigma>. P (snd v)"
  obtain v where member: "v \<in> named_tag_domain D \<sigma>" and property: "P (snd v)"
    using some_tagged by (elim bexE)
  show "\<exists>a \<in> D \<sigma>. P a"
    by (rule bexI[where x="snd v"], rule property, rule named_tag_domain_snd[OF member])
next
  assume some_old: "\<exists>a \<in> D \<sigma>. P a"
  obtain a where member: "a \<in> D \<sigma>" and property: "P a"
    using some_old by (elim bexE)
  have tagged: "(\<sigma>, a) \<in> named_tag_domain D \<sigma>"
    using member by (simp add: named_tag_domain_pair_iff)
  have tagged_property: "P (snd (\<sigma>, a))" using property by (simp only: snd_conv)
  show "\<exists>v \<in> named_tag_domain D \<sigma>. P (snd v)"
    by (rule bexI[where x="(\<sigma>, a)"], rule tagged_property, rule tagged)
qed

context paper_db_bbk_structure
begin

theorem paper_db_tagged_named_forall_truth:
  assumes language: "named_in_language paper_logical_type signature G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g F"
    and n_type: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "valuation (snd (tagged_named_denote G g (NApp (NLogical (SAll \<sigma>)) F))) =
    (\<forall>v \<in> named_tag_domain domain \<sigma>.
      valuation (snd (tagged_named_denote G (g(n := Some v)) (NApp F (NVar n)))))"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) F"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old:
    "valuation (named_denote G (named_untag_assignment g) (NApp (NLogical (SAll \<sigma>)) F)) =
     (\<forall>a \<in> domain \<sigma>. valuation (named_denote G
       ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule paper_db_named_forall_truth[OF language old_typed old_adequate n_type fresh])
  have projected:
    "(\<forall>v \<in> named_tag_domain domain \<sigma>. valuation (named_denote G
      ((named_untag_assignment g)(n := Some (snd v))) (NApp F (NVar n)))) =
     (\<forall>a \<in> domain \<sigma>. valuation (named_denote G
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule named_tag_domain_ball_snd[where P="\<lambda>a. valuation (named_denote G
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n)))"])
  show ?thesis using old
    by (simp only: tagged_named_denote_def snd_conv named_untag_assignment_update
      projected)
qed

theorem paper_db_tagged_named_exists_truth:
  assumes language: "named_in_language paper_logical_type signature G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g F"
    and n_type: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "valuation (snd (tagged_named_denote G g (NApp (NLogical (SEx \<sigma>)) F))) =
    (\<exists>v \<in> named_tag_domain domain \<sigma>.
      valuation (snd (tagged_named_denote G (g(n := Some v)) (NApp F (NVar n)))))"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) F"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old:
    "valuation (named_denote G (named_untag_assignment g) (NApp (NLogical (SEx \<sigma>)) F)) =
     (\<exists>a \<in> domain \<sigma>. valuation (named_denote G
       ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule paper_db_named_exists_truth[OF language old_typed old_adequate n_type fresh])
  have projected:
    "(\<exists>v \<in> named_tag_domain domain \<sigma>. valuation (named_denote G
      ((named_untag_assignment g)(n := Some (snd v))) (NApp F (NVar n)))) =
     (\<exists>a \<in> domain \<sigma>. valuation (named_denote G
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule named_tag_domain_bex_snd[where P="\<lambda>a. valuation (named_denote G
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n)))"])
  show ?thesis using old
    by (simp only: tagged_named_denote_def snd_conv named_untag_assignment_update
      projected)
qed

end

end
