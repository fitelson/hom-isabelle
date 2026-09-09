theory Bacon_Source_Named_Recoding_Quantifiers
  imports Bacon_Source_Named_Recoding_Truth
begin

section \<open>Quantification ranges over precisely the recoded domain\<close>

text \<open>
  For injective f, every value in f[Dσ] has an inverse in Dσ, and
  f⁻¹(f(a)) = a. Quantification over coded values therefore agrees
  with quantification over the old domain. Updating g at a coded value
  becomes the corresponding inverse-value update after pulling g back.
  Source: Bacon–Dorr Definition 3.1(iii.d–e), pp.43–44.

  Status: these clauses require injectivity, not surjectivity onto the
  ambient carrier. No quantified value outside f[Dσ] is used.
  The syntax, fresh named quantifier variable, and adequacy are unchanged.
\<close>

lemma named_image_domain_ball_inv:
  assumes injective: "inj f"
  shows "(\<forall>v \<in> named_image_domain f D \<sigma>. P (inv f v)) = (\<forall>a \<in> D \<sigma>. P a)"
proof
  assume all_image: "\<forall>v \<in> named_image_domain f D \<sigma>. P (inv f v)"
  show "\<forall>a \<in> D \<sigma>. P a"
  proof (rule ballI)
    fix a
    assume member: "a \<in> D \<sigma>"
    have image_member: "f a \<in> named_image_domain f D \<sigma>"
      by (rule named_image_domain_member[where f=f and D=D and \<sigma>=\<sigma> and a=a, OF member])
    have property: "P (inv f (f a))" by (rule bspec[OF all_image image_member])
    show "P a" using property by (simp only: inv_f_f[OF injective])
  qed
next
  assume all_old: "\<forall>a \<in> D \<sigma>. P a"
  show "\<forall>v \<in> named_image_domain f D \<sigma>. P (inv f v)"
  proof (rule ballI)
    fix v
    assume member: "v \<in> named_image_domain f D \<sigma>"
    show "P (inv f v)"
      by (rule bspec[OF all_old named_image_domain_inv_member[OF injective member]])
  qed
qed

lemma named_image_domain_bex_inv:
  assumes injective: "inj f"
  shows "(\<exists>v \<in> named_image_domain f D \<sigma>. P (inv f v)) = (\<exists>a \<in> D \<sigma>. P a)"
proof
  assume some_image: "\<exists>v \<in> named_image_domain f D \<sigma>. P (inv f v)"
  obtain v where member: "v \<in> named_image_domain f D \<sigma>" and property: "P (inv f v)"
    using some_image by (elim bexE)
  show "\<exists>a \<in> D \<sigma>. P a"
    by (rule bexI[where x="inv f v"], rule property,
      rule named_image_domain_inv_member[OF injective member])
next
  assume some_old: "\<exists>a \<in> D \<sigma>. P a"
  obtain a where member: "a \<in> D \<sigma>" and property: "P a"
    using some_old by (elim bexE)
  have image_member: "f a \<in> named_image_domain f D \<sigma>"
    by (rule named_image_domain_member[where f=f and D=D and \<sigma>=\<sigma> and a=a, OF member])
  have image_property: "P (inv f (f a))"
    by (simp only: inv_f_f[OF injective]; rule property)
  show "\<exists>v \<in> named_image_domain f D \<sigma>. P (inv f v)"
    by (rule bexI[where x="f a"], rule image_property, rule image_member)
qed

context paper_named_bbk_model
begin

theorem named_recode_forall_truth:
  assumes injective: "inj f"
    and language: "named_in_language paper_logical_type signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and adequate: "named_adequate g F"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "named_recode_valuation f (named_recode_denote f g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>v \<in> named_image_domain f domain \<sigma>.
      named_recode_valuation f (named_recode_denote f (g(n := Some v)) (NApp F (NVar n))))"
proof -
  let ?q = "named_map_assignment (inv f) g"
  have old_typed: "named_env_typed domain stock ?q"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have old_adequate: "named_adequate ?q F"
    by (rule iffD2[OF named_map_assignment_adequate adequate])
  have old: "valuation (denote ?q (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (?q(n := Some a)) (NApp F (NVar n))))"
    by (rule valuation_forall[OF language old_typed old_adequate n_type fresh])
  have projected:
    "(\<forall>v \<in> named_image_domain f domain \<sigma>.
       valuation (denote (?q(n := Some (inv f v))) (NApp F (NVar n)))) =
     (\<forall>a \<in> domain \<sigma>. valuation (denote (?q(n := Some a)) (NApp F (NVar n))))"
    by (rule named_image_domain_ball_inv[where P="\<lambda>a. valuation (denote
      (?q(n := Some a)) (NApp F (NVar n)))", OF injective])
  show ?thesis using old
    by (simp only: named_recode_truth[OF injective] named_map_assignment_update projected)
qed

theorem named_recode_exists_truth:
  assumes injective: "inj f"
    and language: "named_in_language paper_logical_type signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and adequate: "named_adequate g F"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "named_recode_valuation f (named_recode_denote f g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>v \<in> named_image_domain f domain \<sigma>.
      named_recode_valuation f (named_recode_denote f (g(n := Some v)) (NApp F (NVar n))))"
proof -
  let ?q = "named_map_assignment (inv f) g"
  have old_typed: "named_env_typed domain stock ?q"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have old_adequate: "named_adequate ?q F"
    by (rule iffD2[OF named_map_assignment_adequate adequate])
  have old: "valuation (denote ?q (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (?q(n := Some a)) (NApp F (NVar n))))"
    by (rule valuation_exists[OF language old_typed old_adequate n_type fresh])
  have projected:
    "(\<exists>v \<in> named_image_domain f domain \<sigma>.
       valuation (denote (?q(n := Some (inv f v))) (NApp F (NVar n)))) =
     (\<exists>a \<in> domain \<sigma>. valuation (denote (?q(n := Some a)) (NApp F (NVar n))))"
    by (rule named_image_domain_bex_inv[where P="\<lambda>a. valuation (denote
      (?q(n := Some a)) (NApp F (NVar n)))", OF injective])
  show ?thesis using old
    by (simp only: named_recode_truth[OF injective] named_map_assignment_update projected)
qed

end

end
