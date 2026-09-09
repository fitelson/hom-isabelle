theory Bacon_Source_Relational_Recoding_Quantifiers
  imports Bacon_Source_Relational_Recoding_Truth Bacon_Source_Relational_Quantifier_Axiom_Truth
begin

section \<open>The inverse covers exactly each original quantifier domain\<close>

lemma paper_R_recode_domain_ball_inverse:
  assumes injective: "inj_on f (\<Union>\<rho>. D \<rho>)"
  shows "(\<forall>b\<in>paper_R_recode_domain f D \<sigma>. P (paper_R_recode_inverse D f b)) = (\<forall>a\<in>D \<sigma>. P a)"
proof
  assume every: "\<forall>b\<in>paper_R_recode_domain f D \<sigma>. P (paper_R_recode_inverse D f b)"
  show "\<forall>a\<in>D \<sigma>. P a"
  proof (intro ballI)
    fix a
    assume member: "a \<in> D \<sigma>"
    have image: "f a \<in> paper_R_recode_domain f D \<sigma>"
      by (rule paper_R_recode_domainI[where D=D and f=f and \<sigma>=\<sigma>, OF member])
    have property: "P (paper_R_recode_inverse D f (f a))" by (rule bspec[OF every image])
    show "P a" using property by (simp only: paper_R_recode_inverse_on[where D=D and \<sigma>=\<sigma>, OF injective member])
  qed
next
  assume every: "\<forall>a\<in>D \<sigma>. P a"
  show "\<forall>b\<in>paper_R_recode_domain f D \<sigma>. P (paper_R_recode_inverse D f b)"
    by (intro ballI; rule bspec[OF every]; rule paper_R_recode_inverse_type[OF injective]; assumption)
qed

lemma paper_R_recode_domain_bex_inverse:
  assumes injective: "inj_on f (\<Union>\<rho>. D \<rho>)"
  shows "(\<exists>b\<in>paper_R_recode_domain f D \<sigma>. P (paper_R_recode_inverse D f b)) = (\<exists>a\<in>D \<sigma>. P a)"
proof
  assume some: "\<exists>b\<in>paper_R_recode_domain f D \<sigma>. P (paper_R_recode_inverse D f b)"
  obtain b where member: "b \<in> paper_R_recode_domain f D \<sigma>" and property: "P (paper_R_recode_inverse D f b)"
    using some by blast
  show "\<exists>a\<in>D \<sigma>. P a"
    by (rule bexI[where x="paper_R_recode_inverse D f b"], rule property, rule paper_R_recode_inverse_type[OF injective member])
next
  assume some: "\<exists>a\<in>D \<sigma>. P a"
  obtain a where member: "a \<in> D \<sigma>" and property: "P a" using some by blast
  have image: "f a \<in> paper_R_recode_domain f D \<sigma>"
    by (rule paper_R_recode_domainI[where D=D and f=f and \<sigma>=\<sigma>, OF member])
  have lifted: "P (paper_R_recode_inverse D f (f a))"
    by (simp only: paper_R_recode_inverse_on[where D=D and \<sigma>=\<sigma>, OF injective member]; rule property)
  show "\<exists>b\<in>paper_R_recode_domain f D \<sigma>. P (paper_R_recode_inverse D f b)"
    by (rule bexI[where x="f a"], rule lifted, rule image)
qed

context paper_R_bbk_model
begin

lemma paper_R_recode_quantifier_body_truth:
  assumes injective: "inj_on f (\<Union>\<rho>. domain \<rho>)"
    and predicate: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and member: "b \<in> paper_R_recode_domain f domain \<sigma>"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f (g(n := Some b)) (NApp F (NVar n))) =
    valuation (denote ((paper_R_recode_assignment (paper_R_recode_inverse domain f) g)
      (n := Some (paper_R_recode_inverse domain f b))) (NApp F (NVar n)))"
proof -
  have at_name: "b \<in> paper_R_recode_domain f domain (stock n)" by (simp only: nt; rule member)
  have updated: "named_env_typed (paper_R_recode_domain f domain) stock (g(n := Some b))"
    by (rule named_assignment_update_typed[where D="paper_R_recode_domain f domain" and G=stock and n=n, OF typed at_name])
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable: "paper_R_in_language signature stock (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=n, OF nt rt])
  have body: "paper_R_in_language signature stock (NApp F (NVar n)) Prop" by (rule paper_R_language_App[OF predicate variable])
  have covering: "named_adequate (g(n := Some b)) (NApp F (NVar n))"
    using adequate by (auto simp: named_adequate_def named_assignment_update_domain)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective body updated covering] paper_R_recode_assignment_update)
qed

section \<open>Both quantifier clauses range over all image-domain values\<close>

text \<open>
  At b∈f[Dσ], the updated image assignment is typed and adequate
  for Fn. Pulling it back gives the old assignment updated at the
  guarded inverse of b. The preceding domain equivalences range over
  every old a∈Dσ, without surjectivity onto the ambient new carrier.
  Source: Definition 3.1(iii.d–e), p.44. The target model is not assumed.
\<close>

theorem paper_R_recode_forall_truth:
  assumes injective: "inj_on f (\<Union>\<rho>. domain \<rho>)"
    and predicate: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>b\<in>paper_R_recode_domain f domain \<sigma>.
      paper_R_recode_valuation f (paper_R_recode_denote f (g(n := Some b)) (NApp F (NVar n))))"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  let ?P = "\<lambda>a. valuation (denote (?g(n := Some a)) (NApp F (NVar n)))"
  have dt: "named_env_typed domain stock ?g" by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate ?g F" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
  have whole: "paper_R_in_language signature stock (NApp (NLogical (SAll \<sigma>)) F) Prop"
    using paper_R_named_all_language[OF predicate] by (simp only: named_paper_all_def)
  have wa: "named_adequate g (NApp (NLogical (SAll \<sigma>)) F)" using adequate by (simp add: named_adequate_def)
  have old: "valuation (denote ?g (NApp (NLogical (SAll \<sigma>)) F)) = (\<forall>a\<in>domain \<sigma>. ?P a)"
    by (rule valuation_forall[OF predicate dt da nt fresh])
  have projected: "(\<forall>b\<in>paper_R_recode_domain f domain \<sigma>. ?P (paper_R_recode_inverse domain f b)) =
      (\<forall>a\<in>domain \<sigma>. ?P a)"
    by (rule paper_R_recode_domain_ball_inverse[OF injective])
  have bodies: "(\<forall>b\<in>paper_R_recode_domain f domain \<sigma>.
      paper_R_recode_valuation f (paper_R_recode_denote f (g(n := Some b)) (NApp F (NVar n)))) =
    (\<forall>b\<in>paper_R_recode_domain f domain \<sigma>. ?P (paper_R_recode_inverse domain f b))"
    by (rule ball_cong[OF refl]; rule paper_R_recode_quantifier_body_truth[OF injective predicate typed adequate nt]; assumption)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective whole typed wa] old bodies projected)
qed

theorem paper_R_recode_exists_truth:
  assumes injective: "inj_on f (\<Union>\<rho>. domain \<rho>)"
    and predicate: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>b\<in>paper_R_recode_domain f domain \<sigma>.
      paper_R_recode_valuation f (paper_R_recode_denote f (g(n := Some b)) (NApp F (NVar n))))"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  let ?P = "\<lambda>a. valuation (denote (?g(n := Some a)) (NApp F (NVar n)))"
  have dt: "named_env_typed domain stock ?g" by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate ?g F" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
  have whole: "paper_R_in_language signature stock (NApp (NLogical (SEx \<sigma>)) F) Prop"
    using paper_R_named_ex_language[OF predicate] by (simp only: named_paper_ex_def)
  have wa: "named_adequate g (NApp (NLogical (SEx \<sigma>)) F)" using adequate by (simp add: named_adequate_def)
  have old: "valuation (denote ?g (NApp (NLogical (SEx \<sigma>)) F)) = (\<exists>a\<in>domain \<sigma>. ?P a)"
    by (rule valuation_exists[OF predicate dt da nt fresh])
  have projected: "(\<exists>b\<in>paper_R_recode_domain f domain \<sigma>. ?P (paper_R_recode_inverse domain f b)) =
      (\<exists>a\<in>domain \<sigma>. ?P a)"
    by (rule paper_R_recode_domain_bex_inverse[OF injective])
  have bodies: "(\<exists>b\<in>paper_R_recode_domain f domain \<sigma>.
      paper_R_recode_valuation f (paper_R_recode_denote f (g(n := Some b)) (NApp F (NVar n)))) =
    (\<exists>b\<in>paper_R_recode_domain f domain \<sigma>. ?P (paper_R_recode_inverse domain f b))"
    by (rule bex_cong[OF refl]; rule paper_R_recode_quantifier_body_truth[OF injective predicate typed adequate nt]; assumption)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective whole typed wa] old bodies projected)
qed

end

end
