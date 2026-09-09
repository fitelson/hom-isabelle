theory Bacon_Source_Relational_Naming_Quantifier_Truth
  imports Bacon_Source_Relational_Naming_Quantifier_Chart
begin

section \<open>All-domain quantifier truth in the naming interpretation\<close>

text \<open>
  The testing variable is fresh for F, and the common chart also avoids
  it. The correspondence of updated bodies holds for EVERY b∈Dσ,
  not merely old closed-denotable values. The domain and valuation are
  unchanged, and no expanded-model predicate is assumed.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_forall_truth:
  assumes predicate: "paper_R_in_language (paper_R_naming_signature signature domain) stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "valuation (paper_R_naming_denote g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>b\<in>domain \<sigma>. valuation (paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n))))"
proof -
  obtain h C where cl: "paper_R_in_language signature stock C (Arr \<sigma> Prop)"
    and ht: "named_env_typed domain stock h" and ca: "named_adequate h C" and cf: "n \<notin> named_fv C"
    and av: "paper_R_naming_denote g (NApp (NLogical (SAll \<sigma>)) F) = denote h (NApp (NLogical (SAll \<sigma>)) C)"
    and ev: "paper_R_naming_denote g (NApp (NLogical (SEx \<sigma>)) F) = denote h (NApp (NLogical (SEx \<sigma>)) C)"
    and body: "\<And>b. b \<in> domain \<sigma> \<Longrightarrow> paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n)) =
      denote (h(n := Some b)) (NApp C (NVar n))"
    by (rule paper_R_naming_quantifier_values[OF predicate typed adequate nt fresh]; rule that; assumption)
  have original: "valuation (denote h (NApp (NLogical (SAll \<sigma>)) C)) =
      (\<forall>b\<in>domain \<sigma>. valuation (denote (h(n := Some b)) (NApp C (NVar n))))"
    by (rule valuation_forall[OF cl ht ca nt cf])
  have bodies: "(\<forall>b\<in>domain \<sigma>. valuation (paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n)))) =
      (\<forall>b\<in>domain \<sigma>. valuation (denote (h(n := Some b)) (NApp C (NVar n))))"
  proof (rule ball_cong[OF refl])
    fix b
    assume member: "b \<in> domain \<sigma>"
    show "valuation (paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n))) =
      valuation (denote (h(n := Some b)) (NApp C (NVar n)))" by (simp only: body[OF member])
  qed
  show ?thesis by (simp only: av original bodies)
qed

theorem paper_R_naming_exists_truth:
  assumes predicate: "paper_R_in_language (paper_R_naming_signature signature domain) stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "valuation (paper_R_naming_denote g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>b\<in>domain \<sigma>. valuation (paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n))))"
proof -
  obtain h C where cl: "paper_R_in_language signature stock C (Arr \<sigma> Prop)"
    and ht: "named_env_typed domain stock h" and ca: "named_adequate h C" and cf: "n \<notin> named_fv C"
    and av: "paper_R_naming_denote g (NApp (NLogical (SAll \<sigma>)) F) = denote h (NApp (NLogical (SAll \<sigma>)) C)"
    and ev: "paper_R_naming_denote g (NApp (NLogical (SEx \<sigma>)) F) = denote h (NApp (NLogical (SEx \<sigma>)) C)"
    and body: "\<And>b. b \<in> domain \<sigma> \<Longrightarrow> paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n)) =
      denote (h(n := Some b)) (NApp C (NVar n))"
    by (rule paper_R_naming_quantifier_values[OF predicate typed adequate nt fresh]; rule that; assumption)
  have original: "valuation (denote h (NApp (NLogical (SEx \<sigma>)) C)) =
      (\<exists>b\<in>domain \<sigma>. valuation (denote (h(n := Some b)) (NApp C (NVar n))))"
    by (rule valuation_exists[OF cl ht ca nt cf])
  have bodies: "(\<exists>b\<in>domain \<sigma>. valuation (paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n)))) =
      (\<exists>b\<in>domain \<sigma>. valuation (denote (h(n := Some b)) (NApp C (NVar n))))"
  proof (rule bex_cong[OF refl])
    fix b
    assume member: "b \<in> domain \<sigma>"
    show "valuation (paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n))) =
      valuation (denote (h(n := Some b)) (NApp C (NVar n)))" by (simp only: body[OF member])
  qed
  show ?thesis by (simp only: ev original bodies)
qed

end

end
