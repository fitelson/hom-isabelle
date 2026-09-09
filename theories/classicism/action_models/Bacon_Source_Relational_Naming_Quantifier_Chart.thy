theory Bacon_Source_Relational_Naming_Quantifier_Chart
  imports Bacon_Source_Relational_Naming_Structure Bacon_Source_Relational_Quantifier_Axiom_Truth
begin

section \<open>A quantifier chart also avoids its testing variable\<close>

text \<open>
  Choose the chart for Fn. Its support equals that of F, while its
  variable set includes n. This one chart therefore covers F, ∀F, ∃F
  and Fn, and its override commutes with updating n at every b∈Dσ.
  Neither g nor the chart needs to enumerate the domain. Source:
  Definition 3.1(iii.d–e), p.44, and p.51 n.73.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_naming_quantifier_values:
  assumes predicate: "paper_R_in_language (paper_R_naming_signature signature domain) stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  obtains h C where "paper_R_in_language signature stock C (Arr \<sigma> Prop)"
    and "named_env_typed domain stock h" and "named_adequate h C" and "n \<notin> named_fv C"
    and "paper_R_naming_denote g (NApp (NLogical (SAll \<sigma>)) F) = denote h (NApp (NLogical (SAll \<sigma>)) C)"
    and "paper_R_naming_denote g (NApp (NLogical (SEx \<sigma>)) F) = denote h (NApp (NLogical (SEx \<sigma>)) C)"
    and "\<And>b. b \<in> domain \<sigma> \<Longrightarrow>
      paper_R_naming_denote (g(n := Some b)) (NApp F (NVar n)) = denote (h(n := Some b)) (NApp C (NVar n))"
proof -
  note finish = that
  let ?P = "NApp F (NVar n)"
  let ?x = "paper_R_naming_chosen_chart stock ?P"
  let ?K = "paper_R_naming_support ?P"
  let ?N = "named_vars ?P"
  let ?h = "paper_R_naming_override ?K ?x g"
  let ?C = "paper_R_naming_replace ?x F"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=n, OF nt rt])
  have application: "paper_R_in_language (paper_R_naming_signature signature domain) stock ?P Prop"
    by (rule paper_R_language_App[OF predicate variable])
  have chart: "paper_R_naming_chart stock ?K ?N ?x"
    by (rule paper_R_naming_chosen_chart_language[OF stock_rich application])
  have names: "named_in_signature (paper_R_naming_signature signature domain) ?P"
    using application unfolding paper_R_in_language_def by blast
  have payloads: "\<forall>k\<in>?K. snd k \<in> domain (fst k)" by (rule paper_R_naming_support_values[OF names])
  have fs: "paper_R_naming_support F \<subseteq> ?K" and fv: "named_vars F \<subseteq> ?N" by auto
  have cl: "paper_R_in_language signature stock ?C (Arr \<sigma> Prop)"
    by (rule paper_R_naming_replace_language[OF predicate chart fs])
  have ht: "named_env_typed domain stock ?h" by (rule paper_R_naming_override_typed[OF typed chart payloads])
  have ca: "named_adequate ?h ?C" by (rule paper_R_naming_override_adequate[OF adequate fs])
  have n_in_vars: "n \<in> ?N" by simp
  have outside: "n \<notin> ?x ` ?K" using chart n_in_vars unfolding paper_R_naming_chart_def by blast
  have marker_subset: "?x ` paper_R_naming_support F \<subseteq> ?x ` ?K" by (rule image_mono[OF fs])
  have cf: "n \<notin> named_fv ?C"
    using paper_R_naming_replace_fv_bound[where x="?x" and A=F] fresh marker_subset outside by blast
  have all_language: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NLogical (SAll \<sigma>)) F) Prop"
    by (rule paper_R_named_quantifier_language[OF predicate paper_logical_type.simps(4)])
  have ex_language: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NLogical (SEx \<sigma>)) F) Prop"
    by (rule paper_R_named_quantifier_language[OF predicate paper_logical_type.simps(5)])
  have all_adequate: "named_adequate g (NApp (NLogical (SAll \<sigma>)) F)"
    and ex_adequate: "named_adequate g (NApp (NLogical (SEx \<sigma>)) F)"
    using adequate unfolding named_adequate_def by auto
  have all_support: "paper_R_naming_support (NApp (NLogical (SAll \<sigma>)) F) \<subseteq> ?K"
    and ex_support: "paper_R_naming_support (NApp (NLogical (SEx \<sigma>)) F) \<subseteq> ?K"
    and all_vars: "named_vars (NApp (NLogical (SAll \<sigma>)) F) \<subseteq> ?N"
    and ex_vars: "named_vars (NApp (NLogical (SEx \<sigma>)) F) \<subseteq> ?N" by auto
  have all_value: "paper_R_naming_denote g (NApp (NLogical (SAll \<sigma>)) F) = denote ?h (NApp (NLogical (SAll \<sigma>)) ?C)"
    using paper_R_naming_denote_common_chart[OF all_language typed all_adequate chart all_support all_vars payloads]
    by (simp only: paper_R_naming_replace.simps)
  have ex_value: "paper_R_naming_denote g (NApp (NLogical (SEx \<sigma>)) F) = denote ?h (NApp (NLogical (SEx \<sigma>)) ?C)"
    using paper_R_naming_denote_common_chart[OF ex_language typed ex_adequate chart ex_support ex_vars payloads]
    by (simp only: paper_R_naming_replace.simps)
  have body_value: "paper_R_naming_denote (g(n := Some b)) ?P = denote (?h(n := Some b)) (NApp ?C (NVar n))"
    if member: "b \<in> domain \<sigma>" for b
  proof -
    have slot: "b \<in> domain (stock n)" by (simp only: nt; rule member)
    have updated: "named_env_typed domain stock (g(n := Some b))"
      by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed slot])
    have updated_adequate: "named_adequate (g(n := Some b)) ?P"
      by (rule named_quantifier_application_adequate[OF adequate])
    have commute: "paper_R_naming_override ?K ?x (g(n := Some b)) = ?h(n := Some b)"
      by (rule paper_R_naming_override_update[where K="?K" and x="?x" and n=n, OF outside])
    show ?thesis
      using paper_R_naming_denote_common_chart[OF application updated updated_adequate chart subset_refl subset_refl payloads]
      by (simp only: commute paper_R_naming_replace.simps)
  qed
  show thesis by (rule finish[OF cl ht ca cf all_value ex_value body_value])
qed

end

end
