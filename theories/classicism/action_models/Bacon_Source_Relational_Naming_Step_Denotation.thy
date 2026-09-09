theory Bacon_Source_Relational_Naming_Step_Denotation
  imports Bacon_Source_Relational_Naming_Structure Bacon_Source_Relational_Naming_Conversion_Steps
begin

section \<open>One actual common chart for a β or η step\<close>

context paper_R_bbk_model
begin

lemma paper_R_naming_step_denote:
  assumes left: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and right: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<tau>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
    and step: "named_compatible_step named_beta_contract A B \<or> named_compatible_step named_eta_contract A B"
  shows "paper_R_naming_denote g A = paper_R_naming_denote g B"
proof -
  let ?T = "{A,B}"
  let ?K = "paper_R_naming_family_support ?T"
  let ?N = "paper_R_naming_family_vars ?T"
  have finite: "finite ?T" by simp
  have languages: "\<exists>\<rho>. paper_R_in_language (paper_R_naming_signature signature domain) stock C \<rho>"
    if "C \<in> ?T" for C using that left right by blast
  obtain x where chart: "paper_R_naming_chart stock ?K ?N x"
    and payloads: "\<forall>k\<in>?K. snd k \<in> domain (fst k)"
    by (rule paper_R_naming_family_chart_exists[OF stock_rich finite languages])
  let ?h = "paper_R_naming_override ?K x g"
  let ?C = "paper_R_naming_replace x A"
  let ?E = "paper_R_naming_replace x B"
  have am: "A \<in> ?T" and bm: "B \<in> ?T" by auto
  have asupport: "paper_R_naming_support A \<subseteq> ?K"
    by (rule paper_R_naming_family_support_contains[OF am])
  have bsupport: "paper_R_naming_support B \<subseteq> ?K"
    by (rule paper_R_naming_family_support_contains[OF bm])
  have avars: "named_vars A \<subseteq> ?N" by (rule paper_R_naming_family_vars_contains[OF am])
  have bvars: "named_vars B \<subseteq> ?N" by (rule paper_R_naming_family_vars_contains[OF bm])
  have cl: "paper_R_in_language signature stock ?C \<tau>"
    by (rule paper_R_naming_replace_language[OF left chart asupport])
  have el: "paper_R_in_language signature stock ?E \<tau>"
    by (rule paper_R_naming_replace_language[OF right chart bsupport])
  have ct: "paper_R_has_type stock ?C \<tau>" and et: "paper_R_has_type stock ?E \<tau>"
    using cl el unfolding paper_R_in_language_def by blast+
  have ht: "named_env_typed domain stock ?h" by (rule paper_R_naming_override_typed[OF typed chart payloads])
  have ca: "named_adequate ?h ?C" by (rule paper_R_naming_override_adequate[OF aa asupport])
  have ea: "named_adequate ?h ?E" by (rule paper_R_naming_override_adequate[OF ba bsupport])
  have conversion: "paper_R_raw_beta_eta stock \<tau> ?C ?E"
  proof (rule disjE[OF step])
    assume beta_step: "named_compatible_step named_beta_contract A B"
    have contracted: "named_compatible_step named_beta_contract ?C ?E"
      by (rule paper_R_naming_chart_beta_step[OF beta_step chart asupport avars])
    show ?thesis by (rule paper_R_raw_beta_eta.Beta[OF ct et contracted])
  next
    assume eta_step: "named_compatible_step named_eta_contract A B"
    have contracted: "named_compatible_step named_eta_contract ?C ?E"
      by (rule paper_R_naming_chart_eta_step[OF eta_step chart asupport avars])
    show ?thesis by (rule paper_R_raw_beta_eta.Eta[OF ct et contracted])
  qed
  have old_equal: "denote ?h ?C = denote ?h ?E" by (rule denote_beta_eta[OF conversion cl el ht ca ea])
  have left_value: "paper_R_naming_denote g A = denote ?h ?C"
    by (rule paper_R_naming_denote_common_chart[OF left typed aa chart asupport avars payloads])
  have right_value: "paper_R_naming_denote g B = denote ?h ?E"
    by (rule paper_R_naming_denote_common_chart[OF right typed ba chart bsupport bvars payloads])
  show ?thesis by (simp only: left_value right_value old_equal)
qed

theorem paper_R_naming_beta_step_denote:
  assumes step: "named_compatible_step named_beta_contract A B"
    and left: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and right: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<tau>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_naming_denote g A = paper_R_naming_denote g B"
  by (rule paper_R_naming_step_denote[OF left right typed aa ba disjI1[OF step]])

theorem paper_R_naming_eta_step_denote:
  assumes step: "named_compatible_step named_eta_contract A B"
    and left: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and right: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<tau>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_naming_denote g A = paper_R_naming_denote g B"
  by (rule paper_R_naming_step_denote[OF left right typed aa ba disjI2[OF step]])

end

end
