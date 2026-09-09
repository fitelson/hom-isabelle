theory Bacon_Source_Relational_Naming_Structure
  imports Bacon_Source_Relational_Naming_Interpretation Bacon_Source_Relational_Naming_Finite_Family
begin

section \<open>Locality and heterogeneous application for the actual naming interpretation\<close>

text \<open>
  One finite chart covers the two applications and their operands.
  The operands retain their separately given types, and the original
  heterogeneous application-congruence clause applies under two typed
  overriding assignments. No pointwise abstraction principle or
  Functionality is substituted for that source clause.
  Source: Definition 3.1(ii.b–c), p.44, and p.51 n.73.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_denote_locality:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and first: "named_env_typed domain stock g" and second: "named_env_typed domain stock h"
    and first_adequate: "named_adequate g A" and second_adequate: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "paper_R_naming_denote g A = paper_R_naming_denote h A"
  unfolding paper_R_naming_denote_def
  by (rule paper_R_naming_chart_denote_locality[OF language
    paper_R_naming_chosen_chart_language[OF stock_rich language]
    first second first_adequate second_adequate agree])

theorem paper_R_naming_denote_application_cong:
  assumes fl: "paper_R_in_language (paper_R_naming_signature signature domain) stock F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<sigma>"
    and hl: "paper_R_in_language (paper_R_naming_signature signature domain) stock H (Arr \<upsilon> \<rho>)"
    and bl: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<upsilon>"
    and gt: "named_env_typed domain stock g" and ht: "named_env_typed domain stock h"
    and ga: "named_adequate g (NApp F A)" and ha: "named_adequate h (NApp H B)"
    and heads: "paper_R_naming_denote g F = paper_R_naming_denote h H"
    and arguments: "paper_R_naming_denote g A = paper_R_naming_denote h B"
  shows "paper_R_naming_denote g (NApp F A) = paper_R_naming_denote h (NApp H B)"
proof -
  let ?T = "{F,A,H,B,NApp F A,NApp H B}"
  let ?L = "paper_R_naming_family_support ?T"
  let ?N = "paper_R_naming_family_vars ?T"
  have left_language: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp F A) \<tau>"
    by (rule paper_R_language_App[OF fl al])
  have right_language: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp H B) \<rho>"
    by (rule paper_R_language_App[OF hl bl])
  have finite: "finite ?T" by simp
  have languages: "\<exists>\<delta>. paper_R_in_language (paper_R_naming_signature signature domain) stock C \<delta>"
    if member: "C \<in> ?T" for C
    using member fl al hl bl left_language right_language by blast
  obtain x where chart: "paper_R_naming_chart stock ?L ?N x"
    and payloads: "\<forall>k\<in>?L. snd k \<in> domain (fst k)"
    by (rule paper_R_naming_family_chart_exists[OF stock_rich finite languages])
  let ?gx = "paper_R_naming_override ?L x g"
  let ?hx = "paper_R_naming_override ?L x h"
  have support: "paper_R_naming_support C \<subseteq> ?L" if "C \<in> ?T" for C
    by (rule paper_R_naming_family_support_contains[OF that])
  have avoid: "named_vars C \<subseteq> ?N" if "C \<in> ?T" for C
    by (rule paper_R_naming_family_vars_contains[OF that])
  have old_language: "paper_R_in_language signature stock (paper_R_naming_replace x C) \<delta>"
    if member: "C \<in> ?T" and language: "paper_R_in_language (paper_R_naming_signature signature domain) stock C \<delta>" for C \<delta>
    by (rule paper_R_naming_replace_language[OF language chart support[OF member]])
  have computation: "paper_R_naming_denote k C =
      denote (paper_R_naming_override ?L x k) (paper_R_naming_replace x C)"
    if member: "C \<in> ?T" and language: "paper_R_in_language (paper_R_naming_signature signature domain) stock C \<delta>"
      and typed: "named_env_typed domain stock k" and adequate: "named_adequate k C" for k C \<delta>
    by (rule paper_R_naming_denote_common_chart[OF language typed adequate chart
      support[OF member] avoid[OF member] payloads])
  have fa: "named_adequate g F" and aa: "named_adequate g A"
    using ga unfolding named_adequate_def by auto
  have hfa: "named_adequate h H" and ba: "named_adequate h B"
    using ha unfolding named_adequate_def by auto
  have fm: "F \<in> ?T" and am: "A \<in> ?T" and hm: "H \<in> ?T" and bm: "B \<in> ?T"
    and fam: "NApp F A \<in> ?T" and hbm: "NApp H B \<in> ?T" by auto
  have fx: "paper_R_in_language signature stock (paper_R_naming_replace x F) (Arr \<sigma> \<tau>)"
    by (rule old_language[OF fm fl])
  have ax: "paper_R_in_language signature stock (paper_R_naming_replace x A) \<sigma>"
    by (rule old_language[OF am al])
  have hx: "paper_R_in_language signature stock (paper_R_naming_replace x H) (Arr \<upsilon> \<rho>)"
    by (rule old_language[OF hm hl])
  have bx: "paper_R_in_language signature stock (paper_R_naming_replace x B) \<upsilon>"
    by (rule old_language[OF bm bl])
  have gxt: "named_env_typed domain stock ?gx" by (rule paper_R_naming_override_typed[OF gt chart payloads])
  have hxt: "named_env_typed domain stock ?hx" by (rule paper_R_naming_override_typed[OF ht chart payloads])
  have gxa: "named_adequate ?gx (NApp (paper_R_naming_replace x F) (paper_R_naming_replace x A))"
    using paper_R_naming_override_adequate[OF ga support[OF fam]] by (simp only: paper_R_naming_replace.simps)
  have hxa: "named_adequate ?hx (NApp (paper_R_naming_replace x H) (paper_R_naming_replace x B))"
    using paper_R_naming_override_adequate[OF ha support[OF hbm]] by (simp only: paper_R_naming_replace.simps)
  have head_values: "denote ?gx (paper_R_naming_replace x F) = denote ?hx (paper_R_naming_replace x H)"
    using heads by (simp only: computation[OF fm fl gt fa] computation[OF hm hl ht hfa])
  have argument_values: "denote ?gx (paper_R_naming_replace x A) = denote ?hx (paper_R_naming_replace x B)"
    using arguments by (simp only: computation[OF am al gt aa] computation[OF bm bl ht ba])
  have application: "denote ?gx (NApp (paper_R_naming_replace x F) (paper_R_naming_replace x A)) =
      denote ?hx (NApp (paper_R_naming_replace x H) (paper_R_naming_replace x B))"
    by (rule denote_application_cong[OF fx ax hx bx gxt hxt gxa hxa head_values argument_values])
  show ?thesis by (simp only: computation[OF fam left_language gt ga]
    computation[OF hbm right_language ht ha] paper_R_naming_replace.simps; rule application)
qed

end

end
