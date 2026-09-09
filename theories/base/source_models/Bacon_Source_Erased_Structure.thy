theory Bacon_Source_Erased_Structure
  imports Bacon_Source_Erased_Denotation Bacon_Source_Framed_Application
begin

section \<open>Structural clauses after recovery of the supported tagged frame\<close>

text \<open>
  The erased interpretation agrees with the framed interpretation at every
  typed environment. Variables therefore retain their values, application
  preserves equal heads and arguments, and typed βη conversion preserves
  denotation. Source: Bacon–Dorr Definition 3.1(ii.a,b,d), p.44.

  Representation. Each theorem starts with an independently specified
  named model on tagged domains. The two applications may use different
  contexts, assignments, argument types, and result types. No locality,
  model assembly, or unguarded Γ-erasure claim is supplied in this leaf.
\<close>

lemma named_erased_denote_chosen:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> M \<tau>"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "named_erased_denote G J \<rho> M =
    J (named_chart_assignment (named_chart_choice G \<Gamma>) \<rho>) (source_to_named G (named_chart_choice G \<Gamma>) M)"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  show ?thesis by (rule named_erased_denote_agrees[OF model language env named_chart_choice_valid[OF Named.stock_rich]])
qed

lemma named_erased_application_language:
  assumes head: "sterm_in_language L \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and argument: "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
  shows "sterm_in_language L \<Sigma> \<Gamma> (SApp F A) \<tau>"
proof -
  have ft: "has_stype L \<Gamma> F (Arr \<sigma> \<tau>)" and at: "has_stype L \<Gamma> A \<sigma>"
    and fs: "sterm_in_signature \<Sigma> F" and asig: "sterm_in_signature \<Sigma> A"
    using head argument unfolding sterm_in_language_def by blast+
  have types: "has_stype L \<Gamma> (SApp F A) \<tau>" by (rule has_stype.App[OF ft at])
  have names: "sterm_in_signature \<Sigma> (SApp F A)" using fs asig by simp
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF types names])
qed

theorem named_erased_denote_var:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and slot: "lookup \<Gamma> i = Some \<sigma>" and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "named_erased_denote G J \<rho> (SVar i) = \<rho> i"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  have language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SVar i) \<sigma>"
    unfolding sterm_in_language_def by (rule conjI[OF has_stype.Var[OF slot]]) simp
  have agreement: "named_erased_denote G J \<rho> (SVar i) = Named.framed_denote \<Gamma> \<rho> (SVar i)"
    using named_erased_denote_chosen[OF model language env]
    by (simp only: Named.framed_denote_def Named.chart_denote_def)
  show ?thesis by (rule trans[OF agreement Named.framed_denote_var[OF env slot]])
qed

theorem named_erased_denote_application:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and fl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and hl: "sterm_in_language paper_logical_type \<Sigma> \<Delta> H (Arr \<upsilon> \<omega>)"
    and bl: "sterm_in_language paper_logical_type \<Sigma> \<Delta> B \<upsilon>"
    and re: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
    and se: "pbbk_env_typed (named_tag_domain D) \<Delta> \<xi>"
    and heads: "named_erased_denote G J \<rho> F = named_erased_denote G J \<xi> H"
    and arguments: "named_erased_denote G J \<rho> A = named_erased_denote G J \<xi> B"
  shows "named_erased_denote G J \<rho> (SApp F A) = named_erased_denote G J \<xi> (SApp H B)"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  have fa: "named_erased_denote G J \<rho> F = Named.framed_denote \<Gamma> \<rho> F"
    using named_erased_denote_chosen[OF model fl re] by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have aa: "named_erased_denote G J \<rho> A = Named.framed_denote \<Gamma> \<rho> A"
    using named_erased_denote_chosen[OF model al re] by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have ha: "named_erased_denote G J \<xi> H = Named.framed_denote \<Delta> \<xi> H"
    using named_erased_denote_chosen[OF model hl se] by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have ba: "named_erased_denote G J \<xi> B = Named.framed_denote \<Delta> \<xi> B"
    using named_erased_denote_chosen[OF model bl se] by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have framed_heads: "Named.framed_denote \<Gamma> \<rho> F = Named.framed_denote \<Delta> \<xi> H"
    by (rule trans[OF sym[OF fa] trans[OF heads ha]])
  have framed_arguments: "Named.framed_denote \<Gamma> \<rho> A = Named.framed_denote \<Delta> \<xi> B"
    by (rule trans[OF sym[OF aa] trans[OF arguments ba]])
  have apps: "Named.framed_denote \<Gamma> \<rho> (SApp F A) = Named.framed_denote \<Delta> \<xi> (SApp H B)"
    by (rule Named.framed_denote_application[OF fl al hl bl re se framed_heads framed_arguments])
  have left_language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F A) \<tau>"
    by (rule named_erased_application_language[OF fl al])
  have right_language: "sterm_in_language paper_logical_type \<Sigma> \<Delta> (SApp H B) \<omega>"
    by (rule named_erased_application_language[OF hl bl])
  have left_agree: "named_erased_denote G J \<rho> (SApp F A) = Named.framed_denote \<Gamma> \<rho> (SApp F A)"
    using named_erased_denote_chosen[OF model left_language re] by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have right_agree: "named_erased_denote G J \<xi> (SApp H B) = Named.framed_denote \<Delta> \<xi> (SApp H B)"
    using named_erased_denote_chosen[OF model right_language se] by (simp only: Named.framed_denote_def Named.chart_denote_def)
  show ?thesis by (rule trans[OF left_agree trans[OF apps sym[OF right_agree]]])
qed

theorem named_erased_denote_conversion:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<tau> A B"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "named_erased_denote G J \<rho> A = named_erased_denote G J \<rho> B"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  have languages: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<tau> \<and>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<tau>"
    by (rule sbeta_eta_equiv_in_signature_language[OF conversion])
  have left: "named_erased_denote G J \<rho> A = Named.framed_denote \<Gamma> \<rho> A"
    using named_erased_denote_chosen[OF model conjunct1[OF languages] env]
    by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have right: "named_erased_denote G J \<rho> B = Named.framed_denote \<Gamma> \<rho> B"
    using named_erased_denote_chosen[OF model conjunct2[OF languages] env]
    by (simp only: Named.framed_denote_def Named.chart_denote_def)
  have equivalent: "Named.framed_denote \<Gamma> \<rho> A = Named.framed_denote \<Gamma> \<rho> B"
    by (rule Named.framed_denote_conversion[OF conversion env])
  show ?thesis by (rule trans[OF left trans[OF equivalent sym[OF right]]])
qed

end
