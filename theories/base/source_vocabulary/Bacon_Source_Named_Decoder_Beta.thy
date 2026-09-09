theory Bacon_Source_Named_Decoder_Beta
  imports Bacon_Source_Named_Decoder_Freshness
    Bacon_Source_Named_Alpha_Characterization Bacon_Source_Named_Alpha_Conversion
begin

section \<open>A source β root decodes to literal named βη conversion\<close>

text \<open>
  Decode (λσ.M)N using a fresh binder x. The decoded N is free for x
  in the decoded M, so literal named β yields M′[N′/x]. Its encoding
  equals the encoding of the decoded source reduct: both are the unique
  root β reduct of the same encoded redex. The checked α characterization
  and α→literal βη theorem then align the two named reducts.
  Source: Bacon–Dorr Figure 2, p.8, with its capture restriction retained.

  Status. Both source endpoints have the displayed type and signature;
  chart validity and rich G justify decoding. The conclusion is a chain
  of literal β/η conversions, not a new α constructor or H rule. No
  denotation or model assumption is used.
\<close>

lemma sbeta_contract_deterministic:
  assumes first: "sbeta_contract A B" and second: "sbeta_contract A C"
  shows "B = C"
  using first second by (auto elim: sbeta_contract.cases)

lemma source_beta_redex_languages:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> (SApp (SLam \<sigma> M) N) \<tau>"
  shows "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) M \<tau> \<and> sterm_in_language L \<Sigma> \<Gamma> N \<sigma>"
proof -
  have typed: "has_stype L \<Gamma> (SApp (SLam \<sigma> M) N) \<tau>"
    and sig: "sterm_in_signature \<Sigma> (SApp (SLam \<sigma> M) N)"
    using language unfolding sterm_in_language_def by blast+
  obtain \<upsilon> where ft: "has_stype L \<Gamma> (SLam \<sigma> M) (Arr \<upsilon> \<tau>)"
    and nt: "has_stype L \<Gamma> N \<upsilon>"
    by (rule source_app_type_obtain[OF typed]; rule that; assumption)
  obtain \<rho> where arrows: "Arr \<upsilon> \<tau> = Arr \<sigma> \<rho>"
    and mt: "has_stype L (\<sigma> # \<Gamma>) M \<rho>"
    by (rule source_lam_type_obtain[OF ft]; rule that; assumption)
  have domain_eq: "\<upsilon> = \<sigma>" and result_eq: "\<rho> = \<tau>" using arrows by simp_all
  have body: "has_stype L (\<sigma> # \<Gamma>) M \<tau>" using mt by (simp only: result_eq)
  have argument: "has_stype L \<Gamma> N \<sigma>" using nt by (simp only: domain_eq)
  have ms: "sterm_in_signature \<Sigma> M" and ns: "sterm_in_signature \<Sigma> N" using sig by simp_all
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF conjI[OF body ms] conjI[OF argument ns]])
qed

theorem source_to_named_beta_root_conversion:
  assumes root: "sbeta_contract X Y"
    and left: "sterm_in_language L \<Sigma> \<Gamma> X \<tau>"
    and right: "sterm_in_language L \<Sigma> \<Gamma> Y \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns X) (source_to_named G ns Y)"
proof -
  obtain \<sigma> M N where redex: "X = SApp (SLam \<sigma> M) N" and reduct: "Y = ssubst0 N M"
    using root by (cases rule: sbeta_contract.cases) blast
  have redex_language: "sterm_in_language L \<Sigma> \<Gamma> (SApp (SLam \<sigma> M) N) \<tau>"
    using left by (simp only: redex)
  have body_language: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) M \<tau>"
    and argument_language: "sterm_in_language L \<Sigma> \<Gamma> N \<sigma>"
    using source_beta_redex_languages[OF redex_language] by auto
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?M = "source_to_named G (?n # ns) M"
  let ?N = "source_to_named G ns N"
  let ?R = "named_subst ?n ?N ?M"
  have extended: "named_chart G (\<sigma> # \<Gamma>) (?n # ns)"
    by (rule named_chart_fresh_extend[OF chart rich])
  have named_body: "named_in_language L \<Sigma> G ?M \<tau>"
    by (rule source_to_named_language[OF body_language extended rich])
  have named_argument: "named_in_language L \<Sigma> G ?N (G ?n)"
    by (simp only: named_chart_fresh_type[OF rich]; rule source_to_named_language[OF argument_language chart rich])
  have substituted: "named_in_language L \<Sigma> G ?R \<tau>"
    by (rule named_subst_language[OF named_body named_argument])
  have argument_type: "has_stype L \<Gamma> N \<sigma>"
    using argument_language unfolding sterm_in_language_def by (rule conjunct1)
  have free_for: "named_free_for ?N ?n ?M"
    by (rule source_to_named_free_for[OF argument_type chart rich])
  have literal_root: "named_beta_contract (NApp (NLam ?n ?M) ?N) ?R"
    by (rule named_beta_contract.beta[OF free_for])
  have named_root: "named_beta_contract (source_to_named G ns X) ?R"
    using literal_root by (simp only: redex source_to_named.simps)
  have named_step: "named_compatible_step named_beta_contract (source_to_named G ns X) ?R"
    by (rule named_compatible_step.root[where R=named_beta_contract
      and M="source_to_named G ns X" and N="?R", OF named_root])
  have named_left: "named_in_language L \<Sigma> G (source_to_named G ns X) \<tau>"
    by (rule source_to_named_language[OF left chart rich])
  have beta: "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns X) ?R"
    by (rule named_beta_eta_in_language.Beta[OF named_left substituted named_step])
  have encoded_named: "sbeta_contract (named_to_source G [] (source_to_named G ns X))
    (named_to_source G [] ?R)" by (rule named_beta_contract_encoding[OF named_root])
  have left_type: "has_stype L \<Gamma> X \<tau>" and right_type: "has_stype L \<Gamma> Y \<tau>"
    using left right unfolding sterm_in_language_def by blast+
  have left_encoding: "named_to_source G [] (source_to_named G ns X) = srename (\<lambda>i. ns ! i) X"
    by (rule source_to_named_empty_encoding[OF left_type chart rich])
  have right_encoding: "named_to_source G [] (source_to_named G ns Y) = srename (\<lambda>i. ns ! i) Y"
    by (rule source_to_named_empty_encoding[OF right_type chart rich])
  have renamed_root: "sbeta_contract (srename (\<lambda>i. ns ! i) X) (srename (\<lambda>i. ns ! i) Y)"
    by (rule srename_beta[where r="\<lambda>i. ns ! i", OF root])
  have encoded_source: "sbeta_contract (named_to_source G [] (source_to_named G ns X))
    (named_to_source G [] (source_to_named G ns Y))"
    using renamed_root by (simp only: left_encoding right_encoding)
  have same_encoding: "named_to_source G [] ?R = named_to_source G [] (source_to_named G ns Y)"
    by (rule sbeta_contract_deterministic[OF encoded_named encoded_source])
  have alpha: "named_alpha G ?R (source_to_named G ns Y)"
    by (rule named_encoding_implies_alpha[OF rich same_encoding])
  have align: "named_beta_eta_in_language L \<Sigma> G \<tau> ?R (source_to_named G ns Y)"
    by (rule named_alpha_implies_beta_eta[OF alpha substituted])
  show ?thesis by (rule named_beta_eta_in_language.Trans[OF beta align])
qed

end
