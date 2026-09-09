theory Bacon_Source_Relational_Normalization_Formula_Validity
  imports Bacon_Source_Relational_Normalization_Validity
    Bacon_Source_Relational_Validity_Basics
begin

section \<open>Canonical record normalization preserves formula validity\<close>

theorem paper_R_bbk_normalize_formula_valid_iff:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
  shows "paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain (paper_R_bbk_normalize \<Sigma> G M))
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G M))
      (paper_bbk_valuation (paper_R_bbk_normalize \<Sigma> G M)) A
    \<longleftrightarrow> paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) A"
proof -
  let ?N = "paper_R_bbk_normalize \<Sigma> G M"
  interpret Original: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF valid])
  interpret Normalized: paper_R_bbk_model \<Sigma> G "paper_bbk_domain ?N"
    "paper_bbk_denote ?N" "paper_bbk_valuation ?N"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_normalize_valid[OF valid]])
  show ?thesis
  proof
    assume holds: "Normalized.paper_R_valid A"
    have language: "paper_R_in_language \<Sigma> G A Prop"
      by (rule Normalized.paper_R_valid_language[OF holds])
    show "Original.paper_R_valid A"
    proof (rule Original.paper_R_validI[OF language])
      fix g
      assume typed: "named_env_typed (paper_bbk_domain M) G g"
        and adequate: "named_adequate g A"
      have nt: "named_env_typed (paper_bbk_domain ?N) G g"
        by (simp only: paper_R_bbk_normalize_domain; rule typed)
      have truth: "paper_bbk_valuation ?N (paper_bbk_denote ?N g A)"
        by (rule Normalized.paper_R_validE[OF holds nt adequate])
      show "paper_bbk_valuation M (paper_bbk_denote M g A)"
        using truth by (simp only: paper_R_bbk_normalize_truth[OF valid language typed adequate])
    qed
  next
    assume holds: "Original.paper_R_valid A"
    have language: "paper_R_in_language \<Sigma> G A Prop"
      by (rule Original.paper_R_valid_language[OF holds])
    show "Normalized.paper_R_valid A"
    proof (rule Normalized.paper_R_validI[OF language])
      fix g
      assume typed: "named_env_typed (paper_bbk_domain ?N) G g"
        and adequate: "named_adequate g A"
      have ot: "named_env_typed (paper_bbk_domain M) G g"
        using typed by (simp only: paper_R_bbk_normalize_domain)
      have truth: "paper_bbk_valuation M (paper_bbk_denote M g A)"
        by (rule Original.paper_R_validE[OF holds ot adequate])
      show "paper_bbk_valuation ?N (paper_bbk_denote ?N g A)"
        by (simp only: paper_R_bbk_normalize_truth[OF valid language ot adequate]; rule truth)
    qed
  qed
qed

corollary paper_R_bbk_normalizes_theory:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and theory_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) A"
  shows "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain (paper_R_bbk_normalize \<Sigma> G M))
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G M))
      (paper_bbk_valuation (paper_R_bbk_normalize \<Sigma> G M)) A"
  by (intro ballI; rule iffD2[OF paper_R_bbk_normalize_formula_valid_iff[OF valid]];
    rule bspec[OF theory_truth]; assumption)

text \<open>
  The domains, hence the typed adequate assignments, are unchanged.
  Normalization only changes interpretation inputs and valuation
  arguments outside their source-defined domains. This applies to
  arbitrary sets T of formulas, including open formulas; no H-theory
  or consistency assumption is used. Source: Definition 3.1 and the
  bounded model-category presentation of pp.51–52.
\<close>

end
