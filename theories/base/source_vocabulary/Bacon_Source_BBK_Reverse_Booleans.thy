theory Bacon_Source_BBK_Reverse_Booleans
  imports Bacon_Source_BBK_Roundtrip Bacon_Source_Reverse_Guarded_Conversion
    Bacon_Source_Defined_Connectives
begin

section \<open>The literal defined implication has its required truth clause\<close>

text \<open>
  V(⟦A → B⟧ᵍ) iff V(⟦A⟧ᵍ) implies V(⟦B⟧ᵍ), where → is
  the actual source λ-definition from Bacon–Dorr Figure 1, p.6.
  We use its guarded syntactic β computation, reverse that computation,
  and apply source denotation recovery and the ¬/∨ truth clauses.

  This proof takes place in the independent weak source structure. It uses
  no target model, source soundness theorem, or identity between primitive
  target implication and the source-defined operation. Target syntax is
  used solely to reuse an already checked syntactic conversion.
\<close>

lemma paper_reverse_not_language:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_not A) Prop"
  using A unfolding sterm_in_language_def by (auto intro: paper_not_type)

lemma paper_reverse_imp_language:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp A B) Prop"
  using A B unfolding sterm_in_language_def by (auto intro: paper_imp_type)

context paper_db_bbk_structure
begin

theorem paper_db_imp_truth:
  assumes A: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_imp A B)) =
    (valuation (denote g A) \<longrightarrow> valuation (denote g B))"
proof -
  let ?A = "pterm_to_paper (paper_to_pterm A)"
  let ?B = "pterm_to_paper (paper_to_pterm B)"
  have rtA: "sterm_in_language paper_logical_type signature \<Gamma> ?A Prop"
    by (rule conjunct1[OF sbeta_eta_equiv_in_signature_language[OF paper_roundtrip_conversion[OF A]]])
  have rtB: "sterm_in_language paper_logical_type signature \<Gamma> ?B Prop"
    by (rule conjunct1[OF sbeta_eta_equiv_in_signature_language[OF paper_roundtrip_conversion[OF B]]])
  have imp: "sterm_in_language paper_logical_type signature \<Gamma> (paper_imp A B) Prop"
    by (rule paper_reverse_imp_language[OF A B])
  have conversion: "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> Prop
    (pterm_to_paper (paper_to_pterm (paper_imp A B))) (paper_or (paper_not ?A) ?B)"
    using pterm_to_paper_guarded_conversion[OF paper_imp_application[OF A B]]
    by (simp only: pterm_to_paper.simps)
  have equality: "denote g (paper_imp A B) = denote g (paper_or (paper_not ?A) ?B)"
    using denote_beta_eta[OF conversion env] paper_db_roundtrip_denotation[OF imp env] by simp
  have disjunction: "valuation (denote g (paper_or (paper_not ?A) ?B)) =
    (valuation (denote g (paper_not ?A)) \<or> valuation (denote g ?B))"
    by (rule valuation_disj[OF paper_reverse_not_language[OF rtA] rtB env])
  have negation: "valuation (denote g (paper_not ?A)) = (\<not> valuation (denote g ?A))"
    by (rule valuation_neg[OF rtA env])
  show ?thesis by (simp only: equality disjunction negation
    paper_db_roundtrip_denotation[OF A env] paper_db_roundtrip_denotation[OF B env]) blast
qed

section \<open>Boolean and identity clauses for reverse-interpreted target terms\<close>

text \<open>
  Interpret a target term M by the source denotation of back(M).
  The target ¬, ∧, ∨, and = clauses then follow directly from their
  first-class source counterparts; target → uses the theorem above.
  These are finite-frame truth clauses, not a named-model equivalence.
\<close>

lemma paper_reverse_neg_truth:
  assumes A: "pterm_in_language signature \<Gamma> A Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PNeg A))) =
    (\<not> valuation (denote g (pterm_to_paper A)))"
  by (simp only: pterm_to_paper.simps; rule valuation_neg[OF pterm_to_paper_language[OF A] env])

lemma paper_reverse_conj_truth:
  assumes A: "pterm_in_language signature \<Gamma> A Prop"
    and B: "pterm_in_language signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PConj A B))) =
    (valuation (denote g (pterm_to_paper A)) \<and> valuation (denote g (pterm_to_paper B)))"
  by (simp only: pterm_to_paper.simps;
    rule valuation_conj[OF pterm_to_paper_language[OF A] pterm_to_paper_language[OF B] env])

lemma paper_reverse_disj_truth:
  assumes A: "pterm_in_language signature \<Gamma> A Prop"
    and B: "pterm_in_language signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PDisj A B))) =
    (valuation (denote g (pterm_to_paper A)) \<or> valuation (denote g (pterm_to_paper B)))"
  by (simp only: pterm_to_paper.simps;
    rule valuation_disj[OF pterm_to_paper_language[OF A] pterm_to_paper_language[OF B] env])

lemma paper_reverse_imp_truth:
  assumes A: "pterm_in_language signature \<Gamma> A Prop"
    and B: "pterm_in_language signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PImp A B))) =
    (valuation (denote g (pterm_to_paper A)) \<longrightarrow> valuation (denote g (pterm_to_paper B)))"
  by (simp only: pterm_to_paper.simps;
    rule paper_db_imp_truth[OF pterm_to_paper_language[OF A] pterm_to_paper_language[OF B] env])

lemma paper_reverse_identity_truth:
  assumes A: "pterm_in_language signature \<Gamma> A \<sigma>"
    and B: "pterm_in_language signature \<Gamma> B \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PEq \<sigma> A B))) =
    (denote g (pterm_to_paper A) = denote g (pterm_to_paper B))"
  by (simp only: pterm_to_paper.simps;
    rule valuation_identity[OF pterm_to_paper_language[OF A] pterm_to_paper_language[OF B] env])

end

end
