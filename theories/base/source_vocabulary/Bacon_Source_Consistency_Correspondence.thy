theory Bacon_Source_Consistency_Correspondence
  imports Bacon_Source_Consistency_Basics Bacon_Source_Set_Correspondence
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Refutation_Consistency
begin

section \<open>Source and target consistency agree for closed sentence sets\<close>

text \<open>
  For a sentence set S of ℒ(Σ) and a rich variable stock G, source
  consistency of S agrees with target consistency of tr(S).
  Source role: the consistent sentence sets of Bacon–Dorr Theorem 3.2,
  pp.44–45, connected through the independent source/target consequence
  translations and Figure 2's PC/MP rules.

  Isabelle representation.  Source inconsistency means some derivable
  contradictory pair, with no closedness restriction on that pair.  Source
  explosion gives the closed formulas C := back(PObjTrue) and ¬C.
  Forward set preservation and the guarded β conversion of the source
  negation application give a target contradictory pair, hence PObjFalse.
  Conversely, target PObjFalse and the target theorem PObjTrue pull back
  to ¬C and C in the source local relation.

  Status.  No identity between source and target falsity operators is
  needed or asserted.  S and the declared names may be uncountable.
  The result is proof-theoretic consistency correspondence for the paper
  basis and full F types, not a model theorem, a book-basis result, or a
  named-variable/α-equivalence correspondence.
\<close>

lemma paper_back_truth_sentence:
  fixes \<Sigma> :: "'c ssignature"
  shows "sterm_in_language paper_logical_type \<Sigma> [] (pterm_to_paper (PObjTrue :: 'c pterm)) Prop"
proof -
  have theorem_H: "pH_proves \<Sigma> [] (PObjTrue :: 'c pterm)" by (rule pH_proves_PObjTrue)
  have language: "pterm_in_language \<Sigma> [] (PObjTrue :: 'c pterm) Prop"
    by (rule pH_proves_in_language[OF theorem_H])
  show ?thesis by (rule pterm_to_paper_language[OF language])
qed

lemma paper_back_truth_negation_sentence:
  fixes \<Sigma> :: "'c ssignature"
  shows "sterm_in_language paper_logical_type \<Sigma> [] (paper_not (pterm_to_paper (PObjTrue :: 'c pterm))) Prop"
proof -
  have language: "sterm_in_language paper_logical_type \<Sigma> [] (pterm_to_paper (PObjTrue :: 'c pterm)) Prop"
    by (rule paper_back_truth_sentence)
  have typed: "has_stype paper_logical_type [] (pterm_to_paper (PObjTrue :: 'c pterm)) Prop"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have sig: "sterm_in_signature \<Sigma> (pterm_to_paper (PObjTrue :: 'c pterm))"
    using language unfolding sterm_in_language_def by (rule conjunct2)
  have neg_sig: "sterm_in_signature \<Sigma> (paper_not (pterm_to_paper (PObjTrue :: 'c pterm)))"
    using sig by (simp only: paper_not_signature)
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF paper_not_type[OF typed] neg_sig])
qed

theorem paper_target_consistent_to_source:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_term set"
  assumes sentences: "paper_sentence_set \<Sigma> S"
    and target_consistent: "pH_consistent \<Sigma> [] (image paper_to_pterm S)"
  shows "paper_global_consistent \<Sigma> G S"
proof (rule ccontr)
  assume inconsistent: "\<not> paper_global_consistent \<Sigma> G S"
  let ?C = "pterm_to_paper (PObjTrue :: 'c pterm)"
  have C: "sterm_in_language paper_logical_type \<Sigma> [] ?C Prop" by (rule paper_back_truth_sentence)
  have NC: "sterm_in_language paper_logical_type \<Sigma> [] (paper_not ?C) Prop"
    by (rule paper_back_truth_negation_sentence)
  have positive: "paper_global_derivable \<Sigma> G S ?C"
    by (rule paper_global_inconsistent_explosion[OF inconsistent paper_sentence_global_language[OF C]])
  have negative: "paper_global_derivable \<Sigma> G S (paper_not ?C)"
    by (rule paper_global_inconsistent_explosion[OF inconsistent paper_sentence_global_language[OF NC]])
  have target_positive: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm ?C)"
    by (rule paper_closed_set_preservation[OF sentences C positive])
  have target_negative_raw: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm (paper_not ?C))"
    by (rule paper_closed_set_preservation[OF sentences NC negative])
  have negation_conversion: "pbeta_eta_equiv_in_signature \<Sigma> [] Prop
    (paper_to_pterm (paper_not ?C)) (PNeg (paper_to_pterm ?C))"
    unfolding paper_not_def by (rule paper_not_application[OF C])
  have target_negative: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (PNeg (paper_to_pterm ?C))"
    by (rule source_pH_set_conversion_forward[OF negation_conversion target_negative_raw])
  have contradiction: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) PObjFalse"
    by (rule source_target_set_contradiction_false[OF target_positive target_negative])
  have forbidden: "\<not> pH_set_derivable \<Sigma> [] (image paper_to_pterm S) PObjFalse"
    using target_consistent unfolding pH_consistent_def .
  show False by (rule notE[OF forbidden contradiction])
qed

theorem paper_source_consistent_to_target:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_term set"
  assumes sentences: "paper_sentence_set \<Sigma> S" and rich: "sg_rich G"
    and source_consistent: "paper_global_consistent \<Sigma> G S"
  shows "pH_consistent \<Sigma> [] (image paper_to_pterm S)"
proof (unfold pH_consistent_def, rule notI)
  assume target_false: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (PObjFalse :: 'c pterm)"
  have target_true: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (PObjTrue :: 'c pterm)"
    by (rule pH_set_Theorem[OF pH_proves_PObjTrue])
  have positive: "paper_global_derivable \<Sigma> G S (pterm_to_paper (PObjTrue :: 'c pterm))"
    by (rule paper_target_set_preimage[OF sentences rich target_true])
  have negative_raw: "paper_global_derivable \<Sigma> G S (pterm_to_paper (PObjFalse :: 'c pterm))"
    by (rule paper_target_set_preimage[OF sentences rich target_false])
  have negative: "paper_global_derivable \<Sigma> G S (paper_not (pterm_to_paper (PObjTrue :: 'c pterm)))"
    using negative_raw by (simp only: PObjFalse_def pterm_to_paper.simps)
  show False by (rule paper_global_consistent_no_pair[OF source_consistent positive negative])
qed

theorem paper_closed_set_consistency_iff:
  assumes sentences: "paper_sentence_set \<Sigma> S" and rich: "sg_rich G"
  shows "paper_global_consistent \<Sigma> G S \<longleftrightarrow> pH_consistent \<Sigma> [] (image paper_to_pterm S)"
proof
  assume consistent: "paper_global_consistent \<Sigma> G S"
  show "pH_consistent \<Sigma> [] (image paper_to_pterm S)"
    by (rule paper_source_consistent_to_target[OF sentences rich consistent])
next
  assume consistent: "pH_consistent \<Sigma> [] (image paper_to_pterm S)"
  show "paper_global_consistent \<Sigma> G S"
    by (rule paper_target_consistent_to_source[OF sentences consistent])
qed

corollary paper_standard_closed_set_consistency_iff:
  assumes sentences: "paper_sentence_set \<Sigma> S"
  shows "paper_global_consistent \<Sigma> sg_standard_stock S \<longleftrightarrow>
    pH_consistent \<Sigma> [] (image paper_to_pterm S)"
  by (rule paper_closed_set_consistency_iff[OF sentences sg_standard_stock_rich])

end
