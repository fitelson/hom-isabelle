theory Bacon_Source_Named_Consistent_Negation
  imports Bacon_Source_Named_Consistency_Correspondence Bacon_Source_Named_Sentence_Sets
    Bacon_Source_Named_Logical_Language Bacon_Source_Consistency_Correspondence
begin

section \<open>Adjoining the negation of a nonderivable named sentence\<close>

text \<open>
  If S ⊬H A for a sentence set S and sentence A, then S ∪ {¬A}
  is consistent. Source: the refutation construction underlying
  Bacon–Dorr Theorem 3.2, pp.44–45, and its Figure 2 calculus.

  Representation. Transfer closed consequence to the parametric calculus,
  use its syntactic refutation lemma, and transfer consistency back.
  Literal source negation translates to a β-redex, not definitionally to
  PNeg. The auxiliary deduction/MP argument below accounts for that
  conversion when an assumption is inserted. No model is used, and
  consistency still excludes open contradictory witnesses.
\<close>

lemma paper_named_sentence_set_insert_not:
  assumes sentences: "paper_named_sentence_set \<Sigma> G S"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop" and closed: "named_fv A = {}"
  shows "paper_named_sentence_set \<Sigma> G (insert (named_paper_not A) S)"
proof -
  have neg_language: "named_in_language paper_logical_type \<Sigma> G (named_paper_not A) Prop"
    by (rule named_paper_not_language[OF language])
  have neg_closed: "named_fv (named_paper_not A) = {}" by (simp only: named_paper_primitive_fv(1) closed)
  show ?thesis using sentences neg_language neg_closed by (simp add: paper_named_sentence_set_def)
qed

lemma named_target_consistent_conversion_insert:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and consistent: "pH_consistent \<Sigma> \<Gamma> (insert N T)"
  shows "pH_consistent \<Sigma> \<Gamma> (insert M T)"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable \<Sigma> \<Gamma> (insert M T) PObjFalse"
  have ml: "pterm_in_language \<Sigma> \<Gamma> M Prop" by (rule source_conversion_left_language[OF conversion])
  have nl: "pterm_in_language \<Sigma> \<Gamma> N Prop" by (rule source_conversion_right_language[OF conversion])
  note md = ml[unfolded pterm_in_language_def]
  note nd = nl[unfolded pterm_in_language_def]
  have implication: "pH_set_derivable \<Sigma> \<Gamma> T (PImp M PObjFalse)"
    by (rule pH_set_deduction[OF conjunct1[OF md] conjunct2[OF md] bad])
  have weakened: "pH_set_derivable \<Sigma> \<Gamma> (insert N T) (PImp M PObjFalse)"
    by (rule pH_set_mono[OF implication]) auto
  have assumed_N: "pH_set_derivable \<Sigma> \<Gamma> (insert N T) N"
    by (rule pH_set_Assumption[OF _ conjunct1[OF nd] conjunct2[OF nd]]) simp
  have derived_M: "pH_set_derivable \<Sigma> \<Gamma> (insert N T) M"
    by (rule source_pH_set_conversion_backward[OF conversion assumed_N])
  have contradiction: "pH_set_derivable \<Sigma> \<Gamma> (insert N T) PObjFalse"
    by (rule pH_set_MP[OF derived_M weakened])
  show False using consistent contradiction unfolding pH_consistent_def by blast
qed

theorem paper_named_consistent_insert_not:
  assumes sentences: "paper_named_sentence_set \<Sigma> G S"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and closed: "named_fv A = {}" and rich: "sg_rich G"
    and not_derivable: "\<not> paper_named_derivable \<Sigma> G S A"
  shows "paper_named_consistent \<Sigma> G (insert (named_paper_not A) S)"
proof -
  let ?enc = "named_to_source G []"
  let ?T = "paper_to_pterm ` (?enc ` S)"
  let ?Q = "paper_to_pterm (?enc A)"
  have source_sentences: "paper_sentence_set \<Sigma> (?enc ` S)"
    by (rule paper_named_sentence_set_encoding[OF sentences])
  have source_A: "sterm_in_language paper_logical_type \<Sigma> [] (?enc A) Prop"
    by (rule named_to_source_closed_language[OF language closed])
  have target_A: "pterm_in_language \<Sigma> [] ?Q Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff source_A])
  note qd = target_A[unfolded pterm_in_language_def]
  have target_not_derivable: "\<not> pH_set_derivable \<Sigma> [] ?T ?Q"
  proof
    assume target: "pH_set_derivable \<Sigma> [] ?T ?Q"
    have source: "paper_global_derivable \<Sigma> G (?enc ` S) (?enc A)"
      by (rule iffD2[OF paper_closed_set_derivable_iff[OF source_sentences source_A rich] target])
    have native: "paper_named_derivable \<Sigma> G S A"
      by (rule paper_named_derivable_decoding[OF source rich])
    show False by (rule notE[OF not_derivable native])
  qed
  have primitive_consistent: "pH_consistent \<Sigma> [] (insert (PNeg ?Q) ?T)"
    by (rule pH_consistent_neg_of_not_set_derivable[OF conjunct1[OF qd] conjunct2[OF qd] target_not_derivable])
  have neg_conversion: "pbeta_eta_equiv_in_signature \<Sigma> [] Prop
    (paper_to_pterm (paper_not (?enc A))) (PNeg ?Q)"
    unfolding paper_not_def by (rule paper_not_application[OF source_A])
  have literal_consistent: "pH_consistent \<Sigma> [] (insert (paper_to_pterm (paper_not (?enc A))) ?T)"
    by (rule named_target_consistent_conversion_insert[OF neg_conversion primitive_consistent])
  have target_insert: "pH_consistent \<Sigma> [] (paper_to_pterm ` (?enc ` insert (named_paper_not A) S))"
    using literal_consistent by (simp only: image_insert named_paper_not_encoding)
  have named_insert: "paper_named_sentence_set \<Sigma> G (insert (named_paper_not A) S)"
    by (rule paper_named_sentence_set_insert_not[OF sentences language closed])
  have source_insert: "paper_sentence_set \<Sigma> (?enc ` insert (named_paper_not A) S)"
    by (rule paper_named_sentence_set_encoding[OF named_insert])
  have source_consistent: "paper_global_consistent \<Sigma> G (?enc ` insert (named_paper_not A) S)"
    by (rule paper_target_consistent_to_source[OF source_insert target_insert])
  show ?thesis by (rule iffD2[OF paper_named_consistency_iff[OF rich] source_consistent])
qed

end
