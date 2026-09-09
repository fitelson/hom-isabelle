theory Bacon_Source_BBK_Reverse_Model
  imports Bacon_Source_BBK_Reverse_Structure Bacon_Source_BBK_Reverse_Booleans
    Bacon_Source_BBK_Reverse_Quantifiers
begin

section \<open>Every weak source structure supplies a target model\<close>

text \<open>
  Given the independently specified source structure S, define
  ⟦M⟧T,g := ⟦back(M)⟧S,g. The structural and truth-clause proofs
  establish a target BBK model on the same domains and valuation.
  Source role: the primitive-vocabulary representation bridge for
  Bacon–Dorr Definition 3.1 and Theorem 3.2, pp.43–45.

  The source renaming property is derived, not added as a premise. The
  target implication clause uses the source's literal λ-definition.
  This is a finite-frame interpretation construction; named-variable
  correspondence remains separate. Only the source-side denotation
  round trip is asserted, not an isomorphism recovering arbitrary original
  target denotations containing primitive implication.
\<close>

context paper_db_bbk_structure
begin

theorem paper_reverse_is_pbbk_model:
  "pbbk_model signature domain paper_reverse_denote valuation"
  apply unfold_locales
               apply (rule paper_reverse_domain_nonempty)
              apply (rule paper_reverse_denote_type; assumption)
             apply (rule paper_reverse_denote_var; assumption)
            apply (rule paper_reverse_denote_application_cong; assumption)
           apply (rule paper_reverse_denote_locality; assumption)
          apply (rule paper_reverse_denote_rename; assumption)
         apply (rule paper_reverse_denote_beta_eta; assumption)
        apply (unfold paper_reverse_denote_def, rule paper_reverse_neg_truth; auto simp: pterm_in_language_def)
       apply (unfold paper_reverse_denote_def, rule paper_reverse_conj_truth; auto simp: pterm_in_language_def)
      apply (unfold paper_reverse_denote_def, rule paper_reverse_disj_truth; auto simp: pterm_in_language_def)
     apply (unfold paper_reverse_denote_def, rule paper_reverse_imp_truth; auto simp: pterm_in_language_def)
    apply (unfold paper_reverse_denote_def, rule paper_db_reverse_forall; auto simp: pterm_in_language_def)
   apply (unfold paper_reverse_denote_def, rule paper_db_reverse_exists; auto simp: pterm_in_language_def)
  apply (unfold paper_reverse_denote_def, rule paper_reverse_identity_truth; auto simp: pterm_in_language_def)
  done

end

theorem paper_db_to_pbbk_model:
  assumes source_model: "paper_db_bbk_structure \<Sigma> D J V"
  shows "pbbk_model \<Sigma> D (\<lambda>g M. J g (pterm_to_paper M)) V"
proof -
  interpret Source: paper_db_bbk_structure \<Sigma> D J V by (rule source_model)
  show ?thesis using Source.paper_reverse_is_pbbk_model
    unfolding Source.paper_reverse_denote_def .
qed

end
