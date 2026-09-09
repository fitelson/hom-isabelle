theory Bacon_Source_Relational_Recoding_Model
  imports Bacon_Source_Relational_Recoding_Quantifiers
begin

section \<open>The recoded structure satisfies every independent R-BBK clause\<close>

text \<open>
  An injection f on ⋃σDσ gives an R-BBK model on the image domains.
  We assemble the separately verified structural and six primitive truth
  clauses. The language, variable stock and raw R conversion relation
  are unchanged. No global carrier injection, target surjectivity,
  Functionality or disjoint-domain premise is added.

  Source: Definition 3.1 and the carrier change in Theorem 3.2,
  pp.43–45. The supplied old model is the only semantic premise;
  the target model is proved, not assumed.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_recode_model:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
  shows "paper_R_bbk_model signature stock (paper_R_recode_domain f domain)
    (paper_R_recode_denote f) (paper_R_recode_valuation f)"
  apply (rule paper_R_bbk_model.intro)
               apply (rule stock_rich)
              apply (rule iffD2[OF paper_R_recode_domain_nonempty], rule domain_nonempty, assumption)
             apply (rule paper_R_recode_domain_empty, rule domain_empty, assumption)
            apply (rule paper_R_recode_denote_type[OF injective]; assumption)
           apply (rule paper_R_recode_denote_var[OF injective]; assumption)
          apply (rule paper_R_recode_denote_application[OF injective]; assumption)
         apply (rule paper_R_recode_denote_locality[OF injective]; assumption)
        apply (rule paper_R_recode_denote_conversion[OF injective]; assumption)
       apply (rule paper_R_recode_neg_truth[OF injective]; assumption)
      apply (rule paper_R_recode_conj_truth[OF injective]; assumption)
     apply (rule paper_R_recode_disj_truth[OF injective]; assumption)
    apply (rule paper_R_recode_forall_truth[OF injective]; assumption)
   apply (rule paper_R_recode_exists_truth[OF injective]; assumption)
  apply (rule paper_R_recode_identity_truth[OF injective]; assumption)
  done

end

end
