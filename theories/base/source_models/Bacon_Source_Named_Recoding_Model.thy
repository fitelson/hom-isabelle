theory Bacon_Source_Named_Recoding_Model
  imports Bacon_Source_Named_Recoding_Quantifiers
begin

section \<open>An injectively recoded named interpretation is a named model\<close>

text \<open>
  Every independent named model can be copied along an injection f.
  The new domains are f[Dσ]; every structural and primitive truth clause
  is preserved. Source: Bacon–Dorr Definition 3.1, pp.43–44, used in
  the change of carrier required by Theorem 3.2's countable refinement.

  This constructs a model; it does not assume one on the new carrier.
  Neither surjectivity onto that carrier nor disjointness of the original
  domains is needed. Type and signature syntax remain unchanged.
\<close>

context paper_named_bbk_model
begin

theorem named_recode_model:
  assumes injective: "inj f"
  shows "paper_named_bbk_model signature stock (named_image_domain f domain)
    (named_recode_denote f) (named_recode_valuation f)"
  apply unfold_locales
              apply (rule stock_rich)
             apply (rule named_image_domain_nonempty, rule domain_nonempty)
            apply (rule named_recode_denote_type[OF injective]; assumption)
           apply (rule named_recode_denote_var[OF injective]; assumption)
          apply (rule named_recode_denote_application[OF injective]; assumption)
         apply (rule named_recode_denote_locality[OF injective]; assumption)
        apply (rule named_recode_denote_conversion[OF injective]; assumption)
       apply (rule named_recode_neg_truth[OF injective]; assumption)
      apply (rule named_recode_conj_truth[OF injective]; assumption)
     apply (rule named_recode_disj_truth[OF injective]; assumption)
    apply (rule named_recode_forall_truth[OF injective]; assumption)
   apply (rule named_recode_exists_truth[OF injective]; assumption)
  apply (rule named_recode_identity_truth[OF injective]; assumption)
  done

end

end
