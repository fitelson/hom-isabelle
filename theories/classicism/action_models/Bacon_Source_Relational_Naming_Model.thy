theory Bacon_Source_Relational_Naming_Model
  imports Bacon_Source_Relational_Naming_Conversion Bacon_Source_Relational_Naming_Boolean_Truth
    Bacon_Source_Relational_Naming_Quantifier_Truth
begin

section \<open>The expanded naming interpretation satisfies every R BBK clause\<close>

text \<open>
  Every value a∈Dσ is named by the new constant Inr(a):σ. Finite
  charts define the expanded interpretation, whose structural and six
  logical clauses are proved separately and assembled here. The original
  domains, variable stock and valuation are unchanged.

  Source: the model M⁺ of p.51 n.73. The only supplied model is M:
  there is no expanded-model premise, countability assumption, global
  injection of values into variables, closed-denotability requirement,
  disjoint-domain condition, or Functionality assumption.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_model:
  "paper_R_bbk_model (paper_R_naming_signature signature domain) stock domain paper_R_naming_denote valuation"
  apply (rule paper_R_bbk_model.intro)
               apply (rule stock_rich)
              apply (rule domain_nonempty, assumption)
             apply (rule domain_empty, assumption)
            apply (rule paper_R_naming_denote_type; assumption)
           apply (rule paper_R_naming_denote_var; assumption)
          apply (rule paper_R_naming_denote_application_cong; assumption)
         apply (rule paper_R_naming_denote_locality; assumption)
        apply (rule paper_R_naming_denote_conversion; assumption)
       apply (rule paper_R_naming_neg_truth; assumption)
      apply (rule paper_R_naming_conj_truth; assumption)
     apply (rule paper_R_naming_disj_truth; assumption)
    apply (rule paper_R_naming_forall_truth; assumption)
   apply (rule paper_R_naming_exists_truth; assumption)
  apply (rule paper_R_naming_identity_truth; assumption)
  done

end

end
