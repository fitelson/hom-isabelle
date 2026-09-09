theory Bacon_Source_BBK_Pullback_Model
  imports Bacon_Source_BBK_Pullback_Structure Bacon_Source_BBK_Pullback_Truth
begin

section \<open>The target interpretation supplies every source finite-frame clause\<close>

text \<open>
  For every target BBK model, ⟦A⟧S,g = ⟦tr(A)⟧T,g defines a model
  of the independently declared first-class finite-frame interface.
  Domains and valuation are unchanged. The structural and logical clauses
  have separate proofs, assembled below without additional assumptions.

  This is a one-way model construction for the represented interfaces.
  It does not identify arbitrary target denotations with their reverse
  round trips, and does not yet complete the named-variable correspondence
  required for a literal source-model equivalence.
\<close>

context pbbk_model
begin

theorem paper_target_is_db_model:
  "paper_db_bbk_model signature domain paper_target_denote valuation"
  apply unfold_locales
              apply (rule paper_target_domain_nonempty)
             apply (rule paper_target_denote_type; assumption)
            apply (rule paper_target_denote_var; assumption)
           apply (rule paper_target_denote_application_cong; assumption)
          apply (rule paper_target_denote_locality; assumption)
         apply (rule paper_target_denote_beta_eta; assumption)
        apply (unfold paper_target_denote_def, rule paper_pullback_neg; assumption)
       apply (unfold paper_target_denote_def, rule paper_pullback_conj; assumption)
      apply (unfold paper_target_denote_def, rule paper_pullback_disj; assumption)
     apply (unfold paper_target_denote_def, rule paper_pullback_forall; assumption)
    apply (unfold paper_target_denote_def, rule paper_pullback_exists; assumption)
   apply (unfold paper_target_denote_def, rule paper_pullback_identity; assumption)
  apply (rule paper_target_denote_rename; assumption)
  done

end

theorem pbbk_to_paper_db_model:
  assumes model: "pbbk_model \<Sigma> D J V"
  shows "paper_db_bbk_model \<Sigma> D (\<lambda>g A. J g (paper_to_pterm A)) V"
proof -
  interpret target: pbbk_model \<Sigma> D J V by (rule model)
  show ?thesis using target.paper_target_is_db_model
    unfolding target.paper_target_denote_def .
qed

end
