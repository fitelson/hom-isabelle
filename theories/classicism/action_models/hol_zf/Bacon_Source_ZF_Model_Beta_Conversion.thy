theory Bacon_Source_ZF_Model_Beta_Conversion
  imports Bacon_Source_ZF_Model_Substitution
begin

section \<open>C.4 follows from actual graph application and C.3\<close>

text \<open>
  ⟦(λn.B)C⟧ᵍh = ⟦B[C/n]⟧ᵍh.
  Source: Proposition C.4, p.71. Application evaluates the abstraction
  graph at ⟨1target(h),c⟩. Its defining body is evaluated under the
  n-update, because identity transport leaves the partial assignment
  unchanged. The literal substitution theorem C.3 completes the proof.

  The WHOLE redex is required to belong to R, and C must be free for n
  in B. No β semantic clause, BBK-model premise, or interpretation
  totality outside the independent action-model criterion is assumed.
\<close>

theorem paper_ZF_action_model_beta:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G (NApp (NLam n B) C) \<rho>"
    and free_for: "named_free_for C n B"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate: "named_adequate g (NApp (NLam n B) C)"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NApp (NLam n B) C) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G (named_subst n C B) h g"
proof -
  have redex_type: "paper_R_has_type G (NApp (NLam n B) C) \<rho>"
    and redex_names: "named_in_signature \<Sigma> (NApp (NLam n B) C)"
    using language unfolding paper_R_in_language_def by blast+
  obtain \<sigma> where head_type: "paper_R_has_type G (NLam n B) (Arr \<sigma> \<rho>)"
    and argument_type: "paper_R_has_type G C \<sigma>"
    by (rule paper_R_app_type_obtain[OF redex_type]; rule that; assumption)
  obtain \<tau> where shape: "Arr \<sigma> \<rho> = Arr (G n) \<tau>" and body_type: "paper_R_has_type G B \<tau>"
    by (rule paper_R_lam_type_obtain[OF head_type]; rule that; assumption)
  have domain_type: "\<sigma> = G n" and result_type: "\<tau> = \<rho>" using shape by auto
  have body: "paper_R_in_language \<Sigma> G B \<rho>"
    using body_type redex_names by (auto simp: paper_R_in_language_def result_type)
  have head: "paper_R_in_language \<Sigma> G (NLam n B) (Arr (G n) \<rho>)"
    using head_type redex_names by (auto simp: paper_R_in_language_def domain_type)
  have payload: "paper_R_in_language \<Sigma> G C (G n)"
    using argument_type redex_names by (auto simp: paper_R_in_language_def domain_type)
  have head_adequate: "named_adequate g (NLam n B)" and payload_adequate: "named_adequate g C"
    using adequate by (auto simp: named_adequate_def)
  obtain f where fe: "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h g = Some f"
    and fm: "f \<in> explode (D (Arr (G n) \<rho>) (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model head arrow origin typed head_adequate])
  obtain c where ce: "paper_ZF_action_eval Ar source target compose identity D T I G C h g = Some c"
    and cm: "c \<in> explode (D (G n) (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model payload arrow origin typed payload_adequate])
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Cat: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have object: "target h \<in> Obj" by (rule Cat.target_object[OF arrow])
  have rt: "paper_R_type (Arr (G n) \<rho>)" by (rule paper_R_language_result_type[OF head])
  have graph: "isFun f" and in_domain: "Elem (Opair (identity (target h)) c) (Domain f)"
    by (rule paper_ZF_premodel_application_graph[OF premodel object rt fm cm])+
  have application:
    "paper_ZF_action_eval Ar source target compose identity D T I G (NApp (NLam n B) C) h g =
      Some (app f (Opair (identity (target h)) c))"
    by (rule paper_ZF_action_eval_application[OF fe ce graph in_domain])
  have pair: "Elem (Opair (identity (target h)) c)
      (paper_ZF_pair_code Ar source target (D (G n)) (target h))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object cm])
  have at_identity:
    "Some (app f (Opair (identity (target h)) c)) =
      paper_ZF_action_eval Ar source target compose identity D T I G B (compose (identity (target h)) h)
        ((paper_ZF_action_transport_assignment G T (identity (target h)) g)(n := Some c))"
    by (rule paper_ZF_action_eval_abstraction_apply[OF fe pair])
  have assignment_identity: "paper_ZF_action_transport_assignment G T (identity (target h)) g = g"
    by (rule paper_ZF_premodel_assignment_transport_identity[OF premodel object typed])
  have beta_update:
    "paper_ZF_action_eval Ar source target compose identity D T I G (NApp (NLam n B) C) h g =
      paper_ZF_action_eval Ar source target compose identity D T I G B h (g(n := Some c))"
    using trans[OF application at_identity]
    by (simp only: Cat.identity_left[OF arrow] assignment_identity)
  have substitution:
    "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst n C B) h g =
      paper_ZF_action_eval Ar source target compose identity D T I G B h (g(n := Some c))"
    by (rule paper_ZF_action_model_substitution[
      OF model body payload free_for arrow origin typed head_adequate payload_adequate ce])
  show ?thesis by (rule trans[OF beta_update substitution[symmetric]])
qed

end
