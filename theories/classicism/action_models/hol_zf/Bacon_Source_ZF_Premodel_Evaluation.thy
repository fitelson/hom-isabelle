theory Bacon_Source_ZF_Premodel_Evaluation
  imports Bacon_Source_ZF_Partial_Interpretation Bacon_Source_ZF_Premodel_Application
begin

section \<open>Variables, constants and application in an arbitrary premodel\<close>

text \<open>
  The first three elementary domain checks of Definition 3.19
  follow from a typed adequate assignment and the premodel's
  own action/domain clauses. No action-model totality assumption
  is used. Application requires defined, correctly typed values
  for both subterms, and we derive its graph-definedness.

  These results do not settle the logical-constant or abstraction
  cases. In particular, the interpreted abstraction graph must
  not be presumed to belong to the selected function stock.
\<close>

lemma paper_ZF_action_eval_variable_typed:
  assumes typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate: "named_adequate g (NVar n)"
  shows "\<exists>v. paper_ZF_action_eval Ar source target compose identity D T I G (NVar n) h g = Some v \<and>
    v \<in> explode (D (G n) (target h))"
proof -
  have defined: "n \<in> dom g" using adequate by (simp add: named_adequate_def)
  obtain v where assigned: "g n = Some v" using defined by blast
  have member: "v \<in> explode (D (G n) (target h))"
    by (rule paper_ZF_action_env_value[OF typed assigned])
  show ?thesis by (rule exI[where x=v], simp only: paper_ZF_action_eval.simps assigned;
    rule conjI[OF refl member])
qed

lemma paper_ZF_action_eval_constant_typed:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and rt: "paper_R_type \<rho>" and declared: "c \<in> \<Sigma> \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NConst c \<rho>) h g =
      Some (T \<rho> h (I \<rho> c)) \<and>
    T \<rho> h (I \<rho> c) \<in> explode (D \<rho> (target h))"
proof -
  have action: "paper_action Obj (explode Ar) source target compose identity
      (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  interpret Act: paper_action Obj "explode Ar" source target compose identity "\<lambda>W. explode (D \<rho> W)" "T \<rho>"
    by (rule action)
  have root_member: "I \<rho> c \<in> explode (D \<rho> root)"
    using premodel rt declared unfolding paper_ZF_action_premodel_def by blast
  have source_member: "I \<rho> c \<in> explode (D \<rho> (source h))"
    by (simp only: origin; rule root_member)
  have member: "T \<rho> h (I \<rho> c) \<in> explode (D \<rho> (target h))"
    by (rule Act.transport_type[OF arrow source_member])
  show ?thesis by (simp only: paper_ZF_action_eval.simps; rule conjI[OF refl member])
qed

lemma paper_ZF_action_eval_application_typed:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and object: "target h \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and head: "paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f"
    and head_type: "f \<in> explode (D (Arr \<sigma> \<tau>) (target h))"
    and argument: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some b"
    and argument_type: "b \<in> explode (D \<sigma> (target h))"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g =
      Some (app f (Opair (identity (target h)) b)) \<and>
    app f (Opair (identity (target h)) b) \<in> explode (D \<tau> (target h))"
proof -
  have info: "isFun f \<and> Elem (Opair (identity (target h)) b) (Domain f) \<and>
      app f (Opair (identity (target h)) b) \<in> explode (D \<tau> (target h))"
    by (rule paper_ZF_premodel_application_info[OF premodel object rt head_type argument_type])
  show ?thesis
  proof (rule conjI)
    show "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g =
        Some (app f (Opair (identity (target h)) b))"
      by (rule paper_ZF_action_eval_application[
        OF head argument conjunct1[OF info] conjunct1[OF conjunct2[OF info]]])
    show "app f (Opair (identity (target h)) b) \<in> explode (D \<tau> (target h))"
      by (rule conjunct2[OF conjunct2[OF info]])
  qed
qed

end
