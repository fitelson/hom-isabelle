theory Bacon_Source_ZF_Model_Eta_Conversion
  imports Bacon_Source_ZF_Model_Evaluation_Naturality
    Bacon_Source_ZF_Evaluation_Locality Bacon_Source_ZF_Exponential_Identity_Application
begin

section \<open>η compares all outgoing arrows and target arguments\<close>

text \<open>
  For n∉FV(F), ⟦λn.Fn⟧ᵍh=⟦F⟧ᵍh in every action model.
  Source: Proposition C.5, p.71. Naturality supplies F's value
  after each outgoing arrow. Freshness removes the binder update,
  and precomposition recovers F⟨i,a⟩ for every a at target(i).
  Equality of the complete function graphs finishes the proof.
  No surjectivity of transport and no BBK-model premise is used.
\<close>

lemma paper_ZF_action_model_eta_body:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G F (Arr (G n) \<tau>)"
    and fresh: "n \<notin> named_fv F"
    and first: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g F"
    and evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f"
    and pair: "Elem (Opair i a) (paper_ZF_pair_code Ar source target (D (G n)) (target h))"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F (NVar n))
    (compose i h) ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) = Some (app f (Opair i a))"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have second: "i \<in> explode Ar" and meeting: "target h = source i" and am: "a \<in> explode (D (G n) (target i))"
    using pair by (simp only: paper_ZF_pair_code_member; blast)+
  have rt: "paper_R_type (Arr (G n) \<tau>)" by (rule paper_R_language_result_type[OF language])
  have fm: "f \<in> explode (D (Arr (G n) \<tau>) (target h))"
    by (rule paper_ZF_action_model_eval_member[OF model language first origin typed adequate evaluated])
  have fs: "f \<in> explode (D (Arr (G n) \<tau>) (source i))" using fm by (simp only: meeting)
  have action: "paper_action Obj (explode Ar) source target compose identity
    (\<lambda>W. explode (D (Arr (G n) \<tau>) W)) (T (Arr (G n) \<tau>))"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  have moved: "T (Arr (G n) \<tau>) i f \<in> explode (D (Arr (G n) \<tau>) (target i))"
    by (rule paper_action.transport_type[OF action second fs])
  have natural: "paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
    (paper_ZF_action_transport_assignment G T i g) = Some (T (Arr (G n) \<tau>) i f)"
    by (rule paper_ZF_action_model_eval_naturality[OF model language first origin second meeting typed adequate evaluated])
  have local: "paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
      ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) =
    paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
      (paper_ZF_action_transport_assignment G T i g)"
    by (rule paper_ZF_action_eval_locality; use fresh in auto)
  have head_eval: "paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
    ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) = Some (T (Arr (G n) \<tau>) i f)"
    by (rule trans[OF local natural])
  have arg_eval: "paper_ZF_action_eval Ar source target compose identity D T I G (NVar n) (compose i h)
    ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) = Some a" by simp
  have object: "target i \<in> Obj" by (rule C.target_object[OF second])
  have fg: "isFun (T (Arr (G n) \<tau>) i f)"
    and fp: "Elem (Opair (identity (target i)) a) (Domain (T (Arr (G n) \<tau>) i f))"
    by (rule paper_ZF_premodel_application_graph[OF premodel object rt moved am])+
  have ct: "target (compose i h) = target i" by (rule C.compose_target[OF first second meeting])
  have cp: "Elem (Opair (identity (target (compose i h))) a) (Domain (T (Arr (G n) \<tau>) i f))"
    by (simp only: ct; rule fp)
  have applied: "app (T (Arr (G n) \<tau>) i f) (Opair (identity (target i)) a) = app f (Opair i a)"
    by (rule paper_ZF_premodel_transport_identity_application[OF premodel rt second fs am])
  show ?thesis using paper_ZF_action_eval_application[OF head_eval arg_eval fg cp]
    by (simp only: ct applied)
qed

theorem paper_ZF_action_model_eta:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G F (Arr (G n) \<tau>)" and fresh: "n \<notin> named_fv F"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g F"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n (NApp F (NVar n))) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G F h g"
proof -
  obtain f where fe: "paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f"
    and fm: "f \<in> explode (D (Arr (G n) \<tau>) (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model language arrow origin typed adequate])
  let ?P = "paper_ZF_pair_code Ar source target (D (G n)) (target h)"
  let ?B = "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F (NVar n))"
  let ?V = "paper_ZF_action_abstraction_body compose T G n ?B h g"
  have bodies: "?V z = Some (app f z)" if member: "Elem z ?P" for z
  proof -
    obtain i a where shape: "z = Opair i a" by (rule paper_ZF_pair_codeE[OF member]; rule that; assumption)
    have pair: "Elem (Opair i a) ?P" using member by (simp only: shape)
    show ?thesis by (simp only: shape paper_ZF_action_abstraction_body_pair;
      rule paper_ZF_action_model_eta_body[OF model language fresh arrow origin typed adequate fe pair])
  qed
  have defined: "?V z \<noteq> None" if "z \<in> explode ?P" for z
    using bodies[of z] that by (simp only: explode_Elem; simp)
  have abstraction: "paper_ZF_action_abstract Ar source target compose D T G n ?B h g =
    Some (Lambda ?P (\<lambda>z. the (?V z)))" by (rule paper_ZF_action_abstract_defined[OF defined])
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have rt: "paper_R_type (Arr (G n) \<tau>)" by (rule paper_R_language_result_type[OF language])
  have exponential: "f \<in> explode (paper_ZF_exponential_code Ar source target compose (D (G n)) (T (G n)) (D \<tau>) (T \<tau>) (target h))"
    by (rule paper_ZF_premodel_function_in_exponential[OF premodel object rt fm])
  have graph: "f = Lambda ?P (app f)"
    by (rule paper_ZF_Pi_as_application_graph[OF paper_ZF_exponential_code_graph[OF exponential]])
  have same: "Lambda ?P (\<lambda>z. the (?V z)) = Lambda ?P (app f)"
    by (simp only: Lambda_ext; use bodies in auto)
  show ?thesis by (simp only: paper_ZF_action_eval.simps abstraction same graph[symmetric] fe)
qed

end
