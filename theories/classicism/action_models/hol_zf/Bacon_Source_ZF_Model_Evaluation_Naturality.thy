theory Bacon_Source_ZF_Model_Evaluation_Naturality
  imports Bacon_Source_ZF_Model_Logical_Naturality Bacon_Source_ZF_Abstraction_Naturality
begin

section \<open>Model totality supplies typed values at the actual root input\<close>

lemma paper_ZF_action_model_eval_value:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g B"
  obtains v where "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some v"
    "v \<in> explode (D \<rho> (target h))"
  using model language arrow origin typed adequate that unfolding paper_ZF_action_model_def by blast

lemma paper_ZF_action_model_eval_member:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g B"
    and evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some v"
  shows "v \<in> explode (D \<rho> (target h))"
proof -
  obtain w where returned: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some w"
    and member: "w \<in> explode (D \<rho> (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model language arrow origin typed adequate])
  have same: "w = v" using returned evaluated by simp
  show ?thesis using member by (simp only: same)
qed

section \<open>The application step uses typed subterm values, not mere definedness\<close>

lemma paper_ZF_action_model_eval_App_naturality:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
    and first: "h \<in> explode Ar" and origin: "source h = root"
    and second: "i \<in> explode Ar" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g (NApp F B)"
    and evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g = Some a"
    and head_IH: "\<And>f. paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
        (paper_ZF_action_transport_assignment G T i g) = Some (T (Arr \<sigma> \<tau>) i f)"
    and argument_IH: "\<And>b. paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some b \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
        (paper_ZF_action_transport_assignment G T i g) = Some (T \<sigma> i b)"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) (compose i h)
    (paper_ZF_action_transport_assignment G T i g) = Some (T \<tau> i a)"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have fa: "named_adequate g F" and ba: "named_adequate g B" using adequate by (auto simp: named_adequate_def)
  obtain f where fe: "paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f"
    and fm: "f \<in> explode (D (Arr \<sigma> \<tau>) (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model fl first origin typed fa])
  obtain b where be: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some b"
    and bm: "b \<in> explode (D \<sigma> (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model bl first origin typed ba])
  have rt: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
  have object: "target h \<in> Obj" by (rule C.target_object[OF first])
  have fg: "isFun f" and fp: "Elem (Opair (identity (target h)) b) (Domain f)"
    by (rule paper_ZF_premodel_application_graph[OF premodel object rt fm bm])+
  have old_eval: "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g =
    Some (app f (Opair (identity (target h)) b))"
    by (rule paper_ZF_action_eval_application[OF fe be fg fp])
  have old_value: "a = app f (Opair (identity (target h)) b)" using evaluated old_eval by simp
  have f_source: "f \<in> explode (D (Arr \<sigma> \<tau>) (source i))" using fm by (simp only: meeting)
  have b_source: "b \<in> explode (D \<sigma> (source i))" using bm by (simp only: meeting)
  have function_action: "paper_action Obj (explode Ar) source target compose identity
    (\<lambda>W. explode (D (Arr \<sigma> \<tau>) W)) (T (Arr \<sigma> \<tau>))"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  have argument_action: "paper_action Obj (explode Ar) source target compose identity
    (\<lambda>W. explode (D \<sigma> W)) (T \<sigma>)"
    using premodel sr unfolding paper_ZF_action_premodel_def by blast
  have moved_f: "T (Arr \<sigma> \<tau>) i f \<in> explode (D (Arr \<sigma> \<tau>) (target i))"
    by (rule paper_action.transport_type[OF function_action second f_source])
  have moved_b: "T \<sigma> i b \<in> explode (D \<sigma> (target i))"
    by (rule paper_action.transport_type[OF argument_action second b_source])
  have target_object: "target i \<in> Obj" by (rule C.target_object[OF second])
  have new_graph: "isFun (T (Arr \<sigma> \<tau>) i f)"
    and new_pair: "Elem (Opair (identity (target i)) (T \<sigma> i b)) (Domain (T (Arr \<sigma> \<tau>) i f))"
    by (rule paper_ZF_premodel_application_graph[OF premodel target_object rt moved_f moved_b])+
  have composite_target: "target (compose i h) = target i" by (rule C.compose_target[OF first second meeting])
  have eval_f: "paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
    (paper_ZF_action_transport_assignment G T i g) = Some (T (Arr \<sigma> \<tau>) i f)" by (rule head_IH[OF fe])
  have eval_b: "paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
    (paper_ZF_action_transport_assignment G T i g) = Some (T \<sigma> i b)" by (rule argument_IH[OF be])
  have natural: "T \<tau> i a =
    app (T (Arr \<sigma> \<tau>) i f) (Opair (identity (target i)) (T \<sigma> i b))"
    using paper_ZF_premodel_application_naturality[OF premodel rt second f_source b_source]
    by (simp only: old_value meeting)
  have composite_pair: "Elem (Opair (identity (target (compose i h))) (T \<sigma> i b)) (Domain (T (Arr \<sigma> \<tau>) i f))"
    by (simp only: composite_target; rule new_pair)
  show ?thesis
    using paper_ZF_action_eval_application[OF eval_f eval_b new_graph composite_pair]
    by (simp only: composite_target natural)
qed

section \<open>C.1 for the generic independent action model\<close>

text \<open>
  If ⟦B⟧ᵍh=a in an ACTION MODEL and i composes after h, then
  ⟦B⟧ⁱ·ᵍi∘h=iρ(a). Source: Proposition C.1, p.70.
  The independent R typing induction retains the signature guard and
  generalizes h, i, g and a. Model totality supplies selected-fiber
  membership for the strict application subterms and the abstraction.
  This is deliberately not the unqualified premodel assertion.

  No constructed representation, BBK-model predicate or C theoremhood
  is used. The logical case uses the independently proved logical
  naturality theorem with its membership guard discharged by the model.
\<close>

lemma paper_ZF_action_model_typed_eval_naturality:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and term_type: "paper_R_has_type G B \<rho>" and names: "named_in_signature \<Sigma> B"
    and first: "h \<in> explode Ar" and origin: "source h = root"
    and second: "i \<in> explode Ar" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g B"
    and evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some a"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
    (paper_ZF_action_transport_assignment G T i g) = Some (T \<rho> i a)"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  show ?thesis using term_type names first origin second meeting typed adequate evaluated
  proof (induction arbitrary: h i g a rule: paper_R_has_type.induct)
    case (Var n)
    have assigned: "g n = Some a" using Var.prems(8) by (simp only: paper_ZF_action_eval.simps)
    show ?case by (simp only: paper_ZF_action_eval.simps paper_ZF_action_transport_assignment_def
      paper_hom_assignment_def assigned option.map)
  next
    case (Const \<sigma> c)
    have declared: "c \<in> \<Sigma> \<sigma>" using Const.prems(1) by simp
    have initial: "I \<sigma> c \<in> explode (D \<sigma> root)"
      using premodel Const.hyps declared unfolding paper_ZF_action_premodel_def by blast
    have source_initial: "I \<sigma> c \<in> explode (D \<sigma> (source h))" by (simp only: Const.prems(3); rule initial)
    have action: "paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D \<sigma> W)) (T \<sigma>)"
      using premodel Const.hyps unfolding paper_ZF_action_premodel_def by blast
    have composition: "T \<sigma> (compose i h) (I \<sigma> c) = T \<sigma> i (T \<sigma> h (I \<sigma> c))"
      by (rule paper_action.transport_compose[OF action Const.prems(2,4,5) source_initial])
    have old_value: "a = T \<sigma> h (I \<sigma> c)" using Const.prems(8) by (simp only: paper_ZF_action_eval.simps option.inject)
    show ?case by (simp only: paper_ZF_action_eval.simps composition old_value)
  next
    case (Logical l)
    have old_value: "a = paper_ZF_logical_value Ar source target compose identity D T (target h) l"
      using Logical.prems(8) by (simp only: paper_ZF_action_eval.simps option.inject)
    have natural: "T (paper_logical_type l) i (paper_ZF_logical_value Ar source target compose identity D T (target h) l) =
      paper_ZF_logical_value Ar source target compose identity D T (target i) l"
      by (rule paper_ZF_action_model_logical_naturality[OF model Logical.hyps Logical.prems(2,3,4,5,6)])
    show ?case by (simp only: paper_ZF_action_eval.simps C.compose_target[OF Logical.prems(2,4,5)] old_value natural)
  next
    case (App F \<sigma> \<tau> B)
    have fn: "named_in_signature \<Sigma> F" and bn: "named_in_signature \<Sigma> B" using App.prems(1) by simp_all
    have fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
      unfolding paper_R_in_language_def by (rule conjI[OF App.hyps(1) fn])
    have bl: "paper_R_in_language \<Sigma> G B \<sigma>"
      unfolding paper_R_in_language_def by (rule conjI[OF App.hyps(2) bn])
    have fa: "named_adequate g F" and ba: "named_adequate g B" using App.prems(7) by (auto simp: named_adequate_def)
    show ?case
    proof (rule paper_ZF_action_model_eval_App_naturality[OF model fl bl App.prems(2,3,4,5,6,7,8)])
      fix f
      assume fe: "paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f"
      show "paper_ZF_action_eval Ar source target compose identity D T I G F (compose i h)
        (paper_ZF_action_transport_assignment G T i g) = Some (T (Arr \<sigma> \<tau>) i f)"
        by (rule App.IH(1)[where h=h and i=i and g=g and a=f, OF fn App.prems(2,3,4,5,6) fa fe])
    next
      fix b
      assume be: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some b"
      show "paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
        (paper_ZF_action_transport_assignment G T i g) = Some (T \<sigma> i b)"
        by (rule App.IH(2)[where h=h and i=i and g=g and a=b, OF bn App.prems(2,3,4,5,6) ba be])
    qed
  next
    case (Lam B \<tau> n)
    have whole_type: "paper_R_has_type G (NLam n B) (Arr (G n) \<tau>)"
      by (rule paper_R_has_type.Lam[OF Lam.hyps(1,2,3)])
    have language: "paper_R_in_language \<Sigma> G (NLam n B) (Arr (G n) \<tau>)"
      unfolding paper_R_in_language_def by (rule conjI[OF whole_type Lam.prems(1)])
    have rt: "paper_R_type (Arr (G n) \<tau>)" by (rule paper_R_result_type[OF whole_type])
    have member: "a \<in> explode (D (Arr (G n) \<tau>) (target h))"
      by (rule paper_ZF_action_model_eval_member[OF model language Lam.prems(2,3,6,7,8)])
    show ?case by (rule paper_ZF_premodel_eval_Lam_naturality[OF premodel rt Lam.prems(2,4,5,6,8) member])
  qed
qed

theorem paper_ZF_action_model_eval_naturality:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G B \<rho>"
    and first: "h \<in> explode Ar" and origin: "source h = root"
    and second: "i \<in> explode Ar" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g B"
    and evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some a"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
    (paper_ZF_action_transport_assignment G T i g) = Some (T \<rho> i a)"
proof -
  have term_type: "paper_R_has_type G B \<rho>" and names: "named_in_signature \<Sigma> B"
    using language unfolding paper_R_in_language_def by blast+
  show ?thesis by (rule paper_ZF_action_model_typed_eval_naturality[
    OF model term_type names first origin second meeting typed adequate evaluated])
qed

end
