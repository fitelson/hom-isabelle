theory Bacon_Source_ZF_Action_Constant_Pullback
  imports Bacon_Source_ZF_Action_Model
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Typed_Constant_Map
begin

section \<open>Changing constant names leaves the partial interpretation unchanged\<close>

lemma paper_ZF_action_eval_typed_constants:
  "paper_ZF_action_eval Ar s t c i D T (\<lambda>\<sigma> b. I \<sigma> (\<rho> \<sigma> b)) G A =
    paper_ZF_action_eval Ar s t c i D T I G (paper_R_typed_constant_map \<rho> A)"
proof (induction A)
  case NVar
  show ?case by (rule ext; rule ext; simp only: paper_ZF_action_eval.simps paper_R_typed_constant_map.simps)
next
  case NConst
  show ?case by (rule ext; rule ext; simp only: paper_ZF_action_eval.simps paper_R_typed_constant_map.simps)
next
  case NLogical
  show ?case by (rule ext; rule ext; simp only: paper_ZF_action_eval.simps paper_R_typed_constant_map.simps)
next
  case NApp
  show ?case by (rule ext; rule ext;
    simp only: paper_ZF_action_eval.simps paper_R_typed_constant_map.simps NApp.IH)
next
  case NLam
  show ?case by (rule ext; rule ext;
    simp only: paper_ZF_action_eval.simps paper_R_typed_constant_map.simps NLam.IH)
qed

lemma paper_ZF_action_holds_typed_constants:
  "paper_ZF_action_holds Ar s t c i D T (\<lambda>\<sigma> b. I \<sigma> (\<rho> \<sigma> b)) G h g A =
    paper_ZF_action_holds Ar s t c i D T I G h g (paper_R_typed_constant_map \<rho> A)"
  by (simp only: paper_ZF_action_holds_def paper_ZF_action_eval_typed_constants)

lemma paper_ZF_action_premodel_typed_constant_pullback:
  assumes premodel: "paper_ZF_action_premodel \<Omega> Obj Ar s t c i Root D T I"
    and maps: "\<And>\<sigma> b. b \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> b \<in> \<Omega> \<sigma>"
  shows "paper_ZF_action_premodel \<Sigma> Obj Ar s t c i Root D T (\<lambda>\<sigma> b. I \<sigma> (\<rho> \<sigma> b))"
  using premodel maps unfolding paper_ZF_action_premodel_def by auto

theorem paper_ZF_action_model_typed_constant_pullback:
  assumes model: "paper_ZF_action_model \<Omega> G Obj Ar s t c i Root D T I"
    and maps: "\<And>\<sigma> b. b \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> b \<in> \<Omega> \<sigma>"
  shows "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T (\<lambda>\<sigma> b. I \<sigma> (\<rho> \<sigma> b))"
proof -
  have rich: "paper_R_rich G" and premodel: "paper_ZF_action_premodel \<Omega> Obj Ar s t c i Root D T I"
    using model unfolding paper_ZF_action_model_def by blast+
  have new_premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar s t c i Root D T (\<lambda>\<sigma> b. I \<sigma> (\<rho> \<sigma> b))"
    by (rule paper_ZF_action_premodel_typed_constant_pullback[OF premodel maps])
  show ?thesis unfolding paper_ZF_action_model_def
  proof (rule conjI[OF rich], rule conjI[OF new_premodel], intro allI impI)
    fix A \<tau> h g
    assume language: "paper_R_in_language \<Sigma> G A \<tau>"
      and arrow: "h \<in> explode Ar" and origin: "s h = Root"
      and typed: "paper_ZF_action_env_typed D G (t h) g" and adequate: "named_adequate g A"
    have mapped_language: "paper_R_in_language \<Omega> G (paper_R_typed_constant_map \<rho> A) \<tau>"
      by (rule paper_R_typed_constant_map_language[OF language maps])
    have mapped_adequate: "named_adequate g (paper_R_typed_constant_map \<rho> A)"
      using adequate by (simp only: named_adequate_def paper_R_typed_constant_map_fv)
    have defined: "\<exists>v. paper_ZF_action_eval Ar s t c i D T I G (paper_R_typed_constant_map \<rho> A) h g = Some v \<and>
        v \<in> explode (D \<tau> (t h))"
      using model mapped_language arrow origin typed mapped_adequate unfolding paper_ZF_action_model_def by blast
    show "\<exists>v. paper_ZF_action_eval Ar s t c i D T (\<lambda>\<sigma> b. I \<sigma> (\<rho> \<sigma> b)) G A h g = Some v \<and>
      v \<in> explode (D \<tau> (t h))"
      by (simp only: paper_ZF_action_eval_typed_constants; rule defined)
  qed
qed

text \<open>
  Only the interpretation of nonlogical constants is pulled back.
  Objects, arrows, the root, domains, actions and variable assignments
  are unchanged. The raw evaluation equality includes undefined results
  and every abstraction-body test; the model theorem independently
  transports definedness and correct-domain membership.

  No injectivity, surjectivity, BBK-model assumption or new completeness
  premise is needed. The name carriers may differ, while the world-index
  carrier stays the same. Sources: typed signatures in §1.1 and the
  constant and abstraction clauses of Definition 3.19.
\<close>

end
