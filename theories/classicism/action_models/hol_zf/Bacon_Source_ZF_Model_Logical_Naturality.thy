theory Bacon_Source_ZF_Model_Logical_Naturality
  imports Bacon_Source_ZF_Logical_Naturality Bacon_Source_ZF_Action_Model
begin

section \<open>Selected logical values use canonical transport\<close>

text \<open>
  For a premodel, identifying its type action with exponential
  precomposition requires the logical value to belong to the selected
  fiber. This guard is not inferred from mere definedness.
  Definition 3.20 supplies it for an actual action model.
  Source: Definitions 3.18–3.20, pp.55–56, and C.1, p.70.
\<close>

theorem paper_ZF_premodel_logical_naturality:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and rt: "paper_R_type (paper_logical_type l)"
    and symbol: "paper_logical_type l = Arr \<sigma> \<tau>"
    and arrow: "i \<in> explode A"
    and member: "paper_ZF_logical_value A source target compose identity D T (source i) l
      \<in> explode (D (paper_logical_type l) (source i))"
  shows "T (paper_logical_type l) i
      (paper_ZF_logical_value A source target compose identity D T (source i) l) =
    paper_ZF_logical_value A source target compose identity D T (target i) l"
proof -
  have rooted: "paper_rooted_category Obj (explode A) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret C: paper_rooted_category Obj "explode A" source target compose identity root
    by (rule rooted)
  have category: "paper_category Obj (explode A) source target compose identity" by unfold_locales
  have ar: "paper_R_type (Arr \<sigma> \<tau>)" using rt by (simp only: symbol)
  have subaction: "paper_subaction Obj (explode A) source target compose identity
      (\<lambda>W. explode (D (Arr \<sigma> \<tau>) W)) (T (Arr \<sigma> \<tau>))
      (\<lambda>W. explode (paper_ZF_exponential_code A source target compose
        (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W))
      (paper_ZF_exponential_transport_code A source target compose (D \<sigma>))"
    using premodel ar unfolding paper_ZF_action_premodel_def by blast
  have typed_value: "paper_ZF_logical_value A source target compose identity D T (source i) l
      \<in> explode (D (Arr \<sigma> \<tau>) (source i))"
    using member by (simp only: symbol)
  have transport: "T (Arr \<sigma> \<tau>) i
      (paper_ZF_logical_value A source target compose identity D T (source i) l) =
    paper_ZF_exponential_transport_code A source target compose (D \<sigma>) i
      (paper_ZF_logical_value A source target compose identity D T (source i) l)"
    by (rule paper_subaction_transport[OF subaction arrow typed_value])
  show ?thesis
    by (simp only: symbol transport paper_ZF_logical_value_precompose[OF category arrow symbol])
qed

section \<open>The independent model criterion discharges the membership guard\<close>

lemma paper_ZF_action_model_logical_value_member:
  fixes \<Sigma> :: "'c ssignature"
  assumes model: "paper_ZF_action_model \<Sigma> G Obj A source target compose identity root D T I"
    and rt: "paper_R_type (paper_logical_type l)"
    and arrow: "h \<in> explode A" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
  shows "paper_ZF_logical_value A source target compose identity D T (target h) l
    \<in> explode (D (paper_logical_type l) (target h))"
proof -
  have language: "paper_R_in_language \<Sigma> G (NLogical l) (paper_logical_type l)"
    unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_has_type.Logical[OF rt]]; simp)
  have adequate: "named_adequate g (NLogical l :: 'c paper_named_term)"
    by (simp add: named_adequate_def)
  obtain v where evaluated: "paper_ZF_action_eval A source target compose identity D T I G
      (NLogical l) h g = Some v"
    and member: "v \<in> explode (D (paper_logical_type l) (target h))"
    using model language arrow origin typed adequate unfolding paper_ZF_action_model_def by blast
  have equal: "v = paper_ZF_logical_value A source target compose identity D T (target h) l"
    using evaluated by (simp only: paper_ZF_action_eval.simps option.inject)
  show ?thesis using member by (simp only: equal)
qed

theorem paper_ZF_action_model_logical_naturality:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj A source target compose identity root D T I"
    and rt: "paper_R_type (paper_logical_type l)"
    and first: "h \<in> explode A" and origin: "source h = root"
    and second: "i \<in> explode A" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
  shows "T (paper_logical_type l) i
      (paper_ZF_logical_value A source target compose identity D T (target h) l) =
    paper_ZF_logical_value A source target compose identity D T (target i) l"
proof -
  obtain \<sigma> \<tau> where symbol: "paper_logical_type l = Arr \<sigma> \<tau>"
    by (cases l; auto)
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have member: "paper_ZF_logical_value A source target compose identity D T (source i) l
      \<in> explode (D (paper_logical_type l) (source i))"
    using paper_ZF_action_model_logical_value_member[OF model rt first origin typed]
    by (simp only: meeting)
  show ?thesis
    by (simp only: meeting; rule paper_ZF_premodel_logical_naturality[OF premodel rt symbol second member])
qed

end
