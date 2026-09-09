theory Bacon_Source_ZF_Action_BBK_Logical_Application
  imports Bacon_Source_ZF_Action_BBK_Interpretation Bacon_Source_ZF_Logical_Value_Evaluation
begin

section \<open>Primitive values and their legitimate identity inputs\<close>

lemma paper_ZF_action_bbk_denote_logical:
  "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NLogical l) =
    paper_ZF_logical_value Ar source target compose identity D T (target h) l"
  by (simp add: paper_ZF_action_bbk_denote_def)

lemma paper_ZF_action_bbk_identity_data:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar"
  shows "identity (target h) \<in> explode Ar"
    "source (identity (target h)) = target h"
    "target (identity (target h)) = target h"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity Root"
    using model unfolding paper_ZF_action_model_def paper_ZF_action_premodel_def by blast
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity Root by (rule rooted)
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  show "identity (target h) \<in> explode Ar" by (rule C.identity_arrow[OF object])
  show "source (identity (target h)) = target h" by (rule C.identity_source[OF object])
  show "target (identity (target h)) = target h" by (rule C.identity_target[OF object])
qed

lemma paper_ZF_action_bbk_identity_transport:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and member: "a \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
  shows "T \<sigma> (identity (target h)) a = a"
proof -
  have rt: "paper_R_type \<sigma>" and am: "a \<in> explode (D \<sigma> (target h))"
    using member by (auto simp only: paper_ZF_action_bbk_domain_member)
  have action: "paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D \<sigma> W)) (T \<sigma>)"
    using model rt unfolding paper_ZF_action_model_def paper_ZF_action_premodel_def by blast
  interpret Act: paper_action Obj "explode Ar" source target compose identity "\<lambda>W. explode (D \<sigma> W)" "T \<sigma>"
    by (rule action)
  show ?thesis by (rule Act.transport_identity[OF Act.target_object[OF arrow] am])
qed

lemma paper_ZF_action_bbk_identity_pair:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and member: "a \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
  shows "Elem (Opair (identity (target h)) a) (paper_ZF_pair_code Ar source target (D \<sigma>) (target h))"
proof -
  have am: "a \<in> explode (D \<sigma> (target h))" using member by (simp only: paper_ZF_action_bbk_domain_member; blast)
  show ?thesis by (simp only: paper_ZF_pair_code_member paper_ZF_action_bbk_identity_data[OF model arrow]; simp only: am; simp)
qed

section \<open>Application of the actual primitive graphs\<close>

text \<open>
  Model totality supplies all denotation and graph-input guards through
  the candidate application theorem. Logical graph membership is not a
  new premise. These equations merely expose the literal graph already
  returned by the independent evaluator (Definition 3.19, p.56).
\<close>

lemma paper_ZF_action_bbk_unary_logical_denote:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and symbol: "paper_logical_type l = Arr \<sigma> Prop"
    and language: "paper_R_in_language \<Sigma> G A \<sigma>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g" and adequate: "named_adequate g A"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NLogical l) A) =
    app (paper_ZF_logical_value Ar source target compose identity D T (target h) l)
      (Opair (identity (target h)) (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A))"
proof -
  have rt: "paper_R_type (paper_logical_type l)"
    using paper_R_language_result_type[OF language] by (simp only: symbol; simp)
  have logical: "paper_R_in_language \<Sigma> G (NLogical l) (Arr \<sigma> Prop)"
    using paper_R_has_type.Logical[where G=G, OF rt] by (simp add: paper_R_in_language_def symbol)
  have whole: "named_adequate g (NApp (NLogical l) A)"
    using adequate by (simp add: named_adequate_def)
  show ?thesis by (simp only: paper_ZF_action_bbk_denote_application[OF model logical language arrow origin typed whole]
    paper_ZF_action_bbk_denote_logical)
qed

lemma paper_ZF_action_bbk_binary_logical_denote:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and symbol: "paper_logical_type l = Arr \<sigma> (Arr \<sigma> Prop)"
    and left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NApp (NLogical l) A) B) =
    app (app (paper_ZF_logical_value Ar source target compose identity D T (target h) l)
      (Opair (identity (target h)) (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A)))
      (Opair (identity (target h)) (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B))"
proof -
  have rt: "paper_R_type (paper_logical_type l)"
    using paper_R_language_result_type[OF left] by (simp only: symbol; simp)
  have logical: "paper_R_in_language \<Sigma> G (NLogical l) (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_R_has_type.Logical[where G=G, OF rt] by (simp add: paper_R_in_language_def symbol)
  have partial: "paper_R_in_language \<Sigma> G (NApp (NLogical l) A) (Arr \<sigma> Prop)"
    by (rule paper_R_language_App[OF logical left])
  have aa: "named_adequate g (NApp (NLogical l) A)"
    using adequate_left by (simp add: named_adequate_def)
  have ab: "named_adequate g (NApp (NApp (NLogical l) A) B)"
    using adequate_left adequate_right by (auto simp: named_adequate_def)
  show ?thesis by (simp only: paper_ZF_action_bbk_denote_application[OF model partial right arrow origin typed ab]
    paper_ZF_action_bbk_denote_application[OF model logical left arrow origin typed aa]
    paper_ZF_action_bbk_denote_logical)
qed

end
