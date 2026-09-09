theory Bacon_Source_Relational_Naming_Separating_Reduct
  imports Bacon_Source_Relational_Diagram_Homomorphism Bacon_Source_Relational_Parameter_Theory
begin

section \<open>What a separating parameter-and-diagram target gives in the old language\<close>

context paper_R_diagram_target
begin

theorem paper_R_diagram_reduct_validates_theory:
  assumes theory_h: "paper_R_H_theory \<Sigma> G T"
    and parameter_valid: "\<forall>A\<in>paper_R_parameter_theory \<Sigma> G D T. target.paper_R_valid A"
  shows "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G E (paper_R_constant_pullback_denote Inl K) W A"
proof -
  interpret Reduct: paper_R_bbk_model \<Sigma> G E "paper_R_constant_pullback_denote Inl K" W
    by (rule paper_R_diagram_reduct_model)
  show ?thesis
  proof (intro ballI)
    fix A
    assume member: "A \<in> T"
    have language: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_H_theory_language[OF theory_h member])
    have parameter: "map_named_term Inl id A \<in> paper_R_parameter_theory \<Sigma> G D T"
      by (rule iffD2[OF paper_R_parameter_theory_old_iff[where D=D, OF theory_h] member])
    have target_valid: "target.paper_R_valid (map_named_term Inl id A)" using parameter_valid parameter by blast
    show "Reduct.paper_R_valid A"
    proof (rule Reduct.paper_R_validI[OF language])
      fix g
      assume typed: "named_env_typed E G g" and adequate: "named_adequate g A"
      have mapped_adequate: "named_adequate g (map_named_term Inl id A)"
        by (rule iffD2[OF paper_R_naming_old_adequate_iff adequate])
      have truth: "W (K g (map_named_term Inl id A))" by (rule target.paper_R_validE[OF target_valid typed mapped_adequate])
      show "W (paper_R_constant_pullback_denote Inl K g A)"
        by (simp only: paper_R_constant_pullback_denote_def; rule truth)
    qed
  qed
qed

theorem paper_R_diagram_discriminator_separates:
  assumes pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    and discriminator: "target.paper_R_valid
      (named_paper_not (named_paper_iff G (NConst (Inr p) Prop) (NConst (Inr q) Prop)))"
  shows "W (paper_R_diagram_map Prop p) \<noteq> W (paper_R_diagram_map Prop q)"
proof -
  let ?P = "NConst (Inr p) Prop :: ('c + 'v) paper_named_term"
  let ?Q = "NConst (Inr q) Prop :: ('c + 'v) paper_named_term"
  let ?I = "named_paper_iff G ?P ?Q"
  have pl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?P Prop"
    by (rule paper_R_diagram_value_name_language[OF pm])
  have ql: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?Q Prop"
    by (rule paper_R_diagram_value_name_language[OF qm])
  have il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?I Prop"
    by (rule paper_R_named_paper_iff_language[OF source.stock_rich pl ql])
  have typed: "named_env_typed E G Map.empty" by (simp add: named_env_typed_def)
  have pa: "named_adequate (Map.empty :: 'w named_assignment) ?P"
    and qa: "named_adequate (Map.empty :: 'w named_assignment) ?Q"
    and ia: "named_adequate (Map.empty :: 'w named_assignment) ?I"
    and na: "named_adequate (Map.empty :: 'w named_assignment) (named_paper_not ?I)"
    by (simp_all add: named_adequate_def named_paper_defined_fv named_paper_primitive_fv)
  have truth: "W (K Map.empty (named_paper_not ?I))" by (rule target.paper_R_validE[OF discriminator typed na])
  have negation: "W (K Map.empty (named_paper_not ?I)) = (\<not> W (K Map.empty ?I))"
    by (rule target.paper_R_named_not_truth[OF il typed ia])
  have equivalence: "W (K Map.empty ?I) = (W (K Map.empty ?P) = W (K Map.empty ?Q))"
    by (rule target.paper_R_named_paper_iff_truth[OF pl ql typed pa qa])
  show ?thesis using truth negation equivalence unfolding paper_R_diagram_map_def by blast
qed

end

text \<open>
  The target names denote h(p) and h(q); they are not asserted to denote
  p and q themselves. These results retain the original signature by
  reduct and use no truth-preservation condition on the diagram map.
  No target-model existence claim is made in this helper leaf.
\<close>

end
