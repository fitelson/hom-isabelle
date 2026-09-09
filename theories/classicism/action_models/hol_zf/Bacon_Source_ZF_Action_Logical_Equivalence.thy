theory Bacon_Source_ZF_Action_Logical_Equivalence
  imports Bacon_Source_ZF_Action_H_Soundness Bacon_Source_ZF_Model_Vector_Identity
begin

section \<open>Proposition C.7: every instance of Logical Equivalence is true\<close>

text \<open>
  If H⊢P↔Q, then A,h,g⊩(λn⃗.P)=(λn⃗.Q).
  Source: Proposition C.7, p.71. The H certificate uses the independent
  default-R calculus. We first obtain truth agreement at every root
  arrow from H soundness in the constructed BBK models. Powerset
  transport and C.1 then separate proposition values. Finally C.2
  lifts this equality through the vector, and primitive identity
  expresses equality of the resulting values.

  In particular, equality of truth at just one identity arrow is
  not substituted for equality of propositions. The final assignment
  need cover only the free variables of the vector abstractions.
  No BBK model or Logical Equivalence axiom is assumed.
\<close>

theorem paper_ZF_action_model_logical_equivalence:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and derivation: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g (named_lam_vec ns P)"
    and adequate_right: "named_adequate g (named_lam_vec ns Q)"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g
    (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
proof (rule paper_ZF_action_model_uniform_truth_vector_identity[
    OF model left right binders _ arrow origin typed adequate_left adequate_right])
  fix k u
  assume ka: "k \<in> explode Ar" and ko: "source k = root"
    and ut: "paper_ZF_action_env_typed D G (target k) u"
    and up: "named_adequate u P" and uq: "named_adequate u Q"
  show "paper_ZF_action_holds Ar source target compose identity D T I G k u P =
    paper_ZF_action_holds Ar source target compose identity D T I G k u Q"
    by (rule paper_ZF_action_model_H_iff_truth[OF model derivation left right ka ko ut up uq])
qed

corollary paper_ZF_action_model_logical_equivalence_at_assignment:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and derivation: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate: "named_adequate g
      (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g
    (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
proof -
  have aa: "named_adequate g (named_lam_vec ns P)" and ba: "named_adequate g (named_lam_vec ns Q)"
    using adequate by (auto simp: named_adequate_def named_paper_primitive_fv)
  show ?thesis by (rule paper_ZF_action_model_logical_equivalence[
    OF model derivation left right binders arrow origin typed aa ba])
qed

end
