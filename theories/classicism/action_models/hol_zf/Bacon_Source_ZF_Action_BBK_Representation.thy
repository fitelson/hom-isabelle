theory Bacon_Source_ZF_Action_BBK_Representation
  imports Bacon_Source_ZF_Action_Logical_Equivalence
begin

section \<open>Logical Equivalence is valid in the same constructed BBK model\<close>

lemma paper_ZF_action_bbk_logical_equivalence_valid:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and derivation: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_ZF_action_bbk_domain D (target h))
    (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h)
    (paper_ZF_action_bbk_valuation target identity h)
    (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
proof -
  let ?D = "paper_ZF_action_bbk_domain D (target h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  let ?E = "named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q)"
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  have language: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_equivalence_vector_language[OF left right binders])
  show ?thesis unfolding M.paper_R_valid_def
  proof (rule conjI[OF language], intro allI impI)
    fix g
    assume typed: "named_env_typed ?D G g" and adequate: "named_adequate g ?E"
    have at: "paper_ZF_action_env_typed D G (target h) g"
      using typed by (simp only: paper_ZF_action_bbk_env_iff)
    have holds: "paper_ZF_action_holds Ar source target compose identity D T I G h g ?E"
      by (rule paper_ZF_action_model_logical_equivalence_at_assignment[
        OF model derivation left right binders arrow origin at adequate])
    have truth: "?V (?J g ?E)"
      by (rule iffD1[OF paper_ZF_action_bbk_holds_iff[OF model language arrow origin typed adequate] holds])
    show "M.paper_R_satisfies g ?E" by (simp only: M.paper_R_satisfies_def; rule truth)
  qed
qed

section \<open>Proposition 3.21, with a single fixed candidate throughout\<close>

text \<open>
  Each root arrow h:Root→W determines one R-BBK model Mₕ.
  Every R formula has the same truth in Mₕ and in the action model
  at h, under the same adequate partial assignment. Every H-certified
  Logical Equivalence instance is valid in that very same Mₕ.
  Source: Proposition 3.21, p.70, and Proposition C.7, p.71.

  Bodies need not be closed. Binder vectors are outermost-first and may
  be empty or contain repeated names; the explicit R binder guard is
  retained. The final assignment need cover only the free variables of
  the vector identity, not all free variables of the unabstracted bodies.
  The H certificate is the independent R judgment, not a C theorem.

  This packages the checked constructions and truth lemmas, rather than
  defining a new model class by validity. It assumes only the supplied
  generic coded action model and a root arrow. No BBK model, Logical
  Equivalence axiom, root uniqueness or completeness premise is added.
\<close>

theorem paper_ZF_action_bbk_representation:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
  shows "paper_R_bbk_model \<Sigma> G (paper_ZF_action_bbk_domain D (target h))
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h)
      (paper_ZF_action_bbk_valuation target identity h) \<and>
    (\<forall>A g. paper_R_in_language \<Sigma> G A Prop \<longrightarrow>
      named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g \<longrightarrow> named_adequate g A \<longrightarrow>
      (paper_ZF_action_bbk_valuation target identity h
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A) =
       paper_ZF_action_holds Ar source target compose identity D T I G h g A)) \<and>
    (\<forall>P Q ns. paper_R_named_H \<Sigma> G (named_paper_iff G P Q) \<longrightarrow>
      paper_R_in_language \<Sigma> G P Prop \<longrightarrow> paper_R_in_language \<Sigma> G Q Prop \<longrightarrow>
      list_all paper_R_type (map G ns) \<longrightarrow>
      paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_ZF_action_bbk_domain D (target h))
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h)
        (paper_ZF_action_bbk_valuation target identity h)
        (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q)))"
proof (rule conjI[OF paper_ZF_action_to_R_bbk_model[OF model arrow origin]], rule conjI)
  show "\<forall>A g. paper_R_in_language \<Sigma> G A Prop \<longrightarrow>
      named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g \<longrightarrow> named_adequate g A \<longrightarrow>
      (paper_ZF_action_bbk_valuation target identity h
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A) =
       paper_ZF_action_holds Ar source target compose identity D T I G h g A)"
  proof (intro allI impI)
    fix A g
    assume language: "paper_R_in_language \<Sigma> G A Prop"
      and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g" and adequate: "named_adequate g A"
    show "paper_ZF_action_bbk_valuation target identity h
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A) =
      paper_ZF_action_holds Ar source target compose identity D T I G h g A"
      by (rule sym[OF paper_ZF_action_bbk_holds_iff[OF model language arrow origin typed adequate]])
  qed
next
  show "\<forall>P Q ns. paper_R_named_H \<Sigma> G (named_paper_iff G P Q) \<longrightarrow>
      paper_R_in_language \<Sigma> G P Prop \<longrightarrow> paper_R_in_language \<Sigma> G Q Prop \<longrightarrow>
      list_all paper_R_type (map G ns) \<longrightarrow>
      paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_ZF_action_bbk_domain D (target h))
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h)
        (paper_ZF_action_bbk_valuation target identity h)
        (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
    by (intro allI impI; rule paper_ZF_action_bbk_logical_equivalence_valid[OF model arrow origin]; assumption)
qed

end
