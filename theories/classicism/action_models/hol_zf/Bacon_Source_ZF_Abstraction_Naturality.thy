theory Bacon_Source_ZF_Abstraction_Naturality
  imports Bacon_Source_ZF_Partial_Interpretation Bacon_Source_ZF_Assignment_Transport_Laws
    Bacon_Source_ZF_Premodel_Application_Naturality
begin

section \<open>The abstraction diagram commutes on all outgoing pairs\<close>

text \<open>
  Compare the body at j∘(i∘h) under (j·(i·g))[n↦a]
  with the body at (j∘i)∘h under ((j∘i)·g)[n↦a].
  Category associativity and assignment composition identify these
  inputs literally. Definedness at the original abstraction therefore
  supplies definedness at every pair of the transported abstraction.
  Source: the abstraction step of C.1, p.70.

  The first theorem uses CANONICAL exponential transport. It does
  not apply a premodel's own action outside its selected domain.
  The second theorem requires selected membership before identifying
  the two transports. No body-naturality or action-model premise is
  required for this abstraction step.
\<close>

theorem paper_ZF_action_abstract_naturality:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and first: "h \<in> explode Ar" and second: "i \<in> explode Ar"
    and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and returned: "paper_ZF_action_abstract Ar source target compose D T G n B h g = Some F"
  shows "paper_ZF_action_abstract Ar source target compose D T G n B (compose i h)
      (paper_ZF_action_transport_assignment G T i g) =
    Some (paper_ZF_exponential_transport_code Ar source target compose (D (G n)) i F)"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have category: "paper_category Obj (explode Ar) source target compose identity" by unfold_locales
  have ct: "target (compose i h) = target i" by (rule C.compose_target[OF first second meeting])
  have source_typed: "paper_ZF_action_env_typed D G (source i) g"
    using typed by (simp only: meeting)
  let ?P = "paper_ZF_pair_code Ar source target (D (G n)) (target i)"
  let ?g = "paper_ZF_action_transport_assignment G T i g"
  let ?V = "paper_ZF_action_abstraction_body compose T G n B (compose i h) ?g"
  have points: "?V z = Some (app F (Opair (compose (Fst z) i) (Snd z)))"
    if member: "Elem z ?P" for z
  proof -
    have ja: "Fst z \<in> explode Ar" and origin: "source (Fst z) = target i"
      using paper_ZF_pair_code_projections[OF member] by blast+
    have ij: "target i = source (Fst z)" by (rule origin[symmetric])
    have old_pair_at_source: "Elem (Opair (compose (Fst z) i) (Snd z))
        (paper_ZF_pair_code Ar source target (D (G n)) (source i))"
      by (rule paper_ZF_pair_precompose_code[OF category second member])
    have old_pair: "Elem (Opair (compose (Fst z) i) (Snd z))
        (paper_ZF_pair_code Ar source target (D (G n)) (target h))"
      using old_pair_at_source by (simp only: meeting)
    have old_body: "Some (app F (Opair (compose (Fst z) i) (Snd z))) =
        B (compose (compose (Fst z) i) h)
          ((paper_ZF_action_transport_assignment G T (compose (Fst z) i) g)(n := Some (Snd z)))"
      by (rule paper_ZF_action_abstract_apply[OF returned old_pair])
    have assoc: "compose (Fst z) (compose i h) = compose (compose (Fst z) i) h"
      by (rule C.compose_assoc[OF first second ja meeting ij])
    have assignments:
      "paper_ZF_action_transport_assignment G T (Fst z) ?g =
        paper_ZF_action_transport_assignment G T (compose (Fst z) i) g"
      by (rule sym[OF paper_ZF_premodel_assignment_transport_compose[
        OF premodel second ja ij source_typed]])
    have same_input: "?V z = B (compose (compose (Fst z) i) h)
        ((paper_ZF_action_transport_assignment G T (compose (Fst z) i) g)(n := Some (Snd z)))"
      by (simp only: paper_ZF_action_abstraction_body_def assoc assignments)
    show ?thesis by (rule trans[OF same_input old_body[symmetric]])
  qed
  have defined: "?V z \<noteq> None"
    if member: "z \<in> explode (paper_ZF_pair_code Ar source target (D (G n)) (target (compose i h)))" for z
  proof -
    have pair: "Elem z ?P" using member by (simp only: ct explode_Elem)
    show ?thesis by (simp only: points[OF pair]; simp)
  qed
  have raw_target:
    "paper_ZF_action_abstract Ar source target compose D T G n B (compose i h) ?g =
      Some (Lambda (paper_ZF_pair_code Ar source target (D (G n)) (target (compose i h)))
        (\<lambda>z. the (?V z)))"
    by (rule paper_ZF_action_abstract_defined; rule defined; assumption)
  have target_value: "paper_ZF_action_abstract Ar source target compose D T G n B (compose i h) ?g =
      Some (Lambda ?P (\<lambda>z. the (?V z)))"
    using raw_target by (simp only: ct)
  have graph_equal: "Lambda ?P (\<lambda>z. the (?V z)) =
      paper_ZF_exponential_transport_code Ar source target compose (D (G n)) i F"
  proof (unfold paper_ZF_exponential_transport_code_def, rule iffD2[OF Lambda_ext],
      rule conjI[OF refl], intro allI impI)
    fix z
    assume member: "Elem z ?P"
    show "the (?V z) = app F (Opair (compose (Fst z) i) (Snd z))"
      by (simp only: points[OF member]; simp)
  qed
  show ?thesis by (simp only: target_value graph_equal)
qed

theorem paper_ZF_premodel_eval_Lam_naturality:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and rt: "paper_R_type (Arr (G n) \<tau>)"
    and first: "h \<in> explode Ar" and second: "i \<in> explode Ar" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and returned: "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h g = Some F"
    and member: "F \<in> explode (D (Arr (G n) \<tau>) (target h))"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) (compose i h)
      (paper_ZF_action_transport_assignment G T i g) = Some (T (Arr (G n) \<tau>) i F)"
proof -
  have abstraction: "paper_ZF_action_abstract Ar source target compose D T G n
      (paper_ZF_action_eval Ar source target compose identity D T I G B) h g = Some F"
    using returned by (simp only: paper_ZF_action_eval.simps)
  have subaction: "paper_subaction Obj (explode Ar) source target compose identity
      (\<lambda>W. explode (D (Arr (G n) \<tau>) W)) (T (Arr (G n) \<tau>))
      (\<lambda>W. explode (paper_ZF_exponential_code Ar source target compose
        (D (G n)) (T (G n)) (D \<tau>) (T \<tau>) W))
      (paper_ZF_exponential_transport_code Ar source target compose (D (G n)))"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  have source_member: "F \<in> explode (D (Arr (G n) \<tau>) (source i))"
    using member by (simp only: meeting)
  have own_transport: "T (Arr (G n) \<tau>) i F =
      paper_ZF_exponential_transport_code Ar source target compose (D (G n)) i F"
    by (rule paper_subaction_transport[OF subaction second source_member])
  show ?thesis
    by (simp only: paper_ZF_action_eval.simps own_transport;
      rule paper_ZF_action_abstract_naturality[OF premodel first second meeting typed abstraction])
qed

end
