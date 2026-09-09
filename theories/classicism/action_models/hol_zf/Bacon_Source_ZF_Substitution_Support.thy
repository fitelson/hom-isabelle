theory Bacon_Source_ZF_Substitution_Support
  imports Bacon_Source_ZF_Model_Evaluation_Naturality Bacon_Source_ZF_Evaluation_Locality
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Literal substitution and partial-assignment support\<close>

text \<open>
  The equation A[C/x] uses the literal, single-pass replacement from
  Figure 2, p.8. Its capture restriction remains an explicit hypothesis
  in the semantic theorem. No assignment completion is involved.
\<close>

lemma paper_R_named_subst_type:
  assumes body: "paper_R_has_type G B \<rho>"
    and payload: "paper_R_has_type G C (G x)"
  shows "paper_R_has_type G (named_subst x C B) \<rho>"
  using body
  by (induction rule: paper_R_has_type.induct)
    (auto intro: paper_R_has_type.intros payload)

lemma paper_R_named_subst_language:
  assumes body: "paper_R_in_language \<Sigma> G B \<rho>"
    and payload: "paper_R_in_language \<Sigma> G C (G x)"
  shows "paper_R_in_language \<Sigma> G (named_subst x C B) \<rho>"
  using body payload unfolding paper_R_in_language_def
  by (blast intro: paper_R_named_subst_type named_subst_signature)

lemma paper_ZF_substitution_adequate:
  assumes body: "named_adequate g (NLam x B)" and payload: "named_adequate g C"
  shows "named_adequate g (named_subst x C B)"
  using body payload named_subst_fv_upper[where x=x and B=C and A=B]
  unfolding named_adequate_def by auto

lemma paper_ZF_action_eval_update_fresh:
  assumes fresh: "x \<notin> named_fv B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G B h (g(x := Some c)) =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
  by (rule paper_ZF_action_eval_locality; use fresh in \<open>auto\<close>)

section \<open>Abstraction graphs depend only on legitimate outgoing pairs\<close>

lemma paper_ZF_substitution_abstract_cong:
  assumes points: "\<And>z. Elem z (paper_ZF_pair_code Ar source target (D (G n)) (target h)) \<Longrightarrow>
    paper_ZF_action_abstraction_body compose T G n B h g z =
    paper_ZF_action_abstraction_body compose T G n C h k z"
  shows "paper_ZF_action_abstract Ar source target compose D T G n B h g =
    paper_ZF_action_abstract Ar source target compose D T G n C h k"
proof -
  let ?P = "paper_ZF_pair_code Ar source target (D (G n)) (target h)"
  let ?V = "paper_ZF_action_abstraction_body compose T G n B h g"
  let ?W = "paper_ZF_action_abstraction_body compose T G n C h k"
  have defined: "(\<forall>z\<in>explode ?P. ?V z \<noteq> None) \<longleftrightarrow>
      (\<forall>z\<in>explode ?P. ?W z \<noteq> None)"
  proof (rule ball_cong[OF refl])
    fix z
    assume member: "z \<in> explode ?P"
    have elem: "Elem z ?P" using member by (simp only: explode_Elem)
    show "(?V z \<noteq> None) = (?W z \<noteq> None)" by (simp only: points[OF elem])
  qed
  have graphs: "Lambda ?P (\<lambda>z. the (?V z)) = Lambda ?P (\<lambda>z. the (?W z))"
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI,
      simp only: points)
  show ?thesis by (simp only: paper_ZF_action_abstract_def Let_def defined graphs)
qed

end
