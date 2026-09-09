theory Bacon_Source_ZF_Evaluation_Contexts
  imports Bacon_Source_ZF_Evaluation_Locality
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Steps
begin

section \<open>Abstraction congruence includes its definedness test\<close>

text \<open>
  Equality of body callbacks at every legitimate outgoing pair gives
  equal partial abstractions. The callbacks are compared at i∘h and
  the transported assignment updated at the binder. Both the Some/None
  condition and the Lambda graph agree, even for an empty pair domain.
  This raw fact will also permit a later language-guarded use of C.2;
  no equality at irrelevant or ill-typed inputs is needed by this helper.
\<close>

lemma paper_ZF_action_abstract_cong:
  assumes bodies: "\<And>i a. Elem (Opair i a) (paper_ZF_pair_code Ar source target (D (G n)) (target h)) \<Longrightarrow>
    B (compose i h) ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) =
    C (compose i h) ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
  shows "paper_ZF_action_abstract Ar source target compose D T G n B h g =
    paper_ZF_action_abstract Ar source target compose D T G n C h g"
proof -
  let ?P = "paper_ZF_pair_code Ar source target (D (G n)) (target h)"
  let ?V = "paper_ZF_action_abstraction_body compose T G n B h g"
  let ?W = "paper_ZF_action_abstraction_body compose T G n C h g"
  have equal: "?V z = ?W z" if member: "Elem z ?P" for z
  proof -
    obtain i a where shape: "z = Opair i a"
      by (rule paper_ZF_pair_codeE[OF member]; rule that; assumption)
    have pair: "Elem (Opair i a) ?P" using member by (simp only: shape)
    show ?thesis by (simp only: shape paper_ZF_action_abstraction_body_pair; rule bodies[OF pair])
  qed
  have defined: "(\<forall>z\<in>explode ?P. ?V z \<noteq> None) = (\<forall>z\<in>explode ?P. ?W z \<noteq> None)"
  proof (rule ball_cong[OF refl])
    fix z
    assume member: "z \<in> explode ?P"
    have elem: "Elem z ?P" using member by (simp only: explode_Elem)
    show "(?V z \<noteq> None) = (?W z \<noteq> None)" by (simp only: equal[OF elem])
  qed
  have graphs: "Lambda ?P (\<lambda>z. the (?V z)) = Lambda ?P (\<lambda>z. the (?W z))"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix z
    assume member: "Elem z ?P"
    show "the (?V z) = the (?W z)" by (simp only: equal[OF member])
  qed
  show ?thesis by (simp only: paper_ZF_action_abstract_def Let_def defined graphs)
qed

section \<open>Uniform equality lifts through named compatible contexts\<close>

text \<open>
  If each permitted root replacement has equal evaluator callbacks at
  EVERY arrow and assignment, the same is true in every named App/Lam
  context. A context may bind variables free in the replaced terms.
  Source role: Proposition C.2, pp.70–71, and Figure 2, pp.7–8.

  This is raw functional congruence for the independent recursion,
  including undefined values. It assumes no category, type, model or
  totality predicate. Its uniform callback premise is stronger than
  equality merely on typed adequate root inputs. A model-level C.2
  wrapper must preserve those guards through each context; the bounded
  abstraction helper above is available for that separate proof.
\<close>

theorem paper_ZF_action_eval_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>U V h g. R U V \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G U h g =
      paper_ZF_action_eval Ar source target compose identity D T I G V h g"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
  using step
proof (induction arbitrary: h g rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule roots[OF root.hyps])
next
  case (App_left M M' N)
  have head: "paper_ZF_action_eval Ar source target compose identity D T I G M h g =
      paper_ZF_action_eval Ar source target compose identity D T I G M' h g"
    by (rule App_left.IH)
  show ?case by (simp only: paper_ZF_action_eval.simps head)
next
  case (App_right N N' M)
  have argument: "paper_ZF_action_eval Ar source target compose identity D T I G N h g =
      paper_ZF_action_eval Ar source target compose identity D T I G N' h g"
    by (rule App_right.IH)
  show ?case by (simp only: paper_ZF_action_eval.simps argument)
next
  case (Lam_body M M' n)
  show ?case
  proof (simp only: paper_ZF_action_eval.simps; rule paper_ZF_action_abstract_cong)
    fix i a
    assume pair: "Elem (Opair i a) (paper_ZF_pair_code Ar source target (D (G n)) (target h))"
    show "paper_ZF_action_eval Ar source target compose identity D T I G M (compose i h)
        ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) =
      paper_ZF_action_eval Ar source target compose identity D T I G M' (compose i h)
        ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
      by (rule Lam_body.IH)
  qed
qed

corollary paper_ZF_action_eval_replacement:
  assumes step: "named_compatible_step (\<lambda>U V. U = A \<and> V = B) C E"
    and equal: "\<And>h g. paper_ZF_action_eval Ar source target compose identity D T I G A h g =
      paper_ZF_action_eval Ar source target compose identity D T I G B h g"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G C h g =
    paper_ZF_action_eval Ar source target compose identity D T I G E h g"
proof (rule paper_ZF_action_eval_compatible[OF step])
  fix U V h g
  assume shape: "U = A \<and> V = B"
  show "paper_ZF_action_eval Ar source target compose identity D T I G U h g =
    paper_ZF_action_eval Ar source target compose identity D T I G V h g"
    using shape equal[of h g] by blast
qed

end
