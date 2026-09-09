theory Bacon_Source_ZF_Evaluation_Locality
  imports Bacon_Source_ZF_Partial_Interpretation
begin

section \<open>The partial interpreter depends only on free variables\<close>

text \<open>
  If g and k agree on FV(A), the two partial interpretations of
  A are equal, including the case where both are undefined.
  Source role: Definition 3.1(ii.c), p.44, in the passage from
  action models to BBK models (Proposition 3.21, p.57).

  This is a property of the independent recursion. It needs no
  model, typing, adequacy or totality assumption. For abstraction,
  transport preserves agreement away from the binder, and updating
  both assignments gives the same value at the binder. Equality
  holds at every outgoing pair, so both the definedness condition
  and the resulting graph coincide.
\<close>

theorem paper_ZF_action_eval_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G A h k"
  using agree
proof (induction A arbitrary: h g k)
  case (NVar n)
  have equal: "g n = k n" by (rule NVar.prems; simp)
  show ?case by (simp only: paper_ZF_action_eval.simps equal)
next
  case (NConst c \<rho>)
  show ?case by (simp only: paper_ZF_action_eval.simps)
next
  case (NLogical l)
  show ?case by (simp only: paper_ZF_action_eval.simps)
next
  case (NApp F B)
  have agree_head: "g n = k n" if "n \<in> named_fv F" for n
    by (rule NApp.prems; use that in \<open>simp\<close>)
  have agree_argument: "g n = k n" if "n \<in> named_fv B" for n
    by (rule NApp.prems; use that in \<open>simp\<close>)
  have head: "paper_ZF_action_eval Ar source target compose identity D T I G F h g =
      paper_ZF_action_eval Ar source target compose identity D T I G F h k"
    by (rule NApp.IH(1)[where h=h and g=g and k=k, OF agree_head])
  have argument: "paper_ZF_action_eval Ar source target compose identity D T I G B h g =
      paper_ZF_action_eval Ar source target compose identity D T I G B h k"
    by (rule NApp.IH(2)[where h=h and g=g and k=k, OF agree_argument])
  show ?case by (simp only: paper_ZF_action_eval.simps head argument)
next
  case (NLam n B)
  have body_equal:
    "paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
        ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) =
      paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
        ((paper_ZF_action_transport_assignment G T i k)(n := Some a))" for i a
  proof (rule NLam.IH)
    fix m
    assume free: "m \<in> named_fv B"
    show "((paper_ZF_action_transport_assignment G T i g)(n := Some a)) m =
      ((paper_ZF_action_transport_assignment G T i k)(n := Some a)) m"
    proof (cases "m = n")
      case True
      show ?thesis by (simp add: True)
    next
      case False
      have outer: "m \<in> named_fv (NLam n B)" using free False by simp
      have equal: "g m = k m" by (rule NLam.prems[OF outer])
      show ?thesis by (simp add: False paper_ZF_action_transport_assignment_def
        paper_hom_assignment_def equal)
    qed
  qed
  have bodies:
    "paper_ZF_action_abstraction_body compose T G n
        (paper_ZF_action_eval Ar source target compose identity D T I G B) h g =
      paper_ZF_action_abstraction_body compose T G n
        (paper_ZF_action_eval Ar source target compose identity D T I G B) h k"
  proof (rule ext)
    fix z
    show "paper_ZF_action_abstraction_body compose T G n
        (paper_ZF_action_eval Ar source target compose identity D T I G B) h g z =
      paper_ZF_action_abstraction_body compose T G n
        (paper_ZF_action_eval Ar source target compose identity D T I G B) h k z"
      by (simp only: paper_ZF_action_abstraction_body_def; rule body_equal)
  qed
  show ?case by (simp only: paper_ZF_action_eval.simps paper_ZF_action_abstract_def Let_def bodies)
qed

end
