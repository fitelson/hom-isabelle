theory Bacon_Source_Named_Assignments
  imports Bacon_Source_Named_Syntax Bacon_Source_BBK_Global_Assignments
begin

section \<open>Typed partial assignments and adequacy for named terms\<close>

text \<open>
  An assignment may be defined on only some named variables.  It is
  adequate for A when it assigns every variable in FV(A), and typed when
  each assigned value lies in the domain of that variable's fixed G-type.
  Source: Bacon--Dorr Definition 3.1 and its assignment convention,
  pp.43–44.

  Isabelle representation.  named_assignment is nat → value option:
  None means undefined, and NLam n binds the name n, not a de Bruijn slot.
  A completion is a total G-typed assignment preserving every defined
  partial value.  Status.  These are assignment and finite-FV facts only;
  no denotation, α invariance, Γ-erasure, or model-class equivalence is
  assumed.  Nonempty semantic domains do not imply closed Σ-inhabitants.
\<close>

type_synonym 'v named_assignment = "nat \<Rightarrow> 'v option"

definition named_env_typed ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> sgcontext \<Rightarrow> 'v named_assignment \<Rightarrow> bool" where
  "named_env_typed D G g \<longleftrightarrow> (\<forall>n a. g n = Some a \<longrightarrow> a \<in> D (G n))"

definition named_adequate :: "'v named_assignment \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "named_adequate g A \<longleftrightarrow> named_fv A \<subseteq> dom g"

definition named_completion ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> sgcontext \<Rightarrow> 'v named_assignment \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> bool" where
  "named_completion D G g h \<longleftrightarrow>
    paper_global_env_typed D G h \<and> (\<forall>n a. g n = Some a \<longrightarrow> h n = a)"

definition named_complete_with :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'v named_assignment \<Rightarrow> nat \<Rightarrow> 'v" where
  "named_complete_with d g n = (case g n of None \<Rightarrow> d n | Some a \<Rightarrow> a)"

lemma named_env_value:
  assumes typed: "named_env_typed D G g" and assigned: "g n = Some a"
  shows "a \<in> D (G n)"
  using typed assigned unfolding named_env_typed_def by blast

lemma named_completion_typed:
  assumes completion: "named_completion D G g h"
  shows "paper_global_env_typed D G h"
  using completion unfolding named_completion_def by (rule conjunct1)

lemma named_completion_value:
  assumes completion: "named_completion D G g h" and assigned: "g n = Some a"
  shows "h n = a"
  using completion assigned unfolding named_completion_def by blast

lemma named_complete_with_preserves:
  assumes assigned: "g n = Some a"
  shows "named_complete_with d g n = a"
  by (simp add: named_complete_with_def assigned)

lemma named_complete_with_typed:
  assumes partial: "named_env_typed D G g" and defaults: "paper_global_env_typed D G d"
  shows "paper_global_env_typed D G (named_complete_with d g)"
proof (unfold paper_global_env_typed_def, rule allI)
  fix n
  show "named_complete_with d g n \<in> D (G n)"
  proof (cases "g n")
    case None
    show ?thesis using paper_global_env_at[OF defaults, where n=n]
      by (simp add: named_complete_with_def None)
  next
    case (Some a)
    show ?thesis using named_env_value[OF partial Some]
      by (simp add: named_complete_with_def Some)
  qed
qed

theorem named_assignment_completion_exists:
  assumes domains: "\<And>\<sigma>. D \<sigma> \<noteq> {}" and typed: "named_env_typed D G g"
  shows "\<exists>h. named_completion D G g h"
proof -
  obtain d where defaults: "paper_global_env_typed D G d"
    using paper_global_env_exists[where D=D and G=G, OF domains] by (elim exE)
  have total_type: "paper_global_env_typed D G (named_complete_with d g)"
    by (rule named_complete_with_typed[OF typed defaults])
  have preserves: "\<forall>n a. g n = Some a \<longrightarrow> named_complete_with d g n = a"
    by (intro allI impI, rule named_complete_with_preserves, assumption)
  have completion: "named_completion D G g (named_complete_with d g)"
    unfolding named_completion_def by (rule conjI[OF total_type preserves])
  show ?thesis by (rule exI[where x="named_complete_with d g"], rule completion)
qed

lemma named_adequate_value:
  assumes adequate: "named_adequate g A" and member_fv: "n \<in> named_fv A"
  obtains a where "g n = Some a"
proof -
  have member: "n \<in> dom g" using adequate member_fv unfolding named_adequate_def by blast
  have defined: "g n \<noteq> None" using member by (simp add: dom_def)
  obtain a where assigned: "g n = Some a" using defined by (cases "g n") auto
  show thesis by (rule that[OF assigned])
qed

theorem named_completions_agree:
  assumes adequate: "named_adequate g A"
    and first: "named_completion D G g h" and second: "named_completion D G g k"
    and member_fv: "n \<in> named_fv A"
  shows "h n = k n"
proof -
  obtain a where assigned: "g n = Some a" by (rule named_adequate_value[OF adequate member_fv])
  have left: "h n = a" by (rule named_completion_value[OF first assigned])
  have right: "k n = a" by (rule named_completion_value[OF second assigned])
  show ?thesis by (rule trans[OF left sym[OF right]])
qed

section \<open>Updating the variable used by a binder or quantifier\<close>

lemma named_assignment_update_domain:
  "dom (g(n := Some a)) = insert n (dom g)"
  by (auto simp: dom_def)

lemma named_assignment_update_typed:
  assumes typed: "named_env_typed D G g" and member_domain: "a \<in> D (G n)"
  shows "named_env_typed D G (g(n := Some a))"
proof (unfold named_env_typed_def, intro allI impI)
  fix m b
  assume at_m: "(g(n := Some a)) m = Some b"
  show "b \<in> D (G m)"
  proof (cases "m = n")
    case True
    show ?thesis using at_m member_domain by (simp add: True)
  next
    case False
    have original: "g m = Some b" using at_m False by simp
    show ?thesis by (rule named_env_value[OF typed original])
  qed
qed

lemma named_adequate_update:
  assumes adequate: "named_adequate g A"
  shows "named_adequate (g(n := Some a)) A"
  using adequate unfolding named_adequate_def
  by (simp only: named_assignment_update_domain) blast

lemma named_binder_update_adequate_iff:
  "named_adequate (g(n := Some a)) A \<longleftrightarrow> named_adequate g (NLam n A)"
  by (auto simp only: named_adequate_def named_fv.simps named_assignment_update_domain)

lemma named_quantifier_application_adequate:
  assumes adequate: "named_adequate g F"
  shows "named_adequate (g(n := Some a)) (NApp F (NVar n))"
  using adequate unfolding named_adequate_def
  by (auto simp only: named_fv.simps named_assignment_update_domain)

lemma named_update_fresh_agreement:
  assumes fresh: "n \<notin> named_fv F" and member_fv: "m \<in> named_fv F"
  shows "(g(n := Some a)) m = g m"
proof -
  have distinct: "m \<noteq> n" using fresh member_fv by blast
  show ?thesis by (simp add: distinct)
qed

corollary named_binder_update_typed_adequate:
  assumes typed: "named_env_typed D G g" and adequate: "named_adequate g (NLam n A)"
    and member_domain: "a \<in> D (G n)"
  shows "named_env_typed D G (g(n := Some a)) \<and> named_adequate (g(n := Some a)) A"
  by (rule conjI[OF named_assignment_update_typed[OF typed member_domain]
    iffD2[OF named_binder_update_adequate_iff adequate]])

lemma named_complete_with_update:
  "named_complete_with d (g(n := Some a)) = (named_complete_with d g)(n := a)"
  by (rule ext, rename_tac m, case_tac "m = n") (simp_all add: named_complete_with_def)

theorem named_completion_update:
  assumes completion: "named_completion D G g h" and member_domain: "a \<in> D (G n)"
  shows "named_completion D G (g(n := Some a)) (h(n := a))"
proof -
  have original_type: "paper_global_env_typed D G h" by (rule named_completion_typed[OF completion])
  have total_type: "paper_global_env_typed D G (h(n := a))"
  proof (unfold paper_global_env_typed_def, rule allI)
    fix m
    show "(h(n := a)) m \<in> D (G m)"
      using paper_global_env_at[OF original_type, where n=m] member_domain by (cases "m = n") simp_all
  qed
  have preserves: "\<forall>m b. (g(n := Some a)) m = Some b \<longrightarrow> (h(n := a)) m = b"
  proof (intro allI impI)
    fix m b
    assume at_m: "(g(n := Some a)) m = Some b"
    show "(h(n := a)) m = b"
    proof (cases "m = n")
      case True
      show ?thesis using at_m by (simp add: True)
    next
      case False
      have original: "g m = Some b" using at_m False by simp
      show ?thesis using named_completion_value[OF completion original] by (simp add: False)
    qed
  qed
  show ?thesis unfolding named_completion_def by (rule conjI[OF total_type preserves])
qed

text \<open>
  Updating a binder name therefore preserves typing, supplies exactly the
  missing body assignment, and commutes with completion.  Freshness is not
  required for adequacy itself: its distinct role is to leave the
  predicate's already free variable values unchanged.  Any later conclusion
  about denotation must additionally invoke a proved named locality clause.
\<close>

end
