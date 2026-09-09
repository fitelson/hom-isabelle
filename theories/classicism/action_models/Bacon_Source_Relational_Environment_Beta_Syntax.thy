theory Bacon_Source_Relational_Environment_Beta_Syntax
  imports Bacon_Source_Relational_Environment_Substitution
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Deletion of inactive entries and closed payloads\<close>

lemma paper_R_environment_closed_delete:
  assumes closed: "\<And>m B. r m = Some B \<Longrightarrow> named_fv B = {}"
    and assigned: "(r(n := None)) m = Some B"
  shows "named_fv B = {}"
proof -
  have old: "r m = Some B" using assigned by (auto split: if_splits)
  show ?thesis by (rule closed[OF old])
qed

lemma paper_R_environment_delete_commute:
  "(r(x := None))(y := None) = (r(y := None))(x := None)"
  by (rule ext; auto)

lemma paper_R_environment_subst_delete_fresh:
  assumes fresh: "x \<notin> named_fv A"
  shows "paper_R_environment_subst (r(x := None)) A = paper_R_environment_subst r A"
proof (rule paper_R_environment_subst_locality)
  fix n
  assume free: "n \<in> named_fv A"
  have different: "n \<noteq> x" using fresh free by blast
  show "(r(x := None)) n = r n" by (simp add: different)
qed

lemma paper_R_environment_subst_fv_subset:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
  shows "named_fv (paper_R_environment_subst r A) \<subseteq> named_fv A"
  by (simp only: paper_R_environment_subst_fv[OF closed]; rule Diff_subset)

section \<open>Exact interchange with literal free-for substitution\<close>

text \<open>
  A[N/x][r]=(A[r with x deleted])[N[r]/x]. Every assigned payload
  is closed, but unassigned variables need not disappear. At λy with
  y≠x the source free-for guard permits either y∉FV(N) or x∉FV(A).
  The proof treats both branches, rather than imposing a stronger guard.
  Source: Figure 2, p.8, and the representative substitution in n.64,
  p.45. No typing, completion, α renaming or semantic premise is used.
\<close>

theorem paper_R_environment_subst_beta_commute:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
    and permitted: "named_free_for N x A"
  shows "paper_R_environment_subst r (named_subst x N A) =
    named_subst x (paper_R_environment_subst r N) (paper_R_environment_subst (r(x := None)) A)"
  using permitted closed
proof (induction A arbitrary: r)
  case (NVar n)
  show ?case
  proof (cases "n = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    note different = False
    show ?thesis
    proof (cases "r n")
      case None
      show ?thesis by (simp add: different None)
    next
      case (Some B)
      have empty: "named_fv B = {}" by (rule NVar.prems(2)[OF Some])
      have fresh: "x \<notin> named_fv B" by (simp only: empty; simp)
      have fixed: "named_subst x (paper_R_environment_subst r N) B = B" by (rule named_subst_fresh[OF fresh])
      show ?thesis by (simp add: different Some fixed)
    qed
  qed
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "named_free_for N x F" and af: "named_free_for N x A" using NApp.prems(1) by simp_all
  show ?case by (simp only: named_subst.simps paper_R_environment_subst.simps
    NApp.IH(1)[OF ff NApp.prems(2)] NApp.IH(2)[OF af NApp.prems(2)])
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis by (simp only: True named_subst.simps paper_R_environment_subst.simps fun_upd_upd if_True simp_thms)
  next
    case False
    note different = False
    have af: "named_free_for N x A" and guard: "y \<notin> named_fv N \<or> x \<notin> named_fv A"
      using NLam.prems(1) different by auto
    have body_closed: "\<And>n B. (r(y := None)) n = Some B \<Longrightarrow> named_fv B = {}"
      by (rule paper_R_environment_closed_delete[where r=r and n=y, OF NLam.prems(2)]; assumption)
    have commute: "(r(x := None))(y := None) = (r(y := None))(x := None)"
      by (rule paper_R_environment_delete_commute)
    show ?thesis
    proof (cases "y \<notin> named_fv N")
      case True
      have argument_same: "paper_R_environment_subst (r(y := None)) N = paper_R_environment_subst r N"
        by (rule paper_R_environment_subst_delete_fresh[OF True])
      have body_equation: "paper_R_environment_subst (r(y := None)) (named_subst x N A) =
        named_subst x (paper_R_environment_subst (r(y := None)) N)
          (paper_R_environment_subst ((r(y := None))(x := None)) A)"
        by (rule NLam.IH[OF af body_closed])
      show ?thesis by (simp only: named_subst.simps different if_False paper_R_environment_subst.simps
        body_equation argument_same commute)
    next
      case False
      have absent: "x \<notin> named_fv A" using guard False by blast
      have original_fixed: "named_subst x N A = A" by (rule named_subst_fresh[OF absent])
      have deletion_removed: "paper_R_environment_subst ((r(x := None))(y := None)) A =
          paper_R_environment_subst (r(y := None)) A"
        by (simp only: commute; rule paper_R_environment_subst_delete_fresh[OF absent])
      have support: "named_fv (paper_R_environment_subst (r(y := None)) A) \<subseteq> named_fv A"
        by (rule paper_R_environment_subst_fv_subset; rule body_closed; assumption)
      have result_fresh: "x \<notin> named_fv (paper_R_environment_subst (r(y := None)) A)"
        using support absent by blast
      have result_fixed: "named_subst x (paper_R_environment_subst r N)
          (paper_R_environment_subst (r(y := None)) A) = paper_R_environment_subst (r(y := None)) A"
        by (rule named_subst_fresh[OF result_fresh])
      show ?thesis by (simp only: named_subst.simps different if_False paper_R_environment_subst.simps
        original_fixed deletion_removed result_fixed)
    qed
  qed
qed

end
