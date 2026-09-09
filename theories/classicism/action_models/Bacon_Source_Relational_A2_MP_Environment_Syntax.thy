theory Bacon_Source_Relational_A2_MP_Environment_Syntax
  imports Bacon_Source_Relational_Closed_Identity_Vector
begin

section \<open>Raw environment equations for the explicit MP test context\<close>

lemma paper_R_environment_lam_vec_inactive:
  assumes inactive: "\<And>n. n \<in> set ns \<Longrightarrow> r n = None"
  shows "paper_R_environment_subst r (named_lam_vec ns A) =
    named_lam_vec ns (paper_R_environment_subst r A)"
  using inactive
proof (induction ns)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  have none: "r n = None" by (rule Cons.prems; simp)
  have deletion: "r(n := None) = r" by (rule ext; auto simp: none)
  have tail: "r m = None" if "m \<in> set ns" for m by (rule Cons.prems; use that in simp)
  show ?case by (simp only: named_lam_vec.simps paper_R_environment_subst.simps deletion Cons.IH[OF tail])
qed

lemma paper_R_environment_app_vec:
  "paper_R_environment_subst r (named_app_vec F As) =
    named_app_vec (paper_R_environment_subst r F) (map (paper_R_environment_subst r) As)"
  by (induction As arbitrary: F) simp_all

lemma paper_R_environment_inactive_fixed:
  assumes inactive: "\<And>n. n \<in> named_fv A \<Longrightarrow> r n = None"
  shows "paper_R_environment_subst r A = A"
proof -
  have equality: "paper_R_environment_subst r A = paper_R_environment_subst Map.empty A"
    by (rule paper_R_environment_subst_locality; simp only: inactive; simp)
  show ?thesis using equality by (simp only: paper_R_environment_subst_empty)
qed

lemma paper_R_environment_vector_variables:
  assumes inactive: "\<And>n. n \<in> set ns \<Longrightarrow> r n = None"
  shows "map (paper_R_environment_subst r) (map NVar ns) = map NVar ns"
  using inactive
proof (induction ns)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  have head: "r n = None" by (rule Cons.prems; simp)
  have tail: "r m = None" if "m \<in> set ns" for m by (rule Cons.prems; use that in simp)
  show ?case by (simp only: list.map paper_R_environment_subst.simps head option.case Cons.IH[OF tail])
qed

text \<open>
  The test is λv⃗.(P∨(Xv⃗∧Yv⃗)). Coordinates x,y are
  distinct and absent from the prefix; FV(P) is covered by the prefix.
  Substituting K,L for these coordinates therefore leaves P and the
  displayed argument variables unchanged. These are raw single-pass
  equations; later proof transport separately requires K,L to be closed.
  Source role: the explicit MP context of Appendix A.2, p.66.
\<close>

theorem paper_R_A2_MP_environment_evaluation:
  assumes distinct: "x \<noteq> y" and fresh_x: "x \<notin> set ns" and fresh_y: "y \<notin> set ns"
    and covered: "named_fv P \<subseteq> set ns"
  shows "paper_R_environment_subst ((Map.empty(x := Some K))(y := Some L))
      (named_lam_vec ns (named_paper_or P
        (named_paper_and (named_app_vec (NVar x) (map NVar ns)) (named_app_vec (NVar y) (map NVar ns))))) =
    named_lam_vec ns (named_paper_or P
      (named_paper_and (named_app_vec K (map NVar ns)) (named_app_vec L (map NVar ns))))"
proof -
  let ?r = "(Map.empty(x := Some K))(y := Some L)"
  have inactive: "?r n = None" if "n \<in> set ns" for n
    using that fresh_x fresh_y by auto
  have fixed_P: "paper_R_environment_subst ?r P = P"
    by (rule paper_R_environment_inactive_fixed; rule inactive; use covered in blast)
  have fixed_arguments: "map (paper_R_environment_subst ?r) (map NVar ns) = map NVar ns"
    by (rule paper_R_environment_vector_variables[OF inactive])
  show ?thesis by (simp only: paper_R_environment_lam_vec_inactive[OF inactive]
    named_paper_or_def named_paper_and_def paper_R_environment_subst.simps
    fixed_P paper_R_environment_app_vec fixed_arguments; simp add: distinct)
qed

end
