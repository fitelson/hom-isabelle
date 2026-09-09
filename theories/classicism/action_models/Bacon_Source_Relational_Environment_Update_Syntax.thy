theory Bacon_Source_Relational_Environment_Update_Syntax
  imports Bacon_Source_Relational_Environment_Beta_Syntax
begin

section \<open>A single closed payload is inserted after deleting its coordinate\<close>

text \<open>
  Env(r[x↦B],A) = (Env(r[x↦None],A))[B/x].
  Source role: independence of representative choices in Theorem 3.2,
  footnote 64, p.45. All assigned payloads and B are closed.

  Apply the already proved literal substitution interchange to
  A[x/x]=A and the updated assignment. Its x-payload is exactly B.
  This retains deletion under repeated binders and single-pass payload
  insertion. No typing, adequacy, derivability or model premise is needed.
\<close>

lemma paper_R_environment_closed_update:
  assumes closed: "\<And>n C. r n = Some C \<Longrightarrow> named_fv C = {}"
    and payload: "named_fv B = {}" and assigned: "(r(x := Some B)) n = Some C"
  shows "named_fv C = {}"
proof (cases "n = x")
  case True
  have same: "C = B" using assigned by (simp add: True)
  show ?thesis by (simp only: same; rule payload)
next
  case False
  have old: "r n = Some C" using assigned by (simp add: False)
  show ?thesis by (rule closed[OF old])
qed

theorem paper_R_environment_subst_update_closed:
  assumes closed: "\<And>n C. r n = Some C \<Longrightarrow> named_fv C = {}" and payload: "named_fv B = {}"
  shows "paper_R_environment_subst (r(x := Some B)) A =
    named_subst x B (paper_R_environment_subst (r(x := None)) A)"
proof -
  have updated_closed: "named_fv C = {}" if "(r(x := Some B)) n = Some C" for n C
    by (rule paper_R_environment_closed_update[OF closed payload that])
  have interchange:
    "paper_R_environment_subst (r(x := Some B)) (named_subst x (NVar x) A) =
      named_subst x (paper_R_environment_subst (r(x := Some B)) (NVar x))
        (paper_R_environment_subst ((r(x := Some B))(x := None)) A)"
    by (rule paper_R_environment_subst_beta_commute[OF updated_closed named_free_for_same_variable])
  show ?thesis using interchange
    by (simp only: named_subst_same_variable paper_R_environment_subst.simps fun_upd_same option.case fun_upd_upd)
qed

end
