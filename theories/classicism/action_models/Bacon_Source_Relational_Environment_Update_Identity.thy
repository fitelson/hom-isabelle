theory Bacon_Source_Relational_Environment_Update_Identity
  imports Bacon_Source_Relational_Environment_Update_Syntax
    Bacon_Source_Relational_Environment_Substitution_Typing Bacon_Source_Relational_Application_Identity_Tests
begin

section \<open>Typed closed updates and their literal identity test\<close>

lemma paper_R_closed_term_assignment_update:
  assumes assigned: "paper_R_closed_term_assignment \<Omega> G r"
    and payload: "B \<in> paper_R_closed_terms \<Omega> G (G x)"
  shows "paper_R_closed_term_assignment \<Omega> G (r(x := Some B))"
  using assigned payload unfolding paper_R_closed_term_assignment_def by auto

lemma paper_R_closed_payload_free_for:
  assumes closed: "named_fv B = {}"
  shows "named_free_for B x A"
  by (induction A) (simp_all add: closed)

lemma paper_R_substitution_identity_test_beta:
  assumes fresh: "x \<notin> named_fv L" and closed: "named_fv B = {}"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam x (named_paper_eq \<rho> L K)) B) (named_paper_eq \<rho> L (named_subst x B K))"
proof -
  have free_for: "named_free_for B x (named_paper_eq \<rho> L K)"
    by (rule paper_R_closed_payload_free_for[OF closed])
  have substitution: "named_subst x B (named_paper_eq \<rho> L K) = named_paper_eq \<rho> L (named_subst x B K)"
    by (simp add: named_paper_eq_def named_subst_fresh[OF fresh])
  have contract: "named_beta_contract
    (NApp (NLam x (named_paper_eq \<rho> L K)) B) (named_paper_eq \<rho> L (named_subst x B K))"
    using named_beta_contract.beta[OF free_for] by (simp only: substitution)
  show ?thesis by (rule named_compatible_step.root[where R=named_beta_contract
    and M="NApp (NLam x (named_paper_eq \<rho> L K)) B"
    and N="named_paper_eq \<rho> L (named_subst x B K)", OF contract])
qed

section \<open>One-coordinate representative independence follows from LL\<close>

text \<open>
  If B and C are closed terms of type G(x) and S⊢HᴿB=C,
  then S proves identity of Env(r[x↦B],A) and Env(r[x↦C],A).
  Put K=Env(r[x↦None],A) and L=Env(r[x↦B],A).
  The coordinate x is absent from FV(L). LL with the predicate
  λx.(L=ρK), starting from Ref(L), reduces by literal β to the
  required identity.

  Source role: representative independence in Theorem 3.2, footnote 64,
  p.45. No model or Functionality premise is used. The assignment r
  need not cover all free variables of A; residual open terms are
  permitted, and every replacement remains single-pass and closed.
\<close>

theorem paper_R_environment_subst_update_identity:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Omega> G A \<rho>"
    and assigned: "paper_R_closed_term_assignment \<Omega> G r"
    and left: "B \<in> paper_R_closed_terms \<Omega> G (G x)"
    and right: "C \<in> paper_R_closed_terms \<Omega> G (G x)"
    and equality: "paper_R_named_derivable \<Omega> G S (named_paper_eq (G x) B C)"
  shows "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
    (paper_R_environment_subst (r(x := Some B)) A) (paper_R_environment_subst (r(x := Some C)) A))"
proof -
  let ?K = "paper_R_environment_subst (r(x := None)) A"
  let ?L = "paper_R_environment_subst (r(x := Some B)) A"
  let ?R = "paper_R_environment_subst (r(x := Some C)) A"
  let ?Test = "NLam x (named_paper_eq \<rho> ?L ?K)"
  have closed: "named_fv E = {}" if "r n = Some E" for n E
    by (rule paper_R_closed_terms_closed[OF paper_R_closed_term_assignmentD[OF assigned that]])
  have bc: "named_fv B = {}" by (rule paper_R_closed_terms_closed[OF left])
  have cc: "named_fv C = {}" by (rule paper_R_closed_terms_closed[OF right])
  have bl: "paper_R_in_language \<Omega> G B (G x)" by (rule paper_R_closed_terms_language[OF left])
  have cl: "paper_R_in_language \<Omega> G C (G x)" by (rule paper_R_closed_terms_language[OF right])
  have rt: "paper_R_type (G x)" by (rule paper_R_language_result_type[OF bl])
  have kl: "paper_R_in_language \<Omega> G ?K \<rho>"
    by (rule paper_R_environment_subst_language[OF language paper_R_closed_term_assignment_delete[OF assigned]])
  have ll: "paper_R_in_language \<Omega> G ?L \<rho>"
    by (rule paper_R_environment_subst_language[OF language paper_R_closed_term_assignment_update[OF assigned left]])
  have rl: "paper_R_in_language \<Omega> G ?R \<rho>"
    by (rule paper_R_environment_subst_language[OF language paper_R_closed_term_assignment_update[OF assigned right]])
  have updated_closed: "named_fv E = {}" if "(r(x := Some B)) n = Some E" for n E
    by (rule paper_R_environment_closed_update[OF closed bc that])
  have free_variables: "named_fv ?L = named_fv A - dom (r(x := Some B))"
    by (rule paper_R_environment_subst_fv[OF updated_closed])
  have defined: "x \<in> dom (r(x := Some B))" by (simp add: dom_def)
  have fresh: "x \<notin> named_fv ?L" using free_variables defined by blast
  have body: "paper_R_in_language \<Omega> G (named_paper_eq \<rho> ?L ?K) Prop"
    by (rule paper_R_named_identity_language[OF ll kl])
  have predicate: "paper_R_in_language \<Omega> G ?Test (Arr (G x) Prop)"
    by (rule paper_R_named_identity_test_language[OF body rt])
  have left_update: "?L = named_subst x B ?K" by (rule paper_R_environment_subst_update_closed[OF closed bc])
  have right_update: "?R = named_subst x C ?K" by (rule paper_R_environment_subst_update_closed[OF closed cc])
  have first_step: "named_compatible_step named_beta_contract (NApp ?Test B) (named_paper_eq \<rho> ?L ?L)"
    using paper_R_substitution_identity_test_beta[where K="?K" and \<rho>=\<rho>, OF fresh bc]
    by (simp only: left_update[symmetric])
  have second_step: "named_compatible_step named_beta_contract (NApp ?Test C) (named_paper_eq \<rho> ?L ?R)"
    using paper_R_substitution_identity_test_beta[where K="?K" and \<rho>=\<rho>, OF fresh cc]
    by (simp only: right_update[symmetric])
  have reflexive: "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho> ?L ?L)"
    by (rule paper_R_named_identity_refl[OF ll])
  show ?thesis by (rule paper_R_named_derivable_LL_beta[OF rich bl cl predicate
    paper_R_named_identity_language[OF ll ll] paper_R_named_identity_language[OF ll rl]
    first_step second_step equality reflexive])
qed

end
