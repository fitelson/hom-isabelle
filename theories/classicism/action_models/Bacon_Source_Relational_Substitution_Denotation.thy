theory Bacon_Source_Relational_Substitution_Denotation
  imports Bacon_Source_Relational_Substitution_Syntax Bacon_Source_Relational_Abstraction_Application
begin

section \<open>Substitution under a typed partial assignment\<close>

text \<open>
  ⟦A[B/n]⟧g = ⟦A⟧g[n↦⟦B⟧g] when B is free for n in A.
  The original g covers FV(A)−{n} and FV(B); it need not assign n.
  Source role: Definition 3.1(ii.a–d), pp.43–44, and the finite
  naming construction in p.51 n.73.

  For a nonindividual result this follows from actual β conversion and
  abstraction application. At result e, the R grammar permits only a
  variable or constant, and these are handled directly. No forbidden
  abstraction returning e, Functionality, assignment completion, F model,
  proof judgment, or completeness theorem is used.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_substitution_denote_nonindividual:
  assumes body: "paper_R_in_language signature stock A \<tau>"
    and payload: "paper_R_in_language signature stock B (stock n)"
    and typed: "named_env_typed domain stock g"
    and body_coverage: "named_fv A - {n} \<subseteq> dom g"
    and payload_adequate: "named_adequate g B"
    and free_for: "named_free_for B n A" and result: "\<tau> \<noteq> Ind"
  shows "denote g (named_subst n B A) = denote (g(n := Some (denote g B))) A"
proof -
  have binder_type: "paper_R_type (stock n)" by (rule paper_R_language_result_type[OF payload])
  have abstraction: "paper_R_in_language signature stock (NLam n A) (Arr (stock n) \<tau>)"
    by (rule paper_R_abstraction_language[OF body binder_type result])
  have abstraction_adequate: "named_adequate g (NLam n A)"
    using body_coverage by (simp only: named_adequate_def named_fv.simps)
  have application: "paper_R_in_language signature stock (NApp (NLam n A) B) \<tau>"
    by (rule paper_R_language_App[OF abstraction payload])
  have application_adequate: "named_adequate g (NApp (NLam n A) B)"
    using abstraction_adequate payload_adequate unfolding named_adequate_def by auto
  have substituted: "paper_R_in_language signature stock (named_subst n B A) \<tau>"
    by (rule paper_R_subst_language_pure[OF body payload])
  have substituted_adequate: "named_adequate g (named_subst n B A)"
    using named_subst_fv_upper[where x=n and B=B and A=A] body_coverage payload_adequate
    unfolding named_adequate_def by blast
  have application_type: "paper_R_has_type stock (NApp (NLam n A) B) \<tau>"
    and substituted_type: "paper_R_has_type stock (named_subst n B A) \<tau>"
    using application substituted unfolding paper_R_in_language_def by blast+
  have contraction: "named_compatible_step named_beta_contract (NApp (NLam n A) B) (named_subst n B A)"
    by (rule named_compatible_step.root, rule named_beta_contract.beta[OF free_for])
  have conversion: "paper_R_raw_beta_eta stock \<tau> (NApp (NLam n A) B) (named_subst n B A)"
    by (rule paper_R_raw_beta_eta.Beta[OF application_type substituted_type contraction])
  have beta_value: "denote g (NApp (NLam n A) B) = denote g (named_subst n B A)"
    by (rule denote_beta_eta[OF conversion application substituted typed application_adequate substituted_adequate])
  have app_value: "paper_R_application signature stock domain denote (stock n) \<tau>
      (denote g (NLam n A)) (denote g B) = denote g (NApp (NLam n A) B)"
    by (rule paper_R_application_denote[OF abstraction payload typed application_adequate])
  have payload_member: "denote g B \<in> domain (stock n)"
    by (rule denote_type[OF payload typed payload_adequate])
  have body_value: "paper_R_application signature stock domain denote (stock n) \<tau>
      (denote g (NLam n A)) (denote g B) = denote (g(n := Some (denote g B))) A"
    by (rule paper_R_abstraction_application_denote[
      OF body binder_type result typed abstraction_adequate payload_member])
  show ?thesis using beta_value app_value body_value by simp
qed

theorem paper_R_substitution_denote:
  assumes body: "paper_R_in_language signature stock A \<tau>"
    and payload: "paper_R_in_language signature stock B (stock n)"
    and typed: "named_env_typed domain stock g"
    and body_coverage: "named_fv A - {n} \<subseteq> dom g"
    and payload_adequate: "named_adequate g B" and free_for: "named_free_for B n A"
  shows "denote g (named_subst n B A) = denote (g(n := Some (denote g B))) A"
proof (cases "\<tau> = Ind")
  case False
  show ?thesis by (rule paper_R_substitution_denote_nonindividual[
    OF body payload typed body_coverage payload_adequate free_for False])
next
  case True
  let ?k = "g(n := Some (denote g B))"
  have payload_member: "denote g B \<in> domain (stock n)"
    by (rule denote_type[OF payload typed payload_adequate])
  have updated: "named_env_typed domain stock ?k"
    by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed payload_member])
  have individual: "paper_R_has_type stock A Ind"
    using body True unfolding paper_R_in_language_def by blast
  consider (variable) m where "A = NVar m" "stock m = Ind"
    | (declared) c where "A = NConst c Ind"
    using paper_R_individual_term_shape[OF individual] by blast
  then show ?thesis
  proof cases
    case (variable m)
    show ?thesis
    proof (cases "m = n")
      case True
      have variable_value: "denote ?k (NVar n) = denote g B"
        by (rule denote_var[OF updated]) simp
      show ?thesis by (simp only: variable(1) True named_subst.simps simp_thms if_True variable_value)
    next
      case False
      have covered: "m \<in> dom g" using body_coverage variable(1) False by auto
      obtain a where assigned: "g m = Some a" using covered by (cases "g m") auto
      have unchanged: "?k m = Some a" using assigned False by simp
      have first: "denote g (NVar m) = a" by (rule denote_var[OF typed assigned])
      have second: "denote ?k (NVar m) = a" by (rule denote_var[OF updated unchanged])
      show ?thesis by (simp only: variable(1) named_subst.simps False if_False first second)
    qed
  next
    case (declared c)
    have first_adequate: "named_adequate g A" and second_adequate: "named_adequate ?k A"
      by (simp_all only: declared named_adequate_def named_fv.simps empty_subsetI)
    have same: "denote g A = denote ?k A"
    proof (rule denote_locality[OF body typed updated first_adequate second_adequate])
      fix m
      assume "m \<in> named_fv A"
      then show "g m = ?k m" by (simp only: declared named_fv.simps empty_iff)
    qed
    show ?thesis using same by (simp only: declared named_subst.simps)
  qed
qed

corollary paper_R_substitution_denote_binder_adequate:
  assumes body: "paper_R_in_language signature stock A \<tau>"
    and payload: "paper_R_in_language signature stock B (stock n)"
    and typed: "named_env_typed domain stock g"
    and body_adequate: "named_adequate g (NLam n A)"
    and payload_adequate: "named_adequate g B" and free_for: "named_free_for B n A"
  shows "denote g (named_subst n B A) = denote (g(n := Some (denote g B))) A"
proof (rule paper_R_substitution_denote[OF body payload typed _ payload_adequate free_for])
  show "named_fv A - {n} \<subseteq> dom g" using body_adequate
    by (simp only: named_adequate_def named_fv.simps)
qed

end

end
