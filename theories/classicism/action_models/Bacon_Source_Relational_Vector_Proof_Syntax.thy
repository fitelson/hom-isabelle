theory Bacon_Source_Relational_Vector_Proof_Syntax
  imports Bacon_Source_Relational_Binder_Vectors Bacon_Source_Relational_Conversion_Identity
begin

section \<open>Native R typing and compatible steps for application vectors\<close>

lemma paper_R_named_lam_vec_append:
  "named_lam_vec (xs @ ys) A = named_lam_vec xs (named_lam_vec ys A)"
  by (induction xs) simp_all

lemma paper_R_named_app_vec_compatible:
  assumes step: "named_compatible_step R F H"
  shows "named_compatible_step R (named_app_vec F As) (named_app_vec H As)"
  using step
proof (induction As arbitrary: F H)
  case Nil
  show ?case by (simp only: named_app_vec.simps; rule Nil.prems)
next
  case (Cons A As)
  have head: "named_compatible_step R (NApp F A) (NApp H A)"
    by (rule named_compatible_step.App_left[OF Cons.prems])
  show ?case by (simp only: named_app_vec.simps; rule Cons.IH[OF head])
qed

lemma paper_R_named_app_vec_language:
  assumes arguments: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) As \<sigma>s"
    and head: "paper_R_in_language \<Sigma> G F (paper_type_vector \<sigma>s \<tau>)"
  shows "paper_R_in_language \<Sigma> G (named_app_vec F As) \<tau>"
  using arguments head
proof (induction As arbitrary: \<sigma>s F)
  case Nil
  have types: "\<sigma>s = []" using Nil.prems(1) by simp
  show ?case using Nil.prems(2) by (simp only: types paper_type_vector.simps named_app_vec.simps)
next
  case (Cons A As)
  obtain \<sigma> \<rho>s where types: "\<sigma>s = \<sigma>#\<rho>s" using Cons.prems(1) by (cases \<sigma>s) auto
  have argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and rest: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) As \<rho>s"
    using Cons.prems(1) by (simp_all add: types)
  have head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> (paper_type_vector \<rho>s \<tau>))"
    using Cons.prems(2) by (simp only: types paper_type_vector.simps)
  have applied: "paper_R_in_language \<Sigma> G (NApp F A) (paper_type_vector \<rho>s \<tau>)"
    by (rule paper_R_language_App[OF head argument])
  show ?case by (simp only: named_app_vec.simps; rule Cons.IH[OF rest applied])
qed

lemma paper_R_named_vector_variables_language:
  assumes binders: "list_all paper_R_type (map G ns)"
  shows "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) (map NVar ns) (map G ns)"
  using binders
proof (induction ns)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  have nr: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)" using Cons.prems by simp_all
  have variable: "paper_R_in_language \<Sigma> G (NVar n) (G n)"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF refl nr])
  show ?case using variable Cons.IH[OF tail] by simp
qed

section \<open>Self-application recovers the body through R-typed β steps\<close>

text \<open>
  (λn₁…nₖ.A)n₁…nₖ ≡β A. Each root substitutes a variable
  for itself, so the literal free-for condition holds even with repeated
  names. Every intermediate type is checked in R. The nonindividual
  result guard permits the displayed abstractions; it is automatic
  when A itself is an abstraction of a proposition.
  Source: Figure 2 and the vector manipulations of Appendix A.2–A.3.
  Only the raw named vector definitions, not their F-conversion theorem,
  are reused.
\<close>

theorem paper_R_named_lam_vec_self_beta:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
    and binders: "list_all paper_R_type (map G ns)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_raw_beta_eta G \<tau> (named_app_vec (named_lam_vec ns A) (map NVar ns)) A"
  using binders
proof (induction ns)
  case Nil
  have typed: "paper_R_has_type G A \<tau>" using language unfolding paper_R_in_language_def by (rule conjunct1)
  show ?case by (simp only: named_app_vec.simps named_lam_vec.simps list.map; rule paper_R_raw_beta_eta.Refl[OF typed])
next
  case (Cons n ns)
  let ?T = "paper_type_vector (map G ns) \<tau>"
  let ?L = "named_lam_vec ns A"
  let ?R = "NApp (NLam n ?L) (NVar n)"
  have nr: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)" using Cons.prems by simp_all
  have inner: "paper_R_in_language \<Sigma> G ?L ?T" by (rule paper_R_named_lam_vec_language[OF language tail result])
  have outer: "paper_R_in_language \<Sigma> G (NLam n ?L) (Arr (G n) ?T)"
    using paper_R_named_lam_vec_language[OF language Cons.prems result] by simp
  have variable: "paper_R_in_language \<Sigma> G (NVar n) (G n)"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF refl nr])
  have redex: "paper_R_in_language \<Sigma> G ?R ?T" by (rule paper_R_language_App[OF outer variable])
  have root: "named_beta_contract ?R ?L"
    using named_beta_contract.beta[OF named_free_for_same_variable, where x=n and A="?L"]
    by (simp only: named_subst_same_variable)
  have step: "named_compatible_step named_beta_contract ?R ?L"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="?R" and N="?L", OF root])
  have lifted: "named_compatible_step named_beta_contract
    (named_app_vec ?R (map NVar ns)) (named_app_vec ?L (map NVar ns))"
    by (rule paper_R_named_app_vec_compatible[OF step])
  have arguments: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) (map NVar ns) (map G ns)"
    by (rule paper_R_named_vector_variables_language[OF tail])
  have left_language: "paper_R_in_language \<Sigma> G (named_app_vec ?R (map NVar ns)) \<tau>"
    by (rule paper_R_named_app_vec_language[OF arguments redex])
  have right_language: "paper_R_in_language \<Sigma> G (named_app_vec ?L (map NVar ns)) \<tau>"
    by (rule paper_R_named_app_vec_language[OF arguments inner])
  have lt: "paper_R_has_type G (named_app_vec ?R (map NVar ns)) \<tau>"
    and rt: "paper_R_has_type G (named_app_vec ?L (map NVar ns)) \<tau>"
    using left_language right_language unfolding paper_R_in_language_def by blast+
  have first: "paper_R_raw_beta_eta G \<tau> (named_app_vec ?R (map NVar ns)) (named_app_vec ?L (map NVar ns))"
    by (rule paper_R_raw_beta_eta.Beta[OF lt rt lifted])
  show ?case by (simp only: named_lam_vec.simps named_app_vec.simps list.map;
    rule paper_R_raw_beta_eta.Trans[OF first Cons.IH[OF tail]])
qed

theorem paper_R_named_H_lam_vec_self_identity:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A \<tau>"
    and binders: "list_all paper_R_type (map G ns)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq \<tau> (named_app_vec (named_lam_vec ns A) (map NVar ns)) A)"
proof -
  have redex: "paper_R_in_language \<Sigma> G (named_app_vec (named_lam_vec ns A) (map NVar ns)) \<tau>"
    by (rule paper_R_named_app_vec_language[OF paper_R_named_vector_variables_language[OF binders]
      paper_R_named_lam_vec_language[OF language binders result]])
  show ?thesis by (rule paper_R_named_H_raw_conversion_identity[
    OF rich paper_R_named_lam_vec_self_beta[OF language binders result] redex language])
qed

end
