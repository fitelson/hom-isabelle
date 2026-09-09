theory Bacon_Source_Relational_Abstraction_Application
  imports Bacon_Source_Relational_Binary_Lambda_Conversion
    Bacon_Source_Relational_Quasi_Functional_Denotation
begin

section \<open>Application of an arbitrary R abstraction\<close>

text \<open>
  appσ,τ(⟦λn.A⟧g,a)=⟦A⟧g[n↦a], where σ=G(n), A:τ,
  σ∈R and τ≠e. Source: the abstraction/application clauses of
  Definition 3.1, pp.43–44, and Definition 3.3, pp.45–46.

  The body may itself denote a relation of positive arity. The
  original assignment need be adequate only for λn.A, not for A.
  Updating n supplies the missing body value. No freshness condition
  on n, no distinctness of nested binders, and no total completion
  is needed. The proof uses the literal same-variable β contraction
  after evaluating application with a variable witness.
\<close>

lemma paper_R_abstraction_language:
  assumes body: "paper_R_in_language \<Sigma> G A \<tau>"
    and binder_type: "paper_R_type (G n)" and codomain: "\<tau> \<noteq> Ind"
  shows "paper_R_in_language \<Sigma> G (NLam n A) (Arr (G n) \<tau>)"
proof -
  have typed: "paper_R_has_type G A \<tau>" and names: "named_in_signature \<Sigma> A"
    using body unfolding paper_R_in_language_def by blast+
  have abstraction: "paper_R_has_type G (NLam n A) (Arr (G n) \<tau>)"
    by (rule paper_R_has_type.Lam[OF typed binder_type codomain])
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF abstraction]; simp only: named_in_signature.simps; rule names)
qed

context paper_R_bbk_model
begin

theorem paper_R_abstraction_application_denote:
  assumes body: "paper_R_in_language signature stock A \<tau>"
    and binder_type: "paper_R_type (stock n)" and codomain: "\<tau> \<noteq> Ind"
    and typed: "named_env_typed domain stock g"
    and adequate: "named_adequate g (NLam n A)"
    and member: "a \<in> domain (stock n)"
  shows "paper_R_application signature stock domain denote (stock n) \<tau>
      (denote g (NLam n A)) a = denote (g(n := Some a)) A"
proof -
  have abstraction: "paper_R_in_language signature stock (NLam n A) (Arr (stock n) \<tau>)"
    by (rule paper_R_abstraction_language[OF body binder_type codomain])
  have fresh: "n \<notin> named_fv (NLam n A)" by simp
  have witnessed: "paper_R_application signature stock domain denote (stock n) \<tau>
      (denote g (NLam n A)) a =
    denote (g(n := Some a)) (NApp (NLam n A) (NVar n))"
    by (rule paper_R_fresh_application_denote[OF abstraction typed adequate refl fresh member])
  have variable: "paper_R_in_language signature stock (NVar n) (stock n)"
    by (rule paper_R_language_Var[where G=stock and n=n, OF refl binder_type])
  have application: "paper_R_in_language signature stock (NApp (NLam n A) (NVar n)) \<tau>"
    by (rule paper_R_language_App[OF abstraction variable])
  have at: "paper_R_has_type stock (NApp (NLam n A) (NVar n)) \<tau>"
    using application unfolding paper_R_in_language_def by (rule conjunct1)
  have bt: "paper_R_has_type stock A \<tau>"
    using body unfolding paper_R_in_language_def by (rule conjunct1)
  have step: "named_compatible_step named_beta_contract (NApp (NLam n A) (NVar n)) A"
    by (rule named_compatible_step.root, rule paper_R_same_variable_beta)
  have conversion: "paper_R_raw_beta_eta stock \<tau> (NApp (NLam n A) (NVar n)) A"
    by (rule paper_R_raw_beta_eta.Beta[OF at bt step])
  have updated: "named_env_typed domain stock (g(n := Some a))"
    by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed member])
  have app_adequate: "named_adequate (g(n := Some a)) (NApp (NLam n A) (NVar n))"
    by (rule named_quantifier_application_adequate[OF adequate])
  have body_adequate: "named_adequate (g(n := Some a)) A"
    by (rule iffD2[OF named_binder_update_adequate_iff adequate])
  have evaluated: "denote (g(n := Some a)) (NApp (NLam n A) (NVar n)) =
    denote (g(n := Some a)) A"
    by (rule denote_beta_eta[OF conversion application body updated app_adequate body_adequate])
  show ?thesis by (rule trans[OF witnessed evaluated])
qed

end

end
