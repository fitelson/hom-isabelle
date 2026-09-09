theory Bacon_Source_Relational_Binder_Truth
  imports Bacon_Source_Relational_Binary_Lambda_Conversion
begin

section \<open>Self-application of a named R abstraction\<close>

text \<open>
  For A:t and n:σ with σ∈R, (λn.A)n →β A. The substitution
  replaces n by itself, so it is free-for even with shadowed binders.
  Under g[n↦a], both sides are adequate when g is adequate for λn.A.
  Source: Figure 2, p.8, and Definition 3.1(ii.d), p.44.

  The explicit R binder-type guard matters: R-richness alone does not
  say that every ambient name has an R type. Neither original adequacy
  for A nor a value for n in g is required. No total completion,
  arbitrary-substitution theorem, α rule or F model is used.
\<close>

lemma paper_R_binder_formula_language:
  assumes body: "paper_R_in_language \<Sigma> G A Prop" and rt: "paper_R_type (G n)"
  shows "paper_R_in_language \<Sigma> G (NLam n A) (Arr (G n) Prop)"
proof -
  have bt: "paper_R_has_type G A Prop" and bs: "named_in_signature \<Sigma> A"
    using body unfolding paper_R_in_language_def by blast+
  have lt: "paper_R_has_type G (NLam n A) (Arr (G n) Prop)"
    by (rule paper_R_has_type.Lam[OF bt rt]; simp)
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF lt]; simp only: named_in_signature.simps; rule bs)
qed

context paper_R_bbk_model
begin

lemma paper_R_binder_self_application:
  assumes body: "paper_R_in_language signature stock A Prop"
    and rt: "paper_R_type (stock n)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g (NLam n A)"
    and member: "a \<in> domain (stock n)"
  shows "denote (g(n := Some a)) (NApp (NLam n A) (NVar n)) = denote (g(n := Some a)) A"
proof -
  have predicate: "paper_R_in_language signature stock (NLam n A) (Arr (stock n) Prop)"
    by (rule paper_R_binder_formula_language[OF body rt])
  have variable: "paper_R_in_language signature stock (NVar n) (stock n)"
    by (rule paper_R_language_Var[where G=stock and n=n, OF refl rt])
  have application: "paper_R_in_language signature stock (NApp (NLam n A) (NVar n)) Prop"
    by (rule paper_R_language_App[OF predicate variable])
  have at: "paper_R_has_type stock (NApp (NLam n A) (NVar n)) Prop"
    using application unfolding paper_R_in_language_def by (rule conjunct1)
  have bt: "paper_R_has_type stock A Prop"
    using body unfolding paper_R_in_language_def by (rule conjunct1)
  have step: "named_compatible_step named_beta_contract (NApp (NLam n A) (NVar n)) A"
    by (rule named_compatible_step.root, rule paper_R_same_variable_beta)
  have conversion: "paper_R_raw_beta_eta stock Prop (NApp (NLam n A) (NVar n)) A"
    by (rule paper_R_raw_beta_eta.Beta[OF at bt step])
  have updated: "named_env_typed domain stock (g(n := Some a))"
    by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed member])
  have app_adequate: "named_adequate (g(n := Some a)) (NApp (NLam n A) (NVar n))"
    by (rule named_quantifier_application_adequate[OF adequate])
  have body_adequate: "named_adequate (g(n := Some a)) A"
    by (rule iffD2[OF named_binder_update_adequate_iff adequate])
  show ?thesis by (rule denote_beta_eta[OF conversion application body updated app_adequate body_adequate])
qed

section \<open>Universal and existential binder truth under partial assignments\<close>

text \<open>
  ⟦∀σ(λn.A)⟧ᵍ is true iff ⟦A⟧ᵍ⁽ⁿ↦ᵃ⁾ is true for every
  a∈Dσ; for ∃σ the corresponding condition uses some a∈Dσ.
  Source: Definition 3.1(iii.d–e), p.44.

  The fresh test variable in those clauses is n itself: n is never
  free in λn.A. The preceding self-application lemma removes the
  application after the update. These are independent R model laws,
  suitable for Gen and Inst; they assert no R proof soundness yet.
\<close>

theorem paper_R_forall_binder_truth:
  assumes body: "paper_R_in_language signature stock A Prop"
    and nt: "stock n = \<sigma>" and rt: "paper_R_type \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g (NLam n A)"
  shows "valuation (denote g (named_paper_all \<sigma> (NLam n A))) =
    (\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) A))"
proof -
  have nr: "paper_R_type (stock n)" by (simp only: nt; rule rt)
  have predicate: "paper_R_in_language signature stock (NLam n A) (Arr \<sigma> Prop)"
    using paper_R_binder_formula_language[OF body nr] by (simp only: nt)
  have fresh: "n \<notin> named_fv (NLam n A)" by simp
  have source_truth: "valuation (denote g (named_paper_all \<sigma> (NLam n A))) =
      (\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp (NLam n A) (NVar n))))"
    unfolding named_paper_all_def by (rule valuation_forall[OF predicate typed adequate nt fresh])
  have instances: "(\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp (NLam n A) (NVar n)))) =
      (\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) A))"
  proof (rule ball_cong[OF refl])
    fix a
    assume am: "a \<in> domain \<sigma>"
    have an: "a \<in> domain (stock n)" using am by (simp only: nt)
    have same: "denote (g(n := Some a)) (NApp (NLam n A) (NVar n)) = denote (g(n := Some a)) A"
      by (rule paper_R_binder_self_application[OF body nr typed adequate an])
    show "valuation (denote (g(n := Some a)) (NApp (NLam n A) (NVar n))) =
        valuation (denote (g(n := Some a)) A)" by (rule arg_cong[OF same])
  qed
  show ?thesis by (rule trans[OF source_truth instances])
qed

theorem paper_R_exists_binder_truth:
  assumes body: "paper_R_in_language signature stock A Prop"
    and nt: "stock n = \<sigma>" and rt: "paper_R_type \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g (NLam n A)"
  shows "valuation (denote g (named_paper_ex \<sigma> (NLam n A))) =
    (\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) A))"
proof -
  have nr: "paper_R_type (stock n)" by (simp only: nt; rule rt)
  have predicate: "paper_R_in_language signature stock (NLam n A) (Arr \<sigma> Prop)"
    using paper_R_binder_formula_language[OF body nr] by (simp only: nt)
  have fresh: "n \<notin> named_fv (NLam n A)" by simp
  have source_truth: "valuation (denote g (named_paper_ex \<sigma> (NLam n A))) =
      (\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp (NLam n A) (NVar n))))"
    unfolding named_paper_ex_def by (rule valuation_exists[OF predicate typed adequate nt fresh])
  have instances: "(\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp (NLam n A) (NVar n)))) =
      (\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) A))"
  proof (rule bex_cong[OF refl])
    fix a
    assume am: "a \<in> domain \<sigma>"
    have an: "a \<in> domain (stock n)" using am by (simp only: nt)
    have same: "denote (g(n := Some a)) (NApp (NLam n A) (NVar n)) = denote (g(n := Some a)) A"
      by (rule paper_R_binder_self_application[OF body nr typed adequate an])
    show "valuation (denote (g(n := Some a)) (NApp (NLam n A) (NVar n))) =
        valuation (denote (g(n := Some a)) A)" by (rule arg_cong[OF same])
  qed
  show ?thesis by (rule trans[OF source_truth instances])
qed

end

end
