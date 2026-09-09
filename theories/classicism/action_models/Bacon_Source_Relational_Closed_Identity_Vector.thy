theory Bacon_Source_Relational_Closed_Identity_Vector
  imports Bacon_Source_Relational_Environment_Update_Identity Bacon_Source_Relational_Binder_Vectors
begin

section \<open>A singleton environment passes only binders distinct from its coordinate\<close>

lemma paper_R_environment_singleton_lam_vec:
  assumes fresh: "x \<notin> set ns"
  shows "paper_R_environment_subst (Map.empty(x := Some B)) (named_lam_vec ns A) =
    named_lam_vec ns (paper_R_environment_subst (Map.empty(x := Some B)) A)"
  using fresh
proof (induction ns)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  have different: "n \<noteq> x" and tail: "x \<notin> set ns" using Cons.prems by auto
  have deletion: "(Map.empty(x := Some B))(n := None) = Map.empty(x := Some B)"
    by (rule ext; auto simp: different)
  show ?case by (simp only: named_lam_vec.simps paper_R_environment_subst.simps deletion Cons.IH[OF tail])
qed

lemma paper_R_environment_singleton_identity_vector:
  assumes fresh: "x \<notin> set ns" and closed: "named_fv A = {}"
  shows "paper_R_environment_subst (Map.empty(x := Some B))
      (named_lam_vec ns (named_paper_eq \<rho> A (NVar x))) =
    named_lam_vec ns (named_paper_eq \<rho> A B)"
  by (simp only: paper_R_environment_singleton_lam_vec[OF fresh];
    simp add: named_paper_eq_def paper_R_environment_subst_closed_fixed[OF closed])

section \<open>Closed identity payloads can be transported through a displayed prefix\<close>

text \<open>
  From the ambient local identity A=ρB, with A and B CLOSED,
  derive (λn⃗.A=ρA)=(λn⃗.A=ρB).
  Choose x:ρ outside set(n⃗), apply the proved closed-payload
  environment-update identity theorem to λn⃗.(A=ρx), and
  normalize the two singleton environments.
  Source role: the closed-identity case in Appendix A.2, p.66.

  This is a freshness-controlled use of LL and literal β. It is
  not a rule abstracting arbitrary open identities and does not
  invoke Equivalence or a semantic model. Repeated prefix binders
  are permitted; each remains distinct from the fresh coordinate x.
\<close>

theorem paper_R_closed_identity_vector_transport:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A \<rho>"
    and bl: "paper_R_in_language \<Sigma> G B \<rho>"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
    and binders: "list_all paper_R_type (map G ns)"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<rho> A B)"
  shows "paper_R_named_derivable \<Sigma> G S
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns (named_paper_eq \<rho> A A)) (named_lam_vec ns (named_paper_eq \<rho> A B)))"
proof -
  have rt: "paper_R_type \<rho>" by (rule paper_R_language_result_type[OF al])
  obtain x where xt: "G x = \<rho>" and fresh: "x \<notin> set ns"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=\<rho> and S="set ns", OF rich rt finite_set])
  have variable: "paper_R_in_language \<Sigma> G (NVar x) \<rho>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=x, OF xt rt])
  have body: "paper_R_in_language \<Sigma> G (named_paper_eq \<rho> A (NVar x)) Prop"
    by (rule paper_R_named_identity_language[OF al variable])
  have template: "paper_R_in_language \<Sigma> G (named_lam_vec ns (named_paper_eq \<rho> A (NVar x)))
    (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF body binders])
  have empty_typed: "paper_R_closed_term_assignment \<Sigma> G Map.empty"
    by (simp add: paper_R_closed_term_assignment_def)
  have a_closed: "A \<in> paper_R_closed_terms \<Sigma> G (G x)"
    by (simp only: xt; rule paper_R_closed_termsI[OF al ac])
  have b_closed: "B \<in> paper_R_closed_terms \<Sigma> G (G x)"
    by (simp only: xt; rule paper_R_closed_termsI[OF bl bc])
  have coordinate_identity: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (G x) A B)"
    by (simp only: xt; rule equality)
  have updated: "paper_R_named_derivable \<Sigma> G S
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (paper_R_environment_subst (Map.empty(x := Some A)) (named_lam_vec ns (named_paper_eq \<rho> A (NVar x))))
      (paper_R_environment_subst (Map.empty(x := Some B)) (named_lam_vec ns (named_paper_eq \<rho> A (NVar x)))))"
    by (rule paper_R_environment_subst_update_identity[
      OF rich template empty_typed a_closed b_closed coordinate_identity])
  show ?thesis using updated by (simp only: paper_R_environment_singleton_identity_vector[OF fresh ac])
qed

end
