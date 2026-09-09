theory Bacon_Source_Relational_Global_Abstraction_Identity
  imports Bacon_Source_Relational_Zeta_Theory
    Bacon_Source_Relational_Global_Abstraction_Beta Bacon_Source_Relational_Binder_Vectors
begin

section \<open>Global identity theorems lift through one abstraction\<close>

theorem paper_R_H_zeta_abstraction_identity:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and zeta: "paper_R_zeta_closed \<Sigma> G T"
    and al: "paper_R_in_language \<Sigma> G A \<tau>" and bl: "paper_R_in_language \<Sigma> G B \<tau>"
    and nr: "paper_R_type (G n)" and result: "\<tau> \<noteq> Ind"
    and member: "named_paper_eq \<tau> A B \<in> T"
  shows "named_paper_eq (Arr (G n) \<tau>) (NLam n A) (NLam n B) \<in> T"
proof -
  have finite: "finite (named_vars A \<union> named_vars B \<union> {n})" by (simp add: named_vars_finite)
  obtain v where vt: "G v = G n" and avoids: "v \<notin> named_vars A \<union> named_vars B \<union> {n}"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>="G n", OF rich nr finite])
  have va: "v \<notin> named_vars A" and vb: "v \<notin> named_vars B" using avoids by blast+
  have vl: "paper_R_in_language \<Sigma> G (NVar v) (G n)"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=v, OF vt nr])
  have fa: "named_free_for (NVar v) n A" by (rule paper_R_global_abstraction_variable_free_for[OF va])
  have fb: "named_free_for (NVar v) n B" by (rule paper_R_global_abstraction_variable_free_for[OF vb])
  have fe: "named_free_for (NVar v) n (named_paper_eq \<tau> A B)"
    by (simp add: named_paper_eq_def fa fb)
  have substituted: "named_subst n (NVar v) (named_paper_eq \<tau> A B) \<in> T"
    by (rule paper_R_H_theory_substitution[OF rich theory_h member vl fe])
  have sub_member: "named_paper_eq \<tau> (named_subst n (NVar v) A) (named_subst n (NVar v) B) \<in> T"
    using substituted by (simp add: named_paper_eq_def)
  have sa: "paper_R_in_language \<Sigma> G (named_subst n (NVar v) A) \<tau>"
    by (rule paper_R_subst_language_pure[OF al vl])
  have sb: "paper_R_in_language \<Sigma> G (named_subst n (NVar v) B) \<tau>"
    by (rule paper_R_subst_language_pure[OF bl vl])
  have la: "paper_R_in_language \<Sigma> G (NLam n A) (Arr (G n) \<tau>)"
    by (rule paper_R_global_abstraction_language[OF al nr result])
  have lb: "paper_R_in_language \<Sigma> G (NLam n B) (Arr (G n) \<tau>)"
    by (rule paper_R_global_abstraction_language[OF bl nr result])
  have aa: "paper_R_in_language \<Sigma> G (NApp (NLam n A) (NVar v)) \<tau>"
    by (rule paper_R_language_App[OF la vl])
  have ab: "paper_R_in_language \<Sigma> G (NApp (NLam n B) (NVar v)) \<tau>"
    by (rule paper_R_language_App[OF lb vl])
  have a_beta: "paper_R_named_H \<Sigma> G
      (named_paper_eq \<tau> (NApp (NLam n A) (NVar v)) (named_subst n (NVar v) A))"
    by (rule paper_R_named_H_fresh_abstraction_beta_identity[OF rich al nr result vt va])
  have b_beta: "paper_R_named_H \<Sigma> G
      (named_paper_eq \<tau> (NApp (NLam n B) (NVar v)) (named_subst n (NVar v) B))"
    by (rule paper_R_named_H_fresh_abstraction_beta_identity[OF rich bl nr result vt vb])
  have sub_identity: "paper_R_named_derivable \<Sigma> G T
      (named_paper_eq \<tau> (named_subst n (NVar v) A) (named_subst n (NVar v) B))"
    by (rule paper_R_named_derivable.Assumption[OF sub_member paper_R_named_identity_language[OF sa sb]])
  have first: "paper_R_named_derivable \<Sigma> G T
      (named_paper_eq \<tau> (NApp (NLam n A) (NVar v)) (named_subst n (NVar v) B))"
    by (rule paper_R_named_identity_trans[OF rich aa sa sb
      paper_R_named_derivable.Theorem[OF a_beta] sub_identity])
  have last: "paper_R_named_derivable \<Sigma> G T
      (named_paper_eq \<tau> (named_subst n (NVar v) B) (NApp (NLam n B) (NVar v)))"
    by (rule paper_R_named_identity_sym[OF rich ab sb paper_R_named_derivable.Theorem[OF b_beta]])
  have applications: "paper_R_named_derivable \<Sigma> G T
      (named_paper_eq \<tau> (NApp (NLam n A) (NVar v)) (NApp (NLam n B) (NVar v)))"
    by (rule paper_R_named_identity_trans[OF rich aa sb ab first last])
  have in_original: "named_paper_eq \<tau> (NApp (NLam n A) (NVar v)) (NApp (NLam n B) (NVar v)) \<in> T"
    by (rule paper_R_H_theory_local_consequences[OF theory_h applications subset_refl])
  have fresh_left: "v \<notin> named_fv (NLam n A)"
    using va named_fv_subset_vars[of A] by auto
  have fresh_right: "v \<notin> named_fv (NLam n B)"
    using vb named_fv_subset_vars[of B] by auto
  show ?thesis by (rule paper_R_zeta_closedD[
    OF zeta la lb vt fresh_left fresh_right in_original])
qed

section \<open>Iterated global abstraction, including repeated bound names\<close>

theorem paper_R_H_zeta_lam_vec_identity:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and zeta: "paper_R_zeta_closed \<Sigma> G T"
    and al: "paper_R_in_language \<Sigma> G A \<tau>" and bl: "paper_R_in_language \<Sigma> G B \<tau>"
    and binders: "list_all paper_R_type (map G ns)" and result: "\<tau> \<noteq> Ind"
    and member: "named_paper_eq \<tau> A B \<in> T"
  shows "named_paper_eq (paper_type_vector (map G ns) \<tau>) (named_lam_vec ns A) (named_lam_vec ns B) \<in> T"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: list.map paper_type_vector.simps named_lam_vec.simps; rule member)
next
  case (Cons n ns)
  have nr: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)" using Cons.prems by simp_all
  have left: "paper_R_in_language \<Sigma> G (named_lam_vec ns A) (paper_type_vector (map G ns) \<tau>)"
    by (rule paper_R_named_lam_vec_language[OF al tail result])
  have right: "paper_R_in_language \<Sigma> G (named_lam_vec ns B) (paper_type_vector (map G ns) \<tau>)"
    by (rule paper_R_named_lam_vec_language[OF bl tail result])
  have tail_result: "paper_type_vector (map G ns) \<tau> \<noteq> Ind"
    by (rule paper_type_vector_nonindividual_result[OF result])
  have inner: "named_paper_eq (paper_type_vector (map G ns) \<tau>) (named_lam_vec ns A) (named_lam_vec ns B) \<in> T"
    by (rule Cons.IH[OF tail])
  show ?case by (simp only: list.map paper_type_vector.simps named_lam_vec.simps;
    rule paper_R_H_zeta_abstraction_identity[OF rich theory_h zeta left right nr tail_result inner])
qed

text \<open>
  Every ζ premise has first been established as a member of the
  ORIGINAL H-theory T. The local relation above is used over T
  itself, with no additional assumption. Fresh tests are chosen per
  step; the displayed abstraction binders may repeat and may bind
  free variables of A and B. This is global theorem closure, not
  λ-congruence under arbitrary local hypotheses. Source: pp.14–16.
\<close>

end
