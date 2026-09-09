theory Bacon_Source_Relational_Intensionality_Guarded_Replacement
  imports Bacon_Source_Relational_Intensionality_Syntax
    Bacon_Source_Relational_Application_Identity_Tests
begin

section \<open>Native LL replaces an eigenvariable-safe propositional guard\<close>

theorem paper_R_intensionality_guarded_replacement:
  assumes rich: "paper_R_rich G"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and cl: "paper_R_in_language \<Sigma> G C Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and avoid_B: "set ns \<inter> named_fv B = {}"
    and avoid_C: "set ns \<inter> named_fv C = {}"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop B C)"
  shows "paper_R_named_derivable \<Sigma> G S
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns (named_paper_and P B))
      (named_lam_vec ns (named_paper_and P C)))"
proof -
  let ?L = "named_lam_vec ns (named_paper_and P B)"
  let ?R = "named_lam_vec ns (named_paper_and P C)"
  let ?\<theta> = "paper_type_vector (map G ns) Prop"
  have ll: "paper_R_in_language \<Sigma> G ?L ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_and_language[OF pl bl] binders])
  have rl: "paper_R_in_language \<Sigma> G ?R ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_and_language[OF pl cl] binders])
  have finite: "finite (named_fv P \<union> named_fv B \<union> named_fv C \<union> set ns)"
    by (simp add: named_fv_finite)
  have prop_R: "paper_R_type Prop" by simp
  obtain r where rt: "G r = Prop"
    and fresh: "r \<notin> named_fv P \<union> named_fv B \<union> named_fv C \<union> set ns"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=Prop, OF rich prop_R finite])
  have fixed_P: "r \<notin> named_fv P" and marker: "r \<notin> set ns" using fresh by blast+
  have fixed_L: "r \<notin> named_fv ?L"
    using fresh by (simp only: named_lam_vec_fv named_paper_primitive_fv; blast)
  have variable: "paper_R_in_language \<Sigma> G (NVar r) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=r, OF rt prop_R])
  have template_language: "paper_R_in_language \<Sigma> G
      (named_lam_vec ns (named_paper_and P (NVar r))) ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[
      OF paper_R_named_and_language[OF pl variable] binders])
  let ?Test = "NLam r (named_paper_eq ?\<theta> ?L (named_lam_vec ns (named_paper_and P (NVar r))))"
  have test_body: "paper_R_in_language \<Sigma> G
      (named_paper_eq ?\<theta> ?L (named_lam_vec ns (named_paper_and P (NVar r)))) Prop"
    by (rule paper_R_named_identity_language[OF ll template_language])
  have rr: "paper_R_type (G r)" by (simp only: rt; rule prop_R)
  have predicate: "paper_R_in_language \<Sigma> G ?Test (Arr Prop Prop)"
    using paper_R_named_identity_test_language[OF test_body rr] by (simp only: rt)
  have xl: "paper_R_in_language \<Sigma> G (named_paper_eq ?\<theta> ?L ?L) Prop"
    by (rule paper_R_named_identity_language[OF ll ll])
  have yl: "paper_R_in_language \<Sigma> G (named_paper_eq ?\<theta> ?L ?R) Prop"
    by (rule paper_R_named_identity_language[OF ll rl])
  have first_step: "named_compatible_step named_beta_contract (NApp ?Test B) (named_paper_eq ?\<theta> ?L ?L)"
    by (rule paper_R_intensionality_guard_test_beta[OF fixed_L fixed_P marker avoid_B])
  have second_step: "named_compatible_step named_beta_contract (NApp ?Test C) (named_paper_eq ?\<theta> ?L ?R)"
    by (rule paper_R_intensionality_guard_test_beta[OF fixed_L fixed_P marker avoid_C])
  have initial: "paper_R_named_derivable \<Sigma> G S (named_paper_eq ?\<theta> ?L ?L)"
    by (rule paper_R_named_identity_refl[OF ll])
  show ?thesis by (rule paper_R_named_derivable_LL_beta[
    OF rich bl cl predicate xl yl first_step second_step equality initial])
qed

text \<open>
  This is local H reasoning with the actual LL schema and two
  capture-safe β instances. Only a scalar guard is replaced; the
  possibly open payloads explicitly avoid the λ-prefix binders.
  No local ζ, Equivalence rule, model, or general λ-congruence
  principle is used. Source: the middle step on p.17.
\<close>

end
