theory Bacon_Book_MF_Binder_Conversion
  imports Bacon_Book_MF_Free_For
begin

section \<open>Binder changes with the exact η and β provisos\<close>

theorem book_binder_rename_with_free_for:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_fv (NLam x A)"
    and permitted: "named_free_for (NVar y) x A"
  shows "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_subst x (NVar y) A))"
proof -
  let ?F = "NLam x A"
  let ?R = "NApp ?F (NVar y)"
  let ?S = "named_subst x (NVar y) A"
  have variable: "named_in_language L \<Sigma> G (NVar y) (G x)"
    using named_conversion_variable_language[where L=L and \<Sigma>=\<Sigma> and G=G and n=y]
    by (simp only: same)
  have fn: "named_in_language L \<Sigma> G ?F (Arr (G x) \<tau>)"
    by (rule named_language_Lam[OF language])
  have redex: "named_in_language L \<Sigma> G ?R \<tau>"
    by (rule named_language_App[OF fn variable])
  have expanded: "named_in_language L \<Sigma> G (NLam y ?R) (Arr (G x) \<tau>)"
    using named_language_Lam[where n=y, OF redex] by (simp only: same)
  have substituted: "named_in_language L \<Sigma> G ?S \<tau>"
    by (rule named_subst_language[OF language variable])
  have not_free: "y \<notin> named_fv ?F"
    by (rule fresh)
  have eta_root: "named_eta_contract (NLam y ?R) ?F"
    by (rule named_eta_contract.eta[OF not_free])
  have eta_step: "named_compatible_step named_eta_contract (NLam y ?R) ?F"
    by (rule named_compatible_step.root[where R=named_eta_contract
      and M="NLam y ?R" and N="?F", OF eta_root])
  have eta: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>) (NLam y ?R) ?F"
    by (rule named_beta_eta_in_language.Eta[OF expanded fn eta_step])
  have free_for: "named_free_for (NVar y) x A"
    by (rule permitted)
  have beta_root: "named_beta_contract ?R ?S"
    by (rule named_beta_contract.beta[OF free_for])
  have beta_step: "named_compatible_step named_beta_contract ?R ?S"
    by (rule named_compatible_step.root[where R=named_beta_contract
      and M="?R" and N="?S", OF beta_root])
  have beta: "named_beta_eta_in_language L \<Sigma> G \<tau> ?R ?S"
    by (rule named_beta_eta_in_language.Beta[OF redex substituted beta_step])
  have under_binder: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam y ?R) (NLam y ?S)"
    using named_conversion_Lam[where n=y, OF beta] by (simp only: same)
  show ?thesis
    by (rule named_beta_eta_in_language.Trans[OF named_beta_eta_in_language.Sym[OF eta] under_binder])
qed

theorem book_full_C_conversion:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
    and conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
  shows "book_full_C_proves \<Sigma> G B"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_full_C_proves_language[OF rich derivation])
  have base: "book_theory_derivable \<Sigma> G {A} A" by (rule book_theory_derivable.Assumption; (simp | rule al))
  have converted: "book_theory_derivable \<Sigma> G {A} B" by (rule book_theory_conversion_transport[OF conversion base])
  show ?thesis by (rule book_full_C_contains_theory_derivation[OF rich converted]; simp add: derivation)
qed

text \<open>
  Changing λx.A to λy.A[y/x] requires the source η freshness condition
  y∉FV(λx.A) and the literal β free-for condition, not the stronger
  demand that y occur nowhere among A's bound variables. The intermediate
  term is λy.((λx.A)y). Every node retains its declared language and type.
  Full-C theorem conversion is then inherited from the original H theory
  conversion proof. No new α rule or semantic equality is postulated.
\<close>

end
