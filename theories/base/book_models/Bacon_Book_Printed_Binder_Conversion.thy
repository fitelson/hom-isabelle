theory Bacon_Book_Printed_Binder_Conversion
  imports Bacon_Book_Printed_Conversion_Contexts
begin

section \<open>A binder change derived from printed β and η alone\<close>

text \<open>
  λx.A ≡βη λy.A[y/x] when G(x)=G(y) and y∉Vars(A).
  The intermediate term is λy.((λx.A)y). Its inner β step satisfies
  the printed free-for condition because no binder of A uses y.
  The surrounding λy deliberately binds the inserted variable; the
  free-for test concerns the redex body A, not its outer context.
  Source: Definitions 3.5–3.7, pp.66–70, and the schemas on p.98.

  All conversion conclusions here use the NEW printed-guard relation,
  which has no α constructor. Neither the previous α-to-conversion
  theorem nor α-inclusive source reduction supplies the conclusion.
\<close>

lemma book_printed_fresh_variable_free_for:
  assumes fresh: "y \<notin> named_vars A"
  shows "book_printed_free_for (NVar y) x A"
  using fresh by (induction A) auto

lemma book_printed_swap_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and same: "G x = G y"
  shows "book_in_language L \<Lambda> \<Sigma> G (named_swap x y A) \<tau>"
proof -
  have typed: "has_ntype L G (named_swap x y A) \<tau>"
    by (rule named_swap_type[OF same book_language_type[OF language]])
  have names: "named_in_signature \<Sigma> (named_swap x y A)"
    by (simp only: named_swap_signature; rule book_language_signature[OF language])
  have symbols: "named_logical_occurrences (named_swap x y A) \<subseteq> \<Lambda>"
    by (simp only: book_swap_logical_occurrences; rule book_language_logical_occurrences[OF language])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] symbols])
qed

theorem book_printed_binder_literal_rename:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_subst x (NVar y) A))"
proof -
  let ?F = "NLam x A"
  let ?R = "NApp ?F (NVar y)"
  let ?S = "named_subst x (NVar y) A"
  have variable: "book_in_language L \<Lambda> \<Sigma> G (NVar y) (G x)"
    by (simp only: book_language_var_iff; rule same)
  have fn: "book_in_language L \<Lambda> \<Sigma> G ?F (Arr (G x) \<tau>)"
    by (rule book_language_Lam[OF language])
  have redex: "book_in_language L \<Lambda> \<Sigma> G ?R \<tau>"
    by (rule book_language_App[OF fn variable])
  have expanded: "book_in_language L \<Lambda> \<Sigma> G (NLam y ?R) (Arr (G x) \<tau>)"
    using book_language_Lam[where n=y, OF redex] by (simp only: same)
  have substituted: "book_in_language L \<Lambda> \<Sigma> G ?S \<tau>"
    by (rule book_variable_subst_language[OF language variable])
  have not_free: "y \<notin> named_fv ?F"
    using fresh named_fv_subset_vars[where A=A] by auto
  have eta_root: "named_eta_contract (NLam y ?R) ?F"
    by (rule named_eta_contract.eta[OF not_free])
  have eta_step: "named_compatible_step named_eta_contract (NLam y ?R) ?F"
    by (rule named_compatible_step.root; rule eta_root)
  have eta: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>) (NLam y ?R) ?F"
    by (rule book_printed_conversion.Eta[OF expanded fn eta_step])
  have free_for: "book_printed_free_for (NVar y) x A"
    by (rule book_printed_fresh_variable_free_for[OF fresh])
  have beta_root: "book_printed_beta_contract ?R ?S"
    by (rule book_printed_beta_contract.beta[OF free_for])
  have beta_step: "named_compatible_step book_printed_beta_contract ?R ?S"
    by (rule named_compatible_step.root; rule beta_root)
  have beta: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> ?R ?S"
    by (rule book_printed_conversion.PrintedBeta[OF redex substituted beta_step])
  have under_binder: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>)
    (NLam y ?R) (NLam y ?S)"
    using book_printed_conversion_Lam[where n=y, OF beta] by (simp only: same)
  show ?thesis by (rule book_printed_conversion.Trans[OF book_printed_conversion.Sym[OF eta] under_binder])
qed

lemma book_printed_binder_from_alignment:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
    and alignment: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau>
      (named_subst x (NVar y) A) (named_swap x y A)"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_swap x y A))"
proof -
  have literal: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_subst x (NVar y) A))"
    by (rule book_printed_binder_literal_rename[OF language same fresh])
  have aligned: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>)
    (NLam y (named_subst x (NVar y) A)) (NLam y (named_swap x y A))"
    using book_printed_conversion_Lam[where n=y, OF alignment] by (simp only: same)
  show ?thesis by (rule book_printed_conversion.Trans[OF literal aligned])
qed

end
