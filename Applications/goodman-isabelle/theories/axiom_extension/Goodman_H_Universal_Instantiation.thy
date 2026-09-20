theory Goodman_H_Universal_Instantiation
  imports Goodman_H_Conversion_Schemas
begin

section \<open>The old UI schema becomes a theorem of the book's H\<close>

text \<open>
  ∀x.M → M[N/x]. The book's primitive UI gives (∀σ F) → F N.
  Take F to be the translated abstraction, then use our checked named
  β bridge to obtain the actual translated substitution result.
  Both implications are combined by a derived book-H implication rule.
  We do not assume that the two syntax representations are identical.
\<close>

theorem gi_H_UI:
  assumes rich: "sg_rich G" and body: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
    and argument: "\<Gamma> \<turnstile> N : \<sigma>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and body_constants: "gi_constants_admitted k \<Sigma> M"
    and argument_constants: "gi_constants_admitted k \<Sigma> N"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp (Forall \<sigma> M) (subst0 N M)))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?M = "gi_to_book G (?n # ns) k M"
  let ?N = "gi_to_book G ns k N"
  let ?F = "NLam ?n ?M"
  let ?U = "gi_to_book G ns k (Forall \<sigma> M)"
  let ?R = "gi_to_book G ns k (App (Lam \<sigma> M) N)"
  let ?Y = "gi_to_book G ns k (subst0 N M)"
  have ml: "book_theory_formula \<Sigma> G ?M"
    by (rule gi_to_book_language[OF rich body gi_chart_extension[OF rich chart] body_constants])
  have nl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?N \<sigma>"
    by (rule gi_to_book_language[OF rich argument chart argument_constants])
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?F (Arr \<sigma> Prop)"
    using book_language_Lam[OF ml, where n="?n"]
    by (simp only: named_chart_fresh_type[OF rich])
  have ul: "book_theory_formula \<Sigma> G ?U"
    by (simp only: gi_to_book.simps Let_def; rule book_all_language[OF ml])
  have primitive: "book_theory_derivable \<Sigma> G {}
    (book_imp (NApp (NLogical (SBAll \<sigma>)) ?F) (NApp ?F ?N))"
    by (rule book_theory_derivable.UI[OF fl nl])
  have first: "book_theory_derivable \<Sigma> G {} (book_imp ?U ?R)"
    using primitive by (simp only: gi_to_book.simps Let_def book_all_def named_chart_fresh_type[OF rich])
  have conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop ?R ?Y"
    by (rule gi_to_book_beta_root[OF rich body argument chart distinct body_constants argument_constants])
  have rl: "book_theory_formula \<Sigma> G ?R" and yl: "book_theory_formula \<Sigma> G ?Y"
    using named_beta_eta_languages[OF conversion] by (auto simp only: book_language_UNIV)
  have second: "book_theory_derivable \<Sigma> G {} (book_imp ?R ?Y)"
    by (rule conjunct1[OF book_theory_conversion_pair[OF conversion refl]])
  have result: "book_theory_derivable \<Sigma> G {} (book_imp ?U ?Y)"
    by (rule book_theory_imp_trans[OF ul rl yl first second])
  show ?thesis using result by (simp only: gi_to_book.simps book_H_iff_theory[OF rich])
qed

text \<open>
  This theorem covers UI under the explicit type/chart/signature guards.
  It does not supply existential generalization, quantifier proof rules,
  the propositional-tautology schema, or whole-proof H preservation.
\<close>

end
