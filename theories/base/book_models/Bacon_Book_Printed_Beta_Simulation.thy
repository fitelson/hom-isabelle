theory Bacon_Book_Printed_Beta_Simulation
  imports Bacon_Book_Printed_Binder_Freshening Bacon_Book_Source_Reduction
begin

section \<open>An exact-capture β step is a printed reduction after freshening\<close>

text \<open>
  For a typed body M and an exact-capture-permitted payload N, replace M
  by an α-variant M′ whose binders avoid FV(N). The printed β step
  is then legal. The two substituted results have identical binding
  encodings, hence are α-equivalent. Thus
    (λx.M)N ≡α (λx.M′)N →β,printed M′[N/x] ≡α M[N/x].
  Source: the freshening argument on pp.69–70 and the α-inclusive
  reduction definition on p.73.

  This theorem concerns the independently defined source reduction relation.
  It does not assume a printed proof-calculus α rule or claim the whole
  calculus correspondence. Richness and all language/type guards remain
  explicit. No model, theoremhood, or consistency predicate is used.
\<close>

lemma book_source_reduces_trans:
  assumes first: "book_source_reduces G A B" and second: "book_source_reduces G B C"
  shows "book_source_reduces G A C"
  using first second unfolding book_source_reduces_def by (rule rtranclp_trans)

theorem book_printed_beta_simulation:
  assumes rich: "sg_rich G"
    and body: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
    and payload: "book_in_language L \<Lambda> \<Sigma> G N (G x)"
    and free_for: "named_free_for N x M"
  shows "book_source_reduces G (NApp (NLam x M) N) (named_subst x N M)"
proof -
  let ?P = "book_binder_freshen G N M"
  let ?R = "NApp (NLam x ?P) N"
  let ?Q = "named_subst x N ?P"
  have alpha: "named_alpha G M ?P" by (rule book_binder_freshen_alpha[OF rich body])
  have redex_alpha: "named_alpha G (NApp (NLam x M) N) ?R"
    by (rule named_alpha.App[OF named_alpha.Lam[OF alpha] named_alpha.Refl])
  have first: "book_source_reduces G (NApp (NLam x M) N) ?R"
    by (rule book_source_reduces_alpha[OF redex_alpha])
  have printed: "book_printed_free_for N x ?P" by (rule book_binder_freshen_printed_free_for[OF rich])
  have beta: "book_printed_beta_contract ?R ?Q" by (rule book_printed_beta_contract.beta[OF printed])
  have step: "book_source_reduction_step G ?R ?Q"
    unfolding book_source_reduction_step_def
    by (rule disjI1, rule named_compatible_step.root; rule beta)
  have middle: "book_source_reduces G ?R ?Q"
    unfolding book_source_reduces_def by (rule r_into_rtranclp; rule step)
  have exact: "named_free_for N x ?P" by (rule book_printed_free_for_named[OF printed])
  have encoding: "named_to_source G [] ?Q = named_to_source G [] (named_subst x N M)"
    by (simp only: named_subst_encoding_empty[OF exact] named_subst_encoding_empty[OF free_for]
        book_binder_freshen_encoding[OF rich body])
  have result_alpha: "named_alpha G ?Q (named_subst x N M)"
    by (rule named_encoding_implies_alpha[OF rich encoding])
  have last: "book_source_reduces G ?Q (named_subst x N M)"
    by (rule book_source_reduces_alpha[OF result_alpha])
  show ?thesis by (rule book_source_reduces_trans[OF first book_source_reduces_trans[OF middle last]])
qed

end
