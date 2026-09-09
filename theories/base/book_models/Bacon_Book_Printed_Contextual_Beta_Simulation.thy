theory Bacon_Book_Printed_Contextual_Beta_Simulation
  imports Bacon_Book_Printed_Beta_Simulation Bacon_Book_Source_Reduction_Contexts
begin

section \<open>Recovering the root simulation's typing hypotheses\<close>

text \<open>
  A typed exact-capture β redex determines the type of its body and
  gives the argument the type G(x) of its binder. We can therefore
  invoke the checked α-freshening simulation without a new typing or
  signature assumption on the reduct. Source: Bacon, pp.69–73.
\<close>

theorem book_printed_beta_contract_simulation:
  assumes rich: "sg_rich G"
    and step: "named_beta_contract A C"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_source_reduces G A C"
  using step language
proof (induction arbitrary: \<tau> rule: named_beta_contract.induct)
  case (beta N x M)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G (NLam x M) (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G N \<sigma>"
    by (rule book_language_App_obtain[OF beta.prems]; rule that; assumption)
  obtain \<rho> where arrow: "Arr \<sigma> \<tau> = Arr (G x) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G M \<rho>"
    by (rule book_language_Lam_obtain[OF head]; rule that; assumption)
  have body_language: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
    using body arrow by simp
  have payload_language: "book_in_language L \<Lambda> \<Sigma> G N (G x)"
    using argument arrow by simp
  show ?case by (rule book_printed_beta_simulation[OF rich body_language payload_language beta.hyps])
qed

section \<open>Simulation at every depth of a typed term\<close>

text \<open>
  If A→β,exactC is a contextual step and A:τ belongs to the full
  declared language, then A↠printedC. The induction follows the
  application or abstraction context to the redex, preserving the
  subterm's own type. It then lifts the simulated root chain back
  through that context.

  Rich G and the source language/type guard remain explicit. Every
  intermediate in the resulting chain stays in the same ambient
  language by the separately proved source-reduction preservation
  theorem. This is not a calculus proof, a Church–Rosser theorem, or
  a claim that all those intermediates belong to an arbitrary 𝒥.
\<close>

theorem book_printed_beta_step_simulation:
  assumes rich: "sg_rich G"
    and step: "named_compatible_step named_beta_contract A C"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_source_reduces G A C"
  using step language
proof (induction arbitrary: \<tau> rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule book_printed_beta_contract_simulation[OF rich root.hyps root.prems])
next
  case (App_left M M' N)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G M (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G N \<sigma>"
    by (rule book_language_App_obtain[OF App_left.prems]; rule that; assumption)
  have reduction: "book_source_reduces G M M'" by (rule App_left.IH[OF head])
  show ?case by (rule book_source_reduces_App_left[OF reduction])
next
  case (App_right N N' M)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G M (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G N \<sigma>"
    by (rule book_language_App_obtain[OF App_right.prems]; rule that; assumption)
  have reduction: "book_source_reduces G N N'" by (rule App_right.IH[OF argument])
  show ?case by (rule book_source_reduces_App_right[OF reduction])
next
  case (Lam_body M M' n)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G M \<rho>"
    by (rule book_language_Lam_obtain[OF Lam_body.prems]; rule that; assumption)
  have reduction: "book_source_reduces G M M'" by (rule Lam_body.IH[OF body])
  show ?case by (rule book_source_reduces_Lam[OF reduction])
qed

end
