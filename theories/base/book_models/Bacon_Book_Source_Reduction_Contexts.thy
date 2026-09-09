theory Bacon_Book_Source_Reduction_Contexts
  imports Bacon_Book_Source_Reduction
begin

section \<open>Printed reductions remain reductions in a term context\<close>

text \<open>
  If A↠C, then AN↠CN, NA↠NC, and λx.A↠λx.C.
  Here ↠ is Definition 3.10's possibly empty chain of printed β,
  η, and α steps (Bacon, p.73). Each component step is closed under
  these contexts, so the whole chain is. This is raw syntax: language
  preservation is a separate checked theorem, and no H or model premise
  is involved. In particular, α is part of this reduction definition,
  not an assumed rule of the printed Chapter 5 proof calculus.
\<close>

lemma book_source_reduction_step_App_left:
  assumes step: "book_source_reduction_step G A C"
  shows "book_source_reduction_step G (NApp A N) (NApp C N)"
  using step unfolding book_source_reduction_step_def
  by (blast intro: named_compatible_step.App_left named_alpha.App named_alpha.Refl)

lemma book_source_reduction_step_App_right:
  assumes step: "book_source_reduction_step G A C"
  shows "book_source_reduction_step G (NApp N A) (NApp N C)"
  using step unfolding book_source_reduction_step_def
  by (blast intro: named_compatible_step.App_right named_alpha.App named_alpha.Refl)

lemma book_source_reduction_step_Lam:
  assumes step: "book_source_reduction_step G A C"
  shows "book_source_reduction_step G (NLam n A) (NLam n C)"
  using step unfolding book_source_reduction_step_def
  by (blast intro: named_compatible_step.Lam_body named_alpha.Lam)

lemma book_source_reduces_map:
  assumes reduction: "book_source_reduces G A C"
    and steps: "\<And>M N. book_source_reduction_step G M N \<Longrightarrow>
      book_source_reduction_step G (f M) (f N)"
  shows "book_source_reduces G (f A) (f C)"
  using reduction[unfolded book_source_reduces_def]
  unfolding book_source_reduces_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (step M N)
  have mapped: "book_source_reduction_step G (f M) (f N)"
    by (rule steps[OF step.hyps(2)])
  show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH mapped])
qed

theorem book_source_reduces_App_left:
  assumes reduction: "book_source_reduces G A C"
  shows "book_source_reduces G (NApp A N) (NApp C N)"
  by (rule book_source_reduces_map[where f="\<lambda>A. NApp A N", OF reduction];
      rule book_source_reduction_step_App_left; assumption)

theorem book_source_reduces_App_right:
  assumes reduction: "book_source_reduces G A C"
  shows "book_source_reduces G (NApp N A) (NApp N C)"
  by (rule book_source_reduces_map[where f="\<lambda>A. NApp N A", OF reduction];
      rule book_source_reduction_step_App_right; assumption)

theorem book_source_reduces_Lam:
  assumes reduction: "book_source_reduces G A C"
  shows "book_source_reduces G (NLam n A) (NLam n C)"
  by (rule book_source_reduces_map[where f="NLam n", OF reduction];
      rule book_source_reduction_step_Lam; assumption)

corollary book_source_reduces_App:
  assumes head: "book_source_reduces G F H" and argument: "book_source_reduces G A C"
  shows "book_source_reduces G (NApp F A) (NApp H C)"
proof -
  have first: "book_source_reduces G (NApp F A) (NApp H A)"
    by (rule book_source_reduces_App_left[OF head])
  have second: "book_source_reduces G (NApp H A) (NApp H C)"
    by (rule book_source_reduces_App_right[OF argument])
  show ?thesis unfolding book_source_reduces_def
    by (rule rtranclp_trans[OF first[unfolded book_source_reduces_def]
      second[unfolded book_source_reduces_def]])
qed

end
