theory Bacon_Book_Source_Reduction
  imports Bacon_Book_Printed_Free_For Bacon_Book_Contextual_Reduction_Language
    Bacon_Book_Alpha_Language
begin

section \<open>Directed βη reduction with bound-variable relabelling\<close>

text \<open>
  Definition 3.10, p.73, permits directed β contractions, directed η
  contractions, and bound-variable relabellings. A possibly empty chain
  of these steps is reduction. We retain the recursive free-for test
  printed in Definition 3.7, p.70, for its β roots.

  The relation is ambient and independent of any selected 𝒥. It does
  not require intermediate terms to be in 𝒥 as an antecedent to that
  language's reduction-closure axiom. Language preservation is proved
  separately below. This is not a confluence theorem or a reverse
  correspondence with the existing exact-capture β relation.
\<close>

inductive book_printed_beta_contract ::
  "('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  beta: "book_printed_free_for N x M \<Longrightarrow>
    book_printed_beta_contract (NApp (NLam x M) N) (named_subst x N M)"

lemma book_printed_beta_contract_named:
  assumes step: "book_printed_beta_contract A B"
  shows "named_beta_contract A B"
  using step by (cases rule: book_printed_beta_contract.cases)
    (auto intro: named_beta_contract.beta book_printed_free_for_named)

lemma book_printed_beta_step_language:
  assumes step: "named_compatible_step book_printed_beta_contract A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
proof (rule book_compatible_step_language[OF step _ language])
  fix M N \<rho>
  assume root: "book_printed_beta_contract M N"
    and ml: "book_in_language L \<Lambda> \<Sigma> G M \<rho>"
  show "book_in_language L \<Lambda> \<Sigma> G N \<rho>"
    by (rule book_beta_contract_language[OF book_printed_beta_contract_named[OF root] ml])
qed

definition book_source_reduction_step ::
  "sgcontext \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_source_reduction_step G A B \<longleftrightarrow>
    named_compatible_step book_printed_beta_contract A B \<or>
    named_compatible_step named_eta_contract A B \<or> named_alpha G A B"

definition book_source_reduces ::
  "sgcontext \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_source_reduces G A B \<longleftrightarrow> rtranclp (book_source_reduction_step G) A B"

lemma book_source_reduction_step_language:
  assumes step: "book_source_reduction_step G A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  using step language unfolding book_source_reduction_step_def
  by (blast intro: book_printed_beta_step_language book_eta_step_language
      iffD1[OF book_alpha_language_iff])

theorem book_source_reduces_language:
  assumes reduction: "book_source_reduces G A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  using reduction[unfolded book_source_reduces_def] language
  by (induction rule: rtranclp_induct) (auto intro: book_source_reduction_step_language)

lemma book_source_reduces_alpha:
  assumes alpha: "named_alpha G A B"
  shows "book_source_reduces G A B"
proof -
  have step: "book_source_reduction_step G A B"
    using alpha by (simp add: book_source_reduction_step_def)
  show ?thesis unfolding book_source_reduces_def by (rule r_into_rtranclp; rule step)
qed

end
