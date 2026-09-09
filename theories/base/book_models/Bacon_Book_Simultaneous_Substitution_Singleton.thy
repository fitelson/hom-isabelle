theory Bacon_Book_Simultaneous_Substitution_Singleton
  imports Bacon_Book_Simultaneous_Substitution_Syntax
    Bacon_Book_Theory_Constant_Substitution
begin

section \<open>The one-entry cases agree with the derived substitution rules\<close>

text \<open>
  A one-entry simultaneous table reproduces literal free-variable or
  typed-constant substitution, including exactly its capture condition.
  Thus the new notation genuinely extends the already proved single-name
  results. The final theorem covers one entry of either kind; no induction
  from this case to arbitrary simultaneous tables is asserted here.
\<close>

lemma book_simult_single_variable:
  "book_simult_subst G [(BSVar x (G x), B)] A = named_subst x B A"
  by (induction A) (auto simp: book_subst_disable_def book_simult_subst_empty split: if_splits)

lemma book_simult_single_constant:
  "book_simult_subst G [(BSConst c \<sigma>, B)] A = book_const_subst c \<sigma> B A"
  by (induction A) (auto simp: book_subst_disable_def split: if_splits)

lemma book_simult_single_variable_free_for:
  "book_simult_free_for G [(BSVar x (G x), B)] A \<longleftrightarrow> named_free_for B x A"
  by (induction A)
    (auto simp: book_subst_disable_def book_simult_free_for_empty book_term_keys_variable split: if_splits)

lemma book_simult_single_constant_free_for:
  "book_simult_free_for G [(BSConst c \<sigma>, B)] A \<longleftrightarrow> book_const_free_for B c \<sigma> A"
  by (induction A)
    (auto simp: book_subst_disable_def book_term_keys_constant split: if_splits)

theorem book_theory_simult_single_constant:
  assumes rich: "sg_rich G" and proof_A: "book_theory_derivable \<Sigma> G {} A"
    and payload: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    and permitted: "book_simult_free_for G [(BSConst c \<sigma>, B)] A"
  shows "book_theory_derivable \<Sigma> G {} (book_simult_subst G [(BSConst c \<sigma>, B)] A)"
proof -
  have free_for: "book_const_free_for B c \<sigma> A"
    using permitted by (simp only: book_simult_single_constant_free_for)
  show ?thesis unfolding book_simult_single_constant
    by (rule book_theory_constant_substitution[OF rich proof_A payload free_for])
qed

lemma book_simult_single_wrong_variable_type:
  assumes mismatch: "\<sigma> \<noteq> G x"
  shows "book_simult_subst G [(BSVar x \<sigma>, B)] A = A"
  using mismatch by (induction A)
    (auto simp: book_subst_disable_def book_simult_subst_empty split: if_splits)

theorem book_theory_simult_single:
  assumes rich: "sg_rich G" and proof_A: "book_theory_derivable \<Sigma> G {} A"
    and payload: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (book_subst_key_type k)"
    and permitted: "book_simult_free_for G [(k, B)] A"
  shows "book_theory_derivable \<Sigma> G {} (book_simult_subst G [(k, B)] A)"
proof (cases k)
  case (BSVar x \<sigma>)
  show ?thesis
  proof (cases "\<sigma> = G x")
    case True
    have replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G x)"
      using payload by (simp only: BSVar book_subst_key_type.simps True)
    have free_for: "named_free_for B x A"
      using permitted by (simp only: BSVar True book_simult_single_variable_free_for)
    have result: "book_theory_derivable \<Sigma> G {} (named_subst x B A)"
      by (rule book_theory_variable_substitution[OF rich proof_A replacement free_for])
    show ?thesis using result by (simp only: BSVar True book_simult_single_variable)
  next
    case False
    show ?thesis by (simp only: BSVar
        book_simult_single_wrong_variable_type[where G=G and x=x and \<sigma>=\<sigma>, OF False]; rule proof_A)
  qed
next
  case (BSConst c \<sigma>)
  have replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    using payload by (simp only: BSConst book_subst_key_type.simps)
  have free_for: "book_simult_free_for G [(BSConst c \<sigma>, B)] A"
    using permitted by (simp only: BSConst)
  show ?thesis unfolding BSConst
    by (rule book_theory_simult_single_constant[OF rich proof_A replacement free_for])
qed

end
