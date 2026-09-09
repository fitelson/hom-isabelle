theory Bacon_Book_Conjunction_Simultaneous_Substitution_Singleton
  imports Bacon_Book_Conjunction_Constant_Substitution
    Bacon_Book_Simultaneous_Substitution_Singleton Bacon_Book_Substitution_Freshness
begin

section \<open>One simultaneous entry in a native conjunction theorem\<close>

text \<open>
  A singleton table replaces either one free variable or one ordinary
  typed nonlogical constant. Its operation and capture test agree with
  the existing single-name operations. Source: Definition 5.2, p.99,
  for the primitive conjunction extension of §5.2, p.104.

  We apply the proved NATIVE single-name admissibility theorems to an
  empty-premise native derivation. A wrongly typed variable key is inert.
  There is no key for a logical symbol: BCAnd and all BCMinimal symbols
  remain fixed. No conjunction-background or model premise is introduced.
\<close>

lemma book_subst_table_language_singleton:
  assumes payload: "book_in_language L \<Lambda> \<Sigma> G B (book_subst_key_type k)"
  shows "book_subst_table_language L \<Lambda> \<Sigma> G [(k,B)]"
proof (unfold book_subst_table_language_def, intro allI impI)
  fix j C
  assume found: "map_of [(k,B)] j = Some C"
  have key: "j = k" and payload_eq: "C = B" using found by (auto split: if_splits)
  show "book_in_language L \<Lambda> \<Sigma> G C (book_subst_key_type j)"
    by (simp only: key payload_eq; rule payload)
qed

theorem book_conj_theory_simult_single:
  assumes rich: "sg_rich G"
    and derivation: "book_conj_theory_derivable \<Sigma> G {} A"
    and table: "book_subst_table_language book_conj_logical_type UNIV \<Sigma> G [(k,B)]"
    and permitted: "book_simult_free_for G [(k,B)] A"
  shows "book_conj_theory_derivable \<Sigma> G {} (book_simult_subst G [(k,B)] A)"
proof -
  have found: "map_of [(k,B)] k = Some B" by simp
  have payload: "book_in_language book_conj_logical_type UNIV \<Sigma> G B (book_subst_key_type k)"
    by (rule book_subst_table_language_lookup[OF table found])
  show ?thesis
  proof (cases k)
    case (BSVar x \<sigma>)
    show ?thesis
    proof (cases "\<sigma> = G x")
      case True
      have replacement: "book_in_language book_conj_logical_type UNIV \<Sigma> G B (G x)"
        using payload by (simp only: BSVar book_subst_key_type.simps True)
      have free_for: "named_free_for B x A"
        using permitted by (simp only: BSVar True book_simult_single_variable_free_for)
      have result: "book_conj_theory_derivable \<Sigma> G {} (named_subst x B A)"
        by (rule book_conj_theory_variable_substitution[OF rich derivation replacement free_for])
      show ?thesis using result by (simp only: BSVar True book_simult_single_variable)
    next
      case False
      have unchanged: "book_simult_subst G [(BSVar x \<sigma>,B)] A = A"
        by (rule book_simult_single_wrong_variable_type[where G=G and x=x and \<sigma>=\<sigma>, OF False])
      show ?thesis by (simp only: BSVar unchanged; rule derivation)
    qed
  next
    case (BSConst c \<sigma>)
    have replacement: "book_in_language book_conj_logical_type UNIV \<Sigma> G B \<sigma>"
      using payload by (simp only: BSConst book_subst_key_type.simps)
    have free_for: "book_const_free_for B c \<sigma> A"
      using permitted by (simp only: BSConst book_simult_single_constant_free_for)
    have result: "book_conj_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> B A)"
      by (rule book_conj_theory_constant_substitution[OF rich derivation replacement free_for])
    show ?thesis using result by (simp only: BSConst book_simult_single_constant)
  qed
qed

end
