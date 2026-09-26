theory Bacon_Book_Lambda_I_Universal_Closure_Consistency
  imports Bacon_Book_Lambda_I_Universal_Closure Bacon_Book_Lambda_I_Theory_Consistency
begin

section \<open>Open conclusions require negating their universal closure\<close>

text \<open>
  If S ⊬ A in the λI calculus, then S∪{¬UC(A)} is λI-consistent, where
  UC(A) universally closes the distinct free variables of A. The added
  formula is NOT ¬A when A is open. Since S ⊢ UC(A) iff S ⊢ A, the
  closed-formula result applies without restricting S or A to closed
  formulas. This prepares the countermodel construction only.
\<close>

theorem book_lambda_I_consistent_insert_not_universal_closure:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and nonderivable: "\<not> book_lambda_I_derivable \<Sigma> G S A"
  shows "book_lambda_I_consistent \<Sigma> G
    (insert (book_not G (book_lambda_I_universal_closure G A)) S)"
proof -
  have closure_language: "book_lambda_I_formula \<Sigma> G (book_lambda_I_universal_closure G A)"
    by (rule book_lambda_I_universal_closure_language[OF al])
  have closure_nonderivable: "\<not> book_lambda_I_derivable \<Sigma> G S (book_lambda_I_universal_closure G A)"
  proof
    assume derived: "book_lambda_I_derivable \<Sigma> G S (book_lambda_I_universal_closure G A)"
    have original: "book_lambda_I_derivable \<Sigma> G S A"
      by (rule iffD2[OF book_lambda_I_universal_closure_iff[OF rich al] derived])
    show False by (rule notE[OF nonderivable original])
  qed
  show ?thesis by (rule book_lambda_I_consistent_insert_not[
    OF rich closure_language book_lambda_I_universal_closure_closed closure_nonderivable])
qed

end
