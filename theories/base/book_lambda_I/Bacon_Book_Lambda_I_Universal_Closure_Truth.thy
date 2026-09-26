theory Bacon_Book_Lambda_I_Universal_Closure_Truth
  imports Bacon_Book_Lambda_I_Universal_Closure Bacon_Book_Lambda_I_Models
begin

section \<open>Universal closure preserves all-assignment truth in λI models\<close>

text \<open>
  M ⊨ A iff M ⊨ ∀x.A when x occurs free in A, and hence iff M ⊨ UC(A).
  Truth means satisfaction under every typed total assignment. The
  binder lists are required to be distinct and to consist of free
  variable names of the formula, exactly the λI guard of the syntactic
  closure lemmas; the deterministic universal closure meets it.
\<close>

context book_lambda_I_model
begin

theorem book_formula_valid_all_iff:
  assumes al: "book_lambda_I_formula signature stock A" and occurs: "n \<in> named_fv A"
  shows "book_formula_valid domain stock denote V (book_all stock n A)
    \<longleftrightarrow> book_formula_valid domain stock denote V A"
proof
  assume quantified: "book_formula_valid domain stock denote V (book_all stock n A)"
  show "book_formula_valid domain stock denote V A"
  proof (rule book_formula_validI)
    fix g
    assume typed: "book_env_typed domain stock g"
    have truth: "V (denote g (book_all stock n A))"
      by (rule book_formula_validE[OF quantified typed])
    have all_values: "\<forall>a\<in>domain (stock n). V (denote (g(n := a)) A)"
      using truth by (simp only: all_truth[OF typed al occurs])
    have own_value: "g n \<in> domain (stock n)"
      using typed unfolding book_env_typed_def by (rule spec)
    have own_truth: "V (denote (g(n := g n)) A)"
      by (rule bspec[OF all_values own_value])
    show "V (denote g A)" using own_truth by simp
  qed
next
  assume valid: "book_formula_valid domain stock denote V A"
  show "book_formula_valid domain stock denote V (book_all stock n A)"
  proof (rule book_formula_validI)
    fix g
    assume typed: "book_env_typed domain stock g"
    have all_values: "\<forall>a\<in>domain (stock n). V (denote (g(n := a)) A)"
    proof (rule ballI)
      fix a
      assume member: "a \<in> domain (stock n)"
      have updated: "book_env_typed domain stock (g(n := a))"
        by (rule book_env_update[OF typed member])
      show "V (denote (g(n := a)) A)" by (rule book_formula_validE[OF valid updated])
    qed
    show "V (denote g (book_all stock n A))"
      using all_values by (simp only: all_truth[OF typed al occurs])
  qed
qed

theorem book_formula_valid_all_list_iff:
  assumes al: "book_lambda_I_formula signature stock A"
    and distinct: "distinct ns" and subset: "set ns \<subseteq> named_fv A"
  shows "book_formula_valid domain stock denote V (book_all_list stock ns A)
    \<longleftrightarrow> book_formula_valid domain stock denote V A"
  using distinct subset
proof (induction ns)
  case Nil
  show ?case by (simp only: book_all_list.simps)
next
  case (Cons n ns)
  have tail_distinct: "distinct ns" and tail_subset: "set ns \<subseteq> named_fv A"
    and head_free: "n \<in> named_fv A" and head_outside: "n \<notin> set ns"
    using Cons.prems by auto
  have inner_language: "book_lambda_I_formula signature stock (book_all_list stock ns A)"
    by (rule book_lambda_I_all_list_language[OF al tail_distinct tail_subset])
  have occurs: "n \<in> named_fv (book_all_list stock ns A)"
    using head_free head_outside by (simp add: book_lambda_I_all_list_fv)
  show ?case by (simp only: book_all_list.simps book_formula_valid_all_iff[OF inner_language occurs]
    Cons.IH[OF tail_distinct tail_subset])
qed

theorem book_formula_valid_universal_closure_iff:
  assumes al: "book_lambda_I_formula signature stock A"
  shows "book_formula_valid domain stock denote V (book_lambda_I_universal_closure stock A)
    \<longleftrightarrow> book_formula_valid domain stock denote V A"
  unfolding book_lambda_I_universal_closure_def
  by (rule book_formula_valid_all_list_iff[OF al book_lambda_I_closure_list_distinct book_lambda_I_closure_list_subset])

corollary book_formula_valid_universal_closures_iff:
  assumes language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula signature stock A"
  shows "(\<forall>B\<in>image (book_lambda_I_universal_closure stock) S. book_formula_valid domain stock denote V B)
    \<longleftrightarrow> (\<forall>A\<in>S. book_formula_valid domain stock denote V A)"
  using language by (auto simp: book_formula_valid_universal_closure_iff)

end

end
