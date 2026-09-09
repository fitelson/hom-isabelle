theory Bacon_Book_Universal_Closure_Truth
  imports Bacon_Book_Universal_Closure Bacon_Book_Minimal_Validity
begin

section \<open>Universal closure preserves all-assignment truth\<close>

text \<open>
  M ⊨ A iff M ⊨ ∀x.A, and hence iff M ⊨ UC(A).
  Source: Bacon, Definition 15.2 and its universal-closure observation,
  p.317. Here truth means satisfaction under every typed total assignment.
  This is not the pointwise claim M,g ⊨ A iff M,g ⊨ ∀x.A.

  Representation. book_all_list binds its first list entry outermost;
  arbitrary lists, including empty lists and repeated names, are allowed.
  The final closure binds the finite free-variable set of each formula.
  No original closedness, common free-variable bound, or finite premise
  set is required. The semantic scope remains book_full_minimal_model:
  no richer logical signature or arbitrary admitted-language model is
  asserted, and no model-existence theorem is assumed or proved here.
\<close>

context book_full_minimal_model
begin

theorem book_formula_valid_all_iff:
  assumes al: "book_theory_formula signature stock A"
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
      using truth by (simp only: book_all_truth[OF typed al])
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
      using all_values by (simp only: book_all_truth[OF typed al])
  qed
qed

theorem book_formula_valid_all_list_iff:
  assumes al: "book_theory_formula signature stock A"
  shows "book_formula_valid domain stock denote V (book_all_list stock ns A)
    \<longleftrightarrow> book_formula_valid domain stock denote V A"
proof (induction ns)
  case Nil
  show ?case by (simp only: book_all_list.simps)
next
  case (Cons n ns)
  have inner_language: "book_theory_formula signature stock (book_all_list stock ns A)"
    by (rule book_all_list_language[OF al])
  show ?case by (simp only: book_all_list.simps book_formula_valid_all_iff[OF inner_language] Cons.IH)
qed

theorem book_formula_valid_universal_closure_iff:
  assumes al: "book_theory_formula signature stock A"
  shows "book_formula_valid domain stock denote V (book_universal_closure stock A)
    \<longleftrightarrow> book_formula_valid domain stock denote V A"
  unfolding book_universal_closure_def by (rule book_formula_valid_all_list_iff[OF al])

corollary book_formula_valid_universal_closures_iff:
  assumes language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula signature stock A"
  shows "(\<forall>B\<in>image (book_universal_closure stock) S. book_formula_valid domain stock denote V B)
    \<longleftrightarrow> (\<forall>A\<in>S. book_formula_valid domain stock denote V A)"
  using language by (auto simp: book_formula_valid_universal_closure_iff)

end

end
