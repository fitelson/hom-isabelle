theory Bacon_Book_Model_Class_Theory
  imports Bacon_Book_Theory_Soundness Bacon_Book_Theory_Intersections
begin

section \<open>The common truths of a class of models form a theory\<close>

text \<open>
  Theorem 15.1, p.318, says that the formulas true in every member
  of a class of higher-order models form a higher-order theory.
  First each individual model supplies a theory; then take their
  language-guarded intersection. An empty family gives the degenerate
  theory of all formulas of the declared language, not all raw terms.

  Representation and scope. I indexes a family of full minimal models
  on a common ambient HOL value carrier, with the fixed signature Σ
  and rich variable stock G. Each model has its own typed domains,
  application, interpretation, valuation and witnessed logical values.
  Neither I nor Σ is assumed countable or nonempty. The result is a
  THEORY as in Definition 5.1, not an assertion that an arbitrary
  model's truth set is a substitution-closed LOGIC as in Definition 5.2.
  General-language and richer-signature source cases remain separate.
\<close>

definition book_class_truths where
  "book_class_truths \<Sigma> G I D J W =
    {A. book_theory_formula \<Sigma> G A \<and> (\<forall>i \<in> I. book_formula_valid (D i) G (J i) (W i) A)}"

theorem book_theorem_15_1_full_minimal:
  assumes rich: "sg_rich G"
    and models: "\<And>i. i \<in> I \<Longrightarrow> book_full_minimal_model (D i) (apps i) \<Sigma> G (J i) (W i) (K i)"
  shows "book_higher_order_theory \<Sigma> G (book_class_truths \<Sigma> G I D J W)"
proof -
  let ?T = "\<lambda>i. {A. book_theory_formula \<Sigma> G A \<and> book_formula_valid (D i) G (J i) (W i) A}"
  have theories: "\<forall>T \<in> image ?T I. book_higher_order_theory \<Sigma> G T"
  proof (rule ballI)
    fix T
    assume member: "T \<in> image ?T I"
    obtain i where im: "i \<in> I" and ti: "T = ?T i" using member by (elim imageE)
    interpret M: book_full_minimal_model "D i" "apps i" \<Sigma> G "J i" "W i" "K i"
      by (rule models[OF im])
    have single: "book_higher_order_theory \<Sigma> G M.book_model_truths"
      by (rule M.book_model_truths_form_theory[OF rich])
    show "book_higher_order_theory \<Sigma> G T"
      using single by (simp only: M.book_model_truths_def ti)
  qed
  have intersection: "book_higher_order_theory \<Sigma> G (book_common_theory \<Sigma> G (image ?T I))"
    by (rule book_common_theory_is_theory[OF rich theories])
  have equal: "book_common_theory \<Sigma> G (image ?T I) = book_class_truths \<Sigma> G I D J W"
    by (auto simp: book_common_theory_def book_class_truths_def)
  show ?thesis using intersection by (simp only: equal)
qed

end
