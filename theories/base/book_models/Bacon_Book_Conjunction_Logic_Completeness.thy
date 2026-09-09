theory Bacon_Book_Conjunction_Logic_Completeness
  imports Bacon_Book_Conjunction_Logic Bacon_Book_Conjunction_Completeness
begin

section \<open>Soundness and completeness for the independently defined H∧\<close>

text \<open>
  The proof-theoretic identification H∧ = {A : ⊢∧A} now transfers the
  native calculus's checked semantic results to the least logic itself.
  Soundness holds in each independently specified native model on an
  arbitrary carrier. Completeness quantifies over every native model on
  the displayed canonical carrier, not just constructed model images.

  The language is full F with primitive →, ∀ and ∧; G is rich.
  A may be open, and validity means truth at every typed assignment.
  The arbitrary-premise strong completeness result remains the separate
  theorem book_conj_canonical_strong_completeness for S ⊢∧ A.
  No further logical basis or general sublanguage is covered here.
\<close>

context book_conjunction_model
begin

theorem book_conj_H_soundness:
  assumes rich: "sg_rich stock"
    and in_H: "book_conj_H signature stock A"
  shows "book_formula_valid domain stock denote V A"
proof -
  have derivation: "book_conj_theory_derivable signature stock {} A"
    using in_H by (simp only: book_conj_H_iff_theory[OF rich])
  show ?thesis by (rule book_conj_theory_soundness[OF rich derivation]) simp
qed

end

theorem book_conj_H_canonical_completeness:
  assumes rich: "sg_rich G" and al: "book_conj_formula \<Sigma> G A"
  shows "book_conj_H \<Sigma> G A \<longleftrightarrow> book_conj_canonical_consequence \<Sigma> G {} A"
proof -
  have typed_empty: "\<And>B. B \<in> {} \<Longrightarrow> book_conj_formula \<Sigma> G B" by simp
  show ?thesis
    by (simp only: book_conj_H_iff_theory[OF rich]
      book_conj_canonical_strong_completeness[OF rich typed_empty al])
qed

end
