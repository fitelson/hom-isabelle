theory Bacon_Book_H_Soundness
  imports Bacon_Book_Logic Bacon_Book_Theory_Soundness
begin

section \<open>Soundness of the book's least logic in full minimal models\<close>

text \<open>
  The least-logic/least-theory identification now transfers the independent
  theory soundness proof to H itself. Source: Definitions 5.1–5.3 and
  Theorem 15.1. This retains full F/full λ-language, the minimal primitive
  basis, a rich variable stock, and witnessed logical values. It is not
  a completeness theorem or the general-𝒥/richer-signature soundness claim.
\<close>

context book_full_minimal_model
begin

theorem book_H_soundness:
  assumes rich: "sg_rich stock" and in_H: "book_H signature stock A"
  shows "book_formula_valid domain stock denote V A"
proof -
  have derivation: "book_theory_derivable signature stock {} A"
    using in_H by (simp only: book_H_iff_theory[OF rich])
  show ?thesis by (rule book_axiom_generated_soundness[OF rich derivation])
qed

end
end
