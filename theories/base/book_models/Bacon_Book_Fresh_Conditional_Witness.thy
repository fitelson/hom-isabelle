theory Bacon_Book_Fresh_Conditional_Witness
  imports Bacon_Book_Fresh_Witness_Name Bacon_Book_Conditional_Witness
begin

section \<open>One fresh conditional witness over an arbitrary name carrier\<close>

text \<open>
  Write S′=Inl[S], F′=Inl(F), and w=Inr(⋆). If S is consistent
  and F:σ→t is closed, then S′∪{(∃σF′)→F′w} is consistent
  in Inl[Σ][w:σ]. Source role: a single conditional version of
  the witness step in Bacon, Proposition 15.4, p.319.

  Representation. The old signature is embedded in the left summand of
  'c+unit and w is declared at σ in book_fresh_witness_signature.
  The witness formula is one new premise, not a logical rule. S may be
  infinite and open, but its members must be formulas in Σ. No unused
  original name, cardinality bound, conservativity of the new premise,
  simultaneous witness family, or Henkin model is asserted.
\<close>

theorem book_theory_consistent_fresh_conditional_witness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and consistent: "book_theory_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "book_theory_consistent (book_fresh_witness_signature \<Sigma> \<sigma>) G
    (insert (book_witness_axiom G \<sigma> (book_constant_rename Inl F) (Inr ()))
      (image (book_constant_rename Inl) S))"
proof -
  let ?f = "Inl :: 'c \<Rightarrow> 'c + unit"
  let ?old = "\<lambda>\<tau>. image ?f (\<Sigma> \<tau>)"
  let ?S = "image (book_constant_rename ?f) S"
  let ?F = "book_constant_rename ?f F"
  have image_consistent: "book_theory_consistent ?old G ?S"
    by (rule iffD1[OF book_theory_consistent_Inl_rename_iff consistent])
  have image_language: "book_theory_formula ?old G A" if "A \<in> ?S" for A
  proof -
    have in_image: "A \<in> ?S" by (rule that)
    obtain B where member: "B \<in> S" and renamed: "A = book_constant_rename ?f B"
      using in_image by blast
    have original_language: "book_theory_formula \<Sigma> G B" by (rule language[OF member])
    have mapped_language: "book_theory_formula ?old G (book_constant_rename ?f B)"
      by (rule book_constant_rename_image_language[OF original_language])
    show "book_theory_formula ?old G A" by (simp only: renamed; rule mapped_language)
  qed
  have image_predicate: "book_in_language book_minimal_logical_type UNIV ?old G ?F (Arr \<sigma> Prop)"
    by (rule book_constant_rename_image_language[OF predicate])
  have image_closed: "named_fv ?F = {}" by (simp only: book_constant_rename_fv closed)
  have fresh: "Inr () \<notin> ?old \<sigma>" by (rule book_Inr_fresh_image_signature)
  show ?thesis unfolding book_fresh_witness_signature_def
    by (rule book_theory_consistent_conditional_witness[OF rich image_consistent image_language
      image_predicate image_closed fresh])
qed

end
