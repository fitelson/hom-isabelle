theory Bacon_Book_Conjunction_Decoded_Background_Truth
  imports Bacon_Book_Conjunction_Decoded_Model Bacon_Book_Primitive_Conjunction_Axiom_Theory
    Bacon_Book_Minimal_Validity
begin

section \<open>The fixed conjunction background is true under decoded interpretation\<close>

text \<open>
  In a supplied native conjunction model, every formula in Π∧ is true
  under the decoded denotation Jᵈg(A)=Jg(dec(A)). The three families
  decode to P→(Q→(P∧Q)), (P∧Q)→P, and (P∧Q)→Q.
  Their truth follows from the ACTUAL primitive implication and conjunction
  clauses at each typed assignment.

  Source: the schemas of §5.2, p.104, and the semantic clauses of
  Definition 15.1, p.314. The formulas may be open. No richness,
  closed-term denotability, theory proof, or premise asserting Π∧ true
  is used. This verifies the fixed background in an arbitrary native
  model; it does not declare its axioms to be minimal-H theorems.
\<close>

context book_conjunction_model
begin

theorem book_conj_decoded_axiom_valid:
  assumes member: "A \<in> book_conj_axioms signature stock"
  shows "book_formula_valid domain stock (book_conj_decoded_denote denote) V A"
  using member
proof (induction rule: book_conj_axioms.induct)
  case (Intro P Q)
  show ?case
  proof (rule book_formula_validI)
    fix g
    assume typed: "book_env_typed domain stock g"
    let ?P = "book_conj_decode P"
    let ?Q = "book_conj_decode Q"
    have pl: "book_conj_formula signature stock ?P"
      by (rule book_conj_decode_language[OF Intro.hyps(1)])
    have ql: "book_conj_formula signature stock ?Q"
      by (rule book_conj_decode_language[OF Intro.hyps(2)])
    have conjunction_language: "book_conj_formula signature stock (book_conj_apply ?P ?Q)"
      by (rule book_conj_apply_language[OF pl ql])
    have inner_language: "book_conj_formula signature stock
      (book_conj_imp ?Q (book_conj_apply ?P ?Q))"
      by (rule book_conj_imp_language[OF ql conjunction_language])
    have truth: "V (denote g (book_conj_imp ?P (book_conj_imp ?Q (book_conj_apply ?P ?Q))))"
      by (simp only: book_conj_imp_truth[OF typed pl inner_language]
        book_conj_imp_truth[OF typed ql conjunction_language]
        book_conj_apply_truth[OF typed pl ql]; blast)
    show "V (book_conj_decoded_denote denote g (book_imp P (book_imp Q (book_conj_target_apply P Q))))"
      using truth by (simp only: book_conj_decoded_denote_def book_conj_decode_imp
      book_conj_target_apply_def book_conj_decode_tag_application)
  qed
next
  case (Left P Q)
  show ?case
  proof (rule book_formula_validI)
    fix g
    assume typed: "book_env_typed domain stock g"
    let ?P = "book_conj_decode P"
    let ?Q = "book_conj_decode Q"
    have pl: "book_conj_formula signature stock ?P"
      by (rule book_conj_decode_language[OF Left.hyps(1)])
    have ql: "book_conj_formula signature stock ?Q"
      by (rule book_conj_decode_language[OF Left.hyps(2)])
    have conjunction_language: "book_conj_formula signature stock (book_conj_apply ?P ?Q)"
      by (rule book_conj_apply_language[OF pl ql])
    have truth: "V (denote g (book_conj_imp (book_conj_apply ?P ?Q) ?P))"
      by (simp only: book_conj_imp_truth[OF typed conjunction_language pl]
        book_conj_apply_truth[OF typed pl ql]; blast)
    show "V (book_conj_decoded_denote denote g (book_imp (book_conj_target_apply P Q) P))"
      using truth by (simp only: book_conj_decoded_denote_def book_conj_decode_imp
      book_conj_target_apply_def book_conj_decode_tag_application)
  qed
next
  case (Right P Q)
  show ?case
  proof (rule book_formula_validI)
    fix g
    assume typed: "book_env_typed domain stock g"
    let ?P = "book_conj_decode P"
    let ?Q = "book_conj_decode Q"
    have pl: "book_conj_formula signature stock ?P"
      by (rule book_conj_decode_language[OF Right.hyps(1)])
    have ql: "book_conj_formula signature stock ?Q"
      by (rule book_conj_decode_language[OF Right.hyps(2)])
    have conjunction_language: "book_conj_formula signature stock (book_conj_apply ?P ?Q)"
      by (rule book_conj_apply_language[OF pl ql])
    have truth: "V (denote g (book_conj_imp (book_conj_apply ?P ?Q) ?Q))"
      by (simp only: book_conj_imp_truth[OF typed conjunction_language ql]
        book_conj_apply_truth[OF typed pl ql]; blast)
    show "V (book_conj_decoded_denote denote g (book_imp (book_conj_target_apply P Q) Q))"
      using truth by (simp only: book_conj_decoded_denote_def book_conj_decode_imp
      book_conj_target_apply_def book_conj_decode_tag_application)
  qed
qed

theorem book_conj_decoded_background_valid:
  "\<forall>A\<in>book_conj_axioms signature stock.
    book_formula_valid domain stock (book_conj_decoded_denote denote) V A"
  by (rule ballI, rule book_conj_decoded_axiom_valid, assumption)

end

end
