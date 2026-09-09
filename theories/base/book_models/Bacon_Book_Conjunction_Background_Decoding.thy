theory Bacon_Book_Conjunction_Background_Decoding
  imports Bacon_Book_Primitive_Conjunction_Axiom_Theory
    Bacon_Book_Primitive_Conjunction_Theory_Derivation
begin

section \<open>Background assumptions decode to native conjunction axioms\<close>

text \<open>
  Every member of Π∧ decodes to one of the three native schemas.
  Its operands have source typing by the guarded decoder theorem.
  The result is derivable from every native premise set S because the
  three schemas are actual constructors of that independently defined
  calculus, not imported minimal theorems or model assumptions.
\<close>

lemma book_conj_decode_target_apply:
  "book_conj_decode (book_conj_target_apply P Q) = book_conj_apply (book_conj_decode P) (book_conj_decode Q)"
  by (simp only: book_conj_target_apply_def book_conj_decode_tag_application)

theorem book_conj_decode_axiom:
  assumes member: "A \<in> book_conj_axioms \<Sigma> G"
  shows "book_conj_theory_derivable \<Sigma> G S (book_conj_decode A)"
  using member
proof (induction rule: book_conj_axioms.induct)
  case (Intro P Q)
  have pl: "book_conj_formula \<Sigma> G (book_conj_decode P)" by (rule book_conj_decode_language[OF Intro.hyps(1)])
  have ql: "book_conj_formula \<Sigma> G (book_conj_decode Q)" by (rule book_conj_decode_language[OF Intro.hyps(2)])
  show ?case by (simp only: book_conj_decode_imp book_conj_decode_target_apply;
    rule book_conj_theory_derivable.AndI[OF pl ql])
next
  case (Left P Q)
  have pl: "book_conj_formula \<Sigma> G (book_conj_decode P)" by (rule book_conj_decode_language[OF Left.hyps(1)])
  have ql: "book_conj_formula \<Sigma> G (book_conj_decode Q)" by (rule book_conj_decode_language[OF Left.hyps(2)])
  show ?case by (simp only: book_conj_decode_imp book_conj_decode_target_apply;
    rule book_conj_theory_derivable.AndE1[OF pl ql])
next
  case (Right P Q)
  have pl: "book_conj_formula \<Sigma> G (book_conj_decode P)" by (rule book_conj_decode_language[OF Right.hyps(1)])
  have ql: "book_conj_formula \<Sigma> G (book_conj_decode Q)" by (rule book_conj_decode_language[OF Right.hyps(2)])
  show ?case by (simp only: book_conj_decode_imp book_conj_decode_target_apply;
    rule book_conj_theory_derivable.AndE2[OF pl ql])
qed

section \<open>Decoding the complete fixed target premise set\<close>

theorem book_conj_decode_background_premise:
  assumes member: "B \<in> book_conj_encoded_premises \<Sigma> G S"
    and language: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G B"
  shows "book_conj_theory_derivable \<Sigma> G S (book_conj_decode B)"
proof (cases "B \<in> image book_conj_encode S")
  case True
  obtain A where original: "A \<in> S" and shape: "B = book_conj_encode A" using True by blast
  have decoded_language: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF language])
  have al: "book_conj_formula \<Sigma> G A"
    using decoded_language by (simp only: shape book_conj_decode_encode)
  show ?thesis by (simp only: shape book_conj_decode_encode;
    rule book_conj_theory_derivable.Assumption[OF original al])
next
  case False
  have background: "B \<in> book_conj_axioms \<Sigma> G"
    using member False unfolding book_conj_encoded_premises_def by blast
  show ?thesis by (rule book_conj_decode_axiom[OF background])
qed

end
