theory Bacon_Book_Disjunction_Background_Decoding
  imports Bacon_Book_Primitive_Disjunction_Axiom_Theory
    Bacon_Book_Primitive_Disjunction_Theory_Derivation Bacon_Book_Disjunction_Formula_Transport
begin

section \<open>The fixed disjunction background decodes to native schemas\<close>

text \<open>
  Every axiom in Π∨ decodes to native OrE, OrI1, or OrI2.
  The elimination schema retains all THREE formula operands and its
  right-associated implication order:
  (P→R)→((Q→R)→((P∨Q)→R)).
  Source: Bacon §5.2, p.104.

  The guarded decoder supplies native typing for each operand. These
  are native axiom instances derivable under every premise set S, not
  conjunction-H theorems, semantic premises, or a λ-definition of ∨.
\<close>

lemma book_disj_decode_target_apply:
  "book_disj_decode (book_disj_target_apply P Q) =
    book_disj_apply (book_disj_decode P) (book_disj_decode Q)"
  by (simp only: book_disj_target_apply_def book_disj_decode_tag_application)

theorem book_disj_decode_axiom:
  assumes member: "A \<in> book_disj_axioms \<Sigma> G"
  shows "book_disj_theory_derivable \<Sigma> G S (book_disj_decode A)"
  using member
proof (induction rule: book_disj_axioms.induct)
  case (Elim P Q R)
  have pl: "book_disj_formula \<Sigma> G (book_disj_decode P)"
    by (rule book_disj_decode_language[OF Elim.hyps(1)])
  have ql: "book_disj_formula \<Sigma> G (book_disj_decode Q)"
    by (rule book_disj_decode_language[OF Elim.hyps(2)])
  have rl: "book_disj_formula \<Sigma> G (book_disj_decode R)"
    by (rule book_disj_decode_language[OF Elim.hyps(3)])
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_target_apply;
    rule book_disj_theory_derivable.OrE[OF pl ql rl])
next
  case (Intro1 P Q)
  have pl: "book_disj_formula \<Sigma> G (book_disj_decode P)"
    by (rule book_disj_decode_language[OF Intro1.hyps(1)])
  have ql: "book_disj_formula \<Sigma> G (book_disj_decode Q)"
    by (rule book_disj_decode_language[OF Intro1.hyps(2)])
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_target_apply;
    rule book_disj_theory_derivable.OrI1[OF pl ql])
next
  case (Intro2 P Q)
  have pl: "book_disj_formula \<Sigma> G (book_disj_decode P)"
    by (rule book_disj_decode_language[OF Intro2.hyps(1)])
  have ql: "book_disj_formula \<Sigma> G (book_disj_decode Q)"
    by (rule book_disj_decode_language[OF Intro2.hyps(2)])
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_target_apply;
    rule book_disj_theory_derivable.OrI2[OF pl ql])
qed

section \<open>Decoding a guarded member of the complete target premise set\<close>

text \<open>
  A selected premise in enc(S)∪Π∨, when typed in the exact target
  signature, decodes to a native consequence of S. For an encoded old
  premise, its individual language guard and decode(enc(A))=A supply
  the native Assumption rule. No language guard on every member of S
  is required; unused malformed premises remain harmless.
\<close>

theorem book_disj_decode_background_premise:
  assumes member: "B \<in> book_disj_encoded_premises \<Sigma> G S"
    and language: "book_conj_formula (book_disj_target_signature \<Sigma>) G B"
  shows "book_disj_theory_derivable \<Sigma> G S (book_disj_decode B)"
proof (cases "B \<in> image book_disj_encode S")
  case True
  obtain A where original: "A \<in> S" and shape: "B = book_disj_encode A" using True by blast
  have decoded_language: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF language])
  have al: "book_disj_formula \<Sigma> G A"
    using decoded_language by (simp only: shape book_disj_decode_encode)
  show ?thesis by (simp only: shape book_disj_decode_encode;
    rule book_disj_theory_derivable.Assumption[OF original al])
next
  case False
  have background: "B \<in> book_disj_axioms \<Sigma> G"
    using member False unfolding book_disj_encoded_premises_def by blast
  show ?thesis by (rule book_disj_decode_axiom[OF background])
qed

end
