theory Bacon_Book_Disjunction_Proof_Decoding
  imports Bacon_Book_Primitive_Disjunction_Theory_Derivation
    Bacon_Book_Primitive_Conjunction_Theory_Derivation Bacon_Book_Disjunction_Step_Transport
begin

section \<open>Reflecting proofs from the conjunction target\<close>

text \<open>
  If T⊢∧A in the exact tagged signature, then S⊢∧∨decode(A)
  whenever each USED, typed premise B∈T has a native proof from S.
  The callback retains the target-language guard, so unused malformed
  premises impose no extra obligation. Every decoding of a typed term
  retains the exact signature, excluding wrong-type tag occurrences.

  The proof is induction over the twelve native target constructors.
  The three inherited conjunction schemas become native conjunction
  schemas again. No model, richness, consistency, Π-theoremhood or
  substitution of the distinguished tag is assumed. This implements the
  primitive extension of §5.2, p.104, without adding a decoding rule to
  either independent calculus.
\<close>

theorem book_disj_decode_conjunction_proof:
  fixes \<Sigma> :: "'c ssignature"
  assumes derivation: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G T A"
    and premise_reflection: "\<And>B. B \<in> T \<Longrightarrow>
      book_conj_formula (book_disj_target_signature \<Sigma>) G B \<Longrightarrow>
      book_disj_theory_derivable \<Sigma> G S (book_disj_decode B)"
  shows "book_disj_theory_derivable \<Sigma> G S (book_disj_decode A)"
  using derivation premise_reflection
proof (induction rule: book_conj_theory_derivable.induct)
  case (Assumption A T)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1,2)])
next
  case (PC1 A B T)
  have al: "book_disj_formula \<Sigma> G (book_disj_decode A)"
    by (rule book_disj_decode_language[OF PC1.hyps(1)])
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF PC1.hyps(2)])
  show ?case by (simp only: book_disj_decode_imp; rule book_disj_theory_derivable.PC1[OF al bl])
next
  case (PC2 A B C T)
  have al: "book_disj_formula \<Sigma> G (book_disj_decode A)"
    by (rule book_disj_decode_language[OF PC2.hyps(1)])
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF PC2.hyps(2)])
  have cl: "book_disj_formula \<Sigma> G (book_disj_decode C)"
    by (rule book_disj_decode_language[OF PC2.hyps(3)])
  show ?case by (simp only: book_disj_decode_imp; rule book_disj_theory_derivable.PC2[OF al bl cl])
next
  case (PC3 A B T)
  have al: "book_disj_formula \<Sigma> G (book_disj_decode A)"
    by (rule book_disj_decode_language[OF PC3.hyps(1)])
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF PC3.hyps(2)])
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_not;
      rule book_disj_theory_derivable.PC3[OF al bl])
next
  case (UI F \<sigma> a T)
  have predicate: "book_in_language book_disj_logical_type UNIV \<Sigma> G (book_disj_decode F) (Arr \<sigma> Prop)"
    by (rule book_disj_decode_language[OF UI.hyps(1)])
  have argument: "book_in_language book_disj_logical_type UNIV \<Sigma> G (book_disj_decode a) \<sigma>"
    by (rule book_disj_decode_language[OF UI.hyps(2)])
  show ?case by (simp only: book_disj_decode_imp book_disj_decode.simps;
      rule book_disj_theory_derivable.UI[OF predicate argument])
next
  case (Beta A B T)
  have al: "book_disj_formula \<Sigma> G (book_disj_decode A)"
    by (rule book_disj_decode_language[OF Beta.hyps(1)])
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF Beta.hyps(2)])
  have steps: "named_compatible_step book_printed_beta_contract (book_disj_decode A) (book_disj_decode B) \<or>
    named_compatible_step book_printed_beta_contract (book_disj_decode B) (book_disj_decode A)"
  proof (rule disjE[OF Beta.hyps(3)])
    assume forward: "named_compatible_step book_printed_beta_contract A B"
    show ?thesis by (rule disjI1; rule book_disj_decode_printed_beta_step[OF forward])
  next
    assume backward: "named_compatible_step book_printed_beta_contract B A"
    show ?thesis by (rule disjI2; rule book_disj_decode_printed_beta_step[OF backward])
  qed
  show ?case by (simp only: book_disj_decode_imp; rule book_disj_theory_derivable.Beta[OF al bl steps])
next
  case (Eta A B T)
  have al: "book_disj_formula \<Sigma> G (book_disj_decode A)"
    by (rule book_disj_decode_language[OF Eta.hyps(1)])
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF Eta.hyps(2)])
  have steps: "named_compatible_step named_eta_contract (book_disj_decode A) (book_disj_decode B) \<or>
    named_compatible_step named_eta_contract (book_disj_decode B) (book_disj_decode A)"
  proof (rule disjE[OF Eta.hyps(3)])
    assume forward: "named_compatible_step named_eta_contract A B"
    show ?thesis by (rule disjI1; rule book_disj_decode_eta_step[OF forward])
  next
    assume backward: "named_compatible_step named_eta_contract B A"
    show ?thesis by (rule disjI2; rule book_disj_decode_eta_step[OF backward])
  qed
  show ?case by (simp only: book_disj_decode_imp; rule book_disj_theory_derivable.Eta[OF al bl steps])
next
  case (MP T A B)
  have positive: "book_disj_theory_derivable \<Sigma> G S (book_disj_decode A)"
    by (rule MP.IH(1)[OF MP.prems])
  have decoded_implication: "book_disj_theory_derivable \<Sigma> G S (book_disj_decode (book_conj_imp A B))"
    by (rule MP.IH(2)[OF MP.prems])
  have implication: "book_disj_theory_derivable \<Sigma> G S (book_disj_imp (book_disj_decode A) (book_disj_decode B))"
    using decoded_implication by (simp only: book_disj_decode_imp)
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF MP.hyps(3)])
  show ?case by (rule book_disj_theory_derivable.MP[OF positive implication bl])
next
  case (Gen T A B n)
  have decoded_implication: "book_disj_theory_derivable \<Sigma> G S (book_disj_decode (book_conj_imp A B))"
    by (rule Gen.IH[OF Gen.prems])
  have implication: "book_disj_theory_derivable \<Sigma> G S (book_disj_imp (book_disj_decode A) (book_disj_decode B))"
    using decoded_implication by (simp only: book_disj_decode_imp)
  have al: "book_disj_formula \<Sigma> G (book_disj_decode A)"
    by (rule book_disj_decode_language[OF Gen.hyps(2)])
  have bl: "book_disj_formula \<Sigma> G (book_disj_decode B)"
    by (rule book_disj_decode_language[OF Gen.hyps(3)])
  have fresh: "n \<notin> named_fv (book_disj_decode A)"
    by (simp only: book_disj_decode_fv; rule Gen.hyps(4))
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_all;
      rule book_disj_theory_derivable.Gen[OF implication al bl fresh])
next
  case AndI
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_conj;
    rule book_disj_theory_derivable.AndI[
      OF book_disj_decode_language[OF AndI.hyps(1)] book_disj_decode_language[OF AndI.hyps(2)]])
next
  case AndE1
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_conj;
    rule book_disj_theory_derivable.AndE1[
      OF book_disj_decode_language[OF AndE1.hyps(1)] book_disj_decode_language[OF AndE1.hyps(2)]])
next
  case AndE2
  show ?case by (simp only: book_disj_decode_imp book_disj_decode_conj;
    rule book_disj_theory_derivable.AndE2[
      OF book_disj_decode_language[OF AndE2.hyps(1)] book_disj_decode_language[OF AndE2.hyps(2)]])
qed

end

