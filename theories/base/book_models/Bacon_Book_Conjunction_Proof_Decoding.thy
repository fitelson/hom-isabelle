theory Bacon_Book_Conjunction_Proof_Decoding
  imports Bacon_Book_Primitive_Conjunction_Theory_Derivation
    Bacon_Book_Printed_Theory_Derivation Bacon_Book_Conjunction_Step_Transport
begin

section \<open>Reflecting a printed target proof through the typed-tag decoder\<close>

text \<open>
  A proof T ⊢printed A in the fixed target signature decodes to
  S ⊢∧ decode(A), provided each USED, typed premise B of T already
  has a decoded proof from S. Source role: a fixed-background encoding
  of the primitive conjunction schemas in Bacon, §5.2, p.104.

  Representation. The callback includes B's target-language guard, so
  unused malformed terms in T impose no proof obligation. Every typing
  fact used for decoding has the exact book_conj_target_signature Σ
  guard; raw target typing alone would not exclude a wrong-type tag.
  Implication, negation and universal wrappers decode structurally, with
  the same binder names. The β and η cases preserve immediate steps,
  not an assumed conversion-chain axiom.

  This is induction over all nine printed target constructors. The richer
  calculus is independently declared; no model, consistency, richness,
  Π-theoremhood, tag substitution, or encoding-based rule is assumed.
  The callback's eventual discharge for encoded premises and Π is separate.
\<close>

theorem book_conj_decode_printed_proof:
  fixes \<Sigma> :: "'c ssignature"
  assumes derivation: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G T A"
    and premise_reflection: "\<And>B. B \<in> T \<Longrightarrow>
      book_printed_theory_formula (book_conj_target_signature \<Sigma>) G B \<Longrightarrow>
      book_conj_theory_derivable \<Sigma> G S (book_conj_decode B)"
  shows "book_conj_theory_derivable \<Sigma> G S (book_conj_decode A)"
  using derivation premise_reflection
proof (induction rule: book_printed_theory_derivable.induct)
  case (Assumption A T)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1,2)])
next
  case (PC1 A B T)
  have al: "book_conj_formula \<Sigma> G (book_conj_decode A)"
    by (rule book_conj_decode_language[OF PC1.hyps(1)])
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF PC1.hyps(2)])
  show ?case by (simp only: book_conj_decode_imp; rule book_conj_theory_derivable.PC1[OF al bl])
next
  case (PC2 A B C T)
  have al: "book_conj_formula \<Sigma> G (book_conj_decode A)"
    by (rule book_conj_decode_language[OF PC2.hyps(1)])
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF PC2.hyps(2)])
  have cl: "book_conj_formula \<Sigma> G (book_conj_decode C)"
    by (rule book_conj_decode_language[OF PC2.hyps(3)])
  show ?case by (simp only: book_conj_decode_imp; rule book_conj_theory_derivable.PC2[OF al bl cl])
next
  case (PC3 A B T)
  have al: "book_conj_formula \<Sigma> G (book_conj_decode A)"
    by (rule book_conj_decode_language[OF PC3.hyps(1)])
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF PC3.hyps(2)])
  show ?case by (simp only: book_conj_decode_imp book_conj_decode_not;
      rule book_conj_theory_derivable.PC3[OF al bl])
next
  case (UI F \<sigma> a T)
  have predicate: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode F) (Arr \<sigma> Prop)"
    by (rule book_conj_decode_language[OF UI.hyps(1)])
  have argument: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode a) \<sigma>"
    by (rule book_conj_decode_language[OF UI.hyps(2)])
  show ?case by (simp only: book_conj_decode_imp book_conj_decode.simps;
      rule book_conj_theory_derivable.UI[OF predicate argument])
next
  case (Beta A B T)
  have al: "book_conj_formula \<Sigma> G (book_conj_decode A)"
    by (rule book_conj_decode_language[OF Beta.hyps(1)])
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF Beta.hyps(2)])
  have steps: "named_compatible_step book_printed_beta_contract (book_conj_decode A) (book_conj_decode B) \<or>
    named_compatible_step book_printed_beta_contract (book_conj_decode B) (book_conj_decode A)"
  proof (rule disjE[OF Beta.hyps(3)])
    assume forward: "named_compatible_step book_printed_beta_contract A B"
    show ?thesis by (rule disjI1; rule book_conj_decode_printed_beta_step[OF forward])
  next
    assume backward: "named_compatible_step book_printed_beta_contract B A"
    show ?thesis by (rule disjI2; rule book_conj_decode_printed_beta_step[OF backward])
  qed
  show ?case by (simp only: book_conj_decode_imp; rule book_conj_theory_derivable.Beta[OF al bl steps])
next
  case (Eta A B T)
  have al: "book_conj_formula \<Sigma> G (book_conj_decode A)"
    by (rule book_conj_decode_language[OF Eta.hyps(1)])
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF Eta.hyps(2)])
  have steps: "named_compatible_step named_eta_contract (book_conj_decode A) (book_conj_decode B) \<or>
    named_compatible_step named_eta_contract (book_conj_decode B) (book_conj_decode A)"
  proof (rule disjE[OF Eta.hyps(3)])
    assume forward: "named_compatible_step named_eta_contract A B"
    show ?thesis by (rule disjI1; rule book_conj_decode_eta_step[OF forward])
  next
    assume backward: "named_compatible_step named_eta_contract B A"
    show ?thesis by (rule disjI2; rule book_conj_decode_eta_step[OF backward])
  qed
  show ?case by (simp only: book_conj_decode_imp; rule book_conj_theory_derivable.Eta[OF al bl steps])
next
  case (MP T A B)
  have positive: "book_conj_theory_derivable \<Sigma> G S (book_conj_decode A)"
    by (rule MP.IH(1)[OF MP.prems])
  have decoded_implication: "book_conj_theory_derivable \<Sigma> G S (book_conj_decode (book_imp A B))"
    by (rule MP.IH(2)[OF MP.prems])
  have implication: "book_conj_theory_derivable \<Sigma> G S (book_conj_imp (book_conj_decode A) (book_conj_decode B))"
    using decoded_implication by (simp only: book_conj_decode_imp)
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF MP.hyps(3)])
  show ?case by (rule book_conj_theory_derivable.MP[OF positive implication bl])
next
  case (Gen T A B n)
  have decoded_implication: "book_conj_theory_derivable \<Sigma> G S (book_conj_decode (book_imp A B))"
    by (rule Gen.IH[OF Gen.prems])
  have implication: "book_conj_theory_derivable \<Sigma> G S (book_conj_imp (book_conj_decode A) (book_conj_decode B))"
    using decoded_implication by (simp only: book_conj_decode_imp)
  have al: "book_conj_formula \<Sigma> G (book_conj_decode A)"
    by (rule book_conj_decode_language[OF Gen.hyps(2)])
  have bl: "book_conj_formula \<Sigma> G (book_conj_decode B)"
    by (rule book_conj_decode_language[OF Gen.hyps(3)])
  have fresh: "n \<notin> named_fv (book_conj_decode A)"
    by (simp only: book_conj_decode_fv; rule Gen.hyps(4))
  show ?case by (simp only: book_conj_decode_imp book_conj_decode_all;
      rule book_conj_theory_derivable.Gen[OF implication al bl fresh])
qed

end
