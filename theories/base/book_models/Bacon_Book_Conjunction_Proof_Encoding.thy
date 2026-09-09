theory Bacon_Book_Conjunction_Proof_Encoding
  imports Bacon_Book_Primitive_Conjunction_Theory_Derivation
    Bacon_Book_Primitive_Conjunction_Axiom_Theory Bacon_Book_Conjunction_Step_Transport
begin

section \<open>Native conjunction proofs become minimal proofs over fixed Π∧\<close>

text \<open>
  S ⊢∧ A implies enc(S)∪Π∧ ⊢printed enc(A), with the distinguished
  conjunction constant declared in the target signature. The twelve
  source constructors are handled directly. AndI, AndE1 and AndE2
  become typed ASSUMPTIONS from the fixed background Π∧.
  Source: Bacon §5.2, p.104, and the printed Chapter 5 calculus.

  Π∧ is not claimed to consist of minimal-H theorems. No substitution
  of its distinguished tag throughout the background is performed.
  The translation preserves the literal minimal wrappers, contextual
  printed β and η, and Gen's antecedent freshness. No richness,
  consistency, model, or semantic conjunction clause is assumed.
\<close>

lemma book_conj_background_in_encoded:
  "book_conj_axioms \<Sigma> G \<subseteq> book_conj_encoded_premises \<Sigma> G S"
  unfolding book_conj_encoded_premises_def by (rule Un_upper2)

theorem book_conj_theory_encode:
  assumes derivation: "book_conj_theory_derivable \<Sigma> G S A"
  shows "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S) (book_conj_encode A)"
  using derivation
proof (induction rule: book_conj_theory_derivable.induct)
  case (Assumption A S)
  have image_member: "book_conj_encode A \<in> image book_conj_encode S"
    by (rule imageI[OF Assumption.hyps(1)])
  have member: "book_conj_encode A \<in> book_conj_encoded_premises \<Sigma> G S"
    using image_member unfolding book_conj_encoded_premises_def by blast
  show ?case by (rule book_printed_theory_derivable.Assumption[
    OF member book_conj_encode_language[OF Assumption.hyps(2)]])
next
  case PC1
  show ?case by (simp only: book_conj_encode_imp; rule book_printed_theory_derivable.PC1[
    OF book_conj_encode_language[OF PC1.hyps(1)] book_conj_encode_language[OF PC1.hyps(2)]])
next
  case PC2
  show ?case by (simp only: book_conj_encode_imp; rule book_printed_theory_derivable.PC2[
    OF book_conj_encode_language[OF PC2.hyps(1)] book_conj_encode_language[OF PC2.hyps(2)]
      book_conj_encode_language[OF PC2.hyps(3)]])
next
  case PC3
  show ?case by (simp only: book_conj_encode_imp book_conj_encode_not;
    rule book_printed_theory_derivable.PC3[
      OF book_conj_encode_language[OF PC3.hyps(1)] book_conj_encode_language[OF PC3.hyps(2)]])
next
  case UI
  show ?case by (simp only: book_conj_encode_imp book_conj_encode.simps book_conj_logical.simps;
    rule book_printed_theory_derivable.UI[
      OF book_conj_encode_language[OF UI.hyps(1)] book_conj_encode_language[OF UI.hyps(2)]])
next
  case (Beta A B S)
  have steps: "named_compatible_step book_printed_beta_contract (book_conj_encode A) (book_conj_encode B) \<or>
    named_compatible_step book_printed_beta_contract (book_conj_encode B) (book_conj_encode A)"
    using Beta.hyps(3) by (blast intro: book_conj_encode_printed_beta_step)
  show ?case by (simp only: book_conj_encode_imp; rule book_printed_theory_derivable.Beta[
    OF book_conj_encode_language[OF Beta.hyps(1)] book_conj_encode_language[OF Beta.hyps(2)] steps])
next
  case (Eta A B S)
  have steps: "named_compatible_step named_eta_contract (book_conj_encode A) (book_conj_encode B) \<or>
    named_compatible_step named_eta_contract (book_conj_encode B) (book_conj_encode A)"
    using Eta.hyps(3) by (blast intro: book_conj_encode_eta_step)
  show ?case by (simp only: book_conj_encode_imp; rule book_printed_theory_derivable.Eta[
    OF book_conj_encode_language[OF Eta.hyps(1)] book_conj_encode_language[OF Eta.hyps(2)] steps])
next
  case (MP S A B)
  have conditional: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S) (book_imp (book_conj_encode A) (book_conj_encode B))"
    using MP.IH(2) by (simp only: book_conj_encode_imp)
  show ?case by (rule book_printed_theory_derivable.MP[
    OF MP.IH(1) conditional book_conj_encode_language[OF MP.hyps(3)]])
next
  case (Gen S A B n)
  have conditional: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S) (book_imp (book_conj_encode A) (book_conj_encode B))"
    using Gen.IH by (simp only: book_conj_encode_imp)
  have fresh: "n \<notin> named_fv (book_conj_encode A)"
    by (simp only: book_conj_encode_fv; rule Gen.hyps(4))
  have generalized: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S)
      (book_imp (book_conj_encode A) (book_all G n (book_conj_encode B)))"
    by (rule book_printed_theory_derivable.Gen[OF conditional
      book_conj_encode_language[OF Gen.hyps(2)] book_conj_encode_language[OF Gen.hyps(3)] fresh])
  show ?case using generalized by (simp only: book_conj_encode_imp book_conj_encode_all)
next
  case (AndI A B S)
  have background: "book_imp (book_conj_encode A)
    (book_imp (book_conj_encode B) (book_conj_target_apply (book_conj_encode A) (book_conj_encode B)))
    \<in> book_conj_axioms \<Sigma> G"
    by (rule book_conj_axioms.Intro[
      OF book_conj_encode_language[OF AndI.hyps(1)] book_conj_encode_language[OF AndI.hyps(2)]])
  have target: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S)
    (book_imp (book_conj_encode A)
      (book_imp (book_conj_encode B) (book_conj_target_apply (book_conj_encode A) (book_conj_encode B))))"
    by (rule book_conj_background_assumption[OF background book_conj_background_in_encoded])
  show ?case using target by (simp only: book_conj_encode_imp book_conj_apply_encode book_conj_target_apply_def)
next
  case (AndE1 A B S)
  have background: "book_imp (book_conj_target_apply (book_conj_encode A) (book_conj_encode B))
    (book_conj_encode A) \<in> book_conj_axioms \<Sigma> G"
    by (rule book_conj_axioms.Left[
      OF book_conj_encode_language[OF AndE1.hyps(1)] book_conj_encode_language[OF AndE1.hyps(2)]])
  have target: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S)
    (book_imp (book_conj_target_apply (book_conj_encode A) (book_conj_encode B)) (book_conj_encode A))"
    by (rule book_conj_background_assumption[OF background book_conj_background_in_encoded])
  show ?case using target by (simp only: book_conj_encode_imp book_conj_apply_encode book_conj_target_apply_def)
next
  case (AndE2 A B S)
  have background: "book_imp (book_conj_target_apply (book_conj_encode A) (book_conj_encode B))
    (book_conj_encode B) \<in> book_conj_axioms \<Sigma> G"
    by (rule book_conj_axioms.Right[
      OF book_conj_encode_language[OF AndE2.hyps(1)] book_conj_encode_language[OF AndE2.hyps(2)]])
  have target: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S)
    (book_imp (book_conj_target_apply (book_conj_encode A) (book_conj_encode B)) (book_conj_encode B))"
    by (rule book_conj_background_assumption[OF background book_conj_background_in_encoded])
  show ?case using target by (simp only: book_conj_encode_imp book_conj_apply_encode book_conj_target_apply_def)
qed

end
