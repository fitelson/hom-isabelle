theory Bacon_Book_Disjunction_Proof_Encoding
  imports Bacon_Book_Primitive_Disjunction_Theory_Derivation
    Bacon_Book_Primitive_Disjunction_Axiom_Theory Bacon_Book_Disjunction_Step_Transport
begin

section \<open>Native disjunction proofs encode over fixed Π∨\<close>

text \<open>
  S⊢∧∨A implies enc(S)∪Π∨⊢∧enc(A). This is induction over
  all fifteen independently specified source constructors. The inherited
  conjunction schemas remain logical axioms; only the three disjunction
  schemas become typed assumptions from the fixed background.
  Source: Chapter 5 and §5.2, p.104.

  No richness, model, consistency or theoremhood of Π∨ is assumed.
  Both primitive connectives keep their distinct syntactic roles. The
  new tag is fixed, and all original binder/freshness guards are preserved.
\<close>

lemma book_disj_background_in_encoded:
  "book_disj_axioms \<Sigma> G \<subseteq> book_disj_encoded_premises \<Sigma> G S"
  unfolding book_disj_encoded_premises_def by (rule Un_upper2)

theorem book_disj_theory_encode:
  assumes derivation: "book_disj_theory_derivable \<Sigma> G S A"
  shows "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_disj_encode A)"
  using derivation
proof (induction rule: book_disj_theory_derivable.induct)
  case (Assumption A S)
  have image_member: "book_disj_encode A \<in> image book_disj_encode S"
    by (rule imageI[OF Assumption.hyps(1)])
  have member: "book_disj_encode A \<in> book_disj_encoded_premises \<Sigma> G S"
    using image_member unfolding book_disj_encoded_premises_def by blast
  show ?case by (rule book_conj_theory_derivable.Assumption[
    OF member book_disj_encode_language[OF Assumption.hyps(2)]])
next
  case PC1
  show ?case by (simp only: book_disj_encode_imp; rule book_conj_theory_derivable.PC1[
    OF book_disj_encode_language[OF PC1.hyps(1)] book_disj_encode_language[OF PC1.hyps(2)]])
next
  case PC2
  show ?case by (simp only: book_disj_encode_imp; rule book_conj_theory_derivable.PC2[
    OF book_disj_encode_language[OF PC2.hyps(1)] book_disj_encode_language[OF PC2.hyps(2)]
      book_disj_encode_language[OF PC2.hyps(3)]])
next
  case PC3
  show ?case by (simp only: book_disj_encode_imp book_disj_encode_not;
    rule book_conj_theory_derivable.PC3[
      OF book_disj_encode_language[OF PC3.hyps(1)] book_disj_encode_language[OF PC3.hyps(2)]])
next
  case UI
  show ?case by (simp only: book_disj_encode_imp book_disj_encode.simps book_disj_logical.simps;
    rule book_conj_theory_derivable.UI[
      OF book_disj_encode_language[OF UI.hyps(1)] book_disj_encode_language[OF UI.hyps(2)]])
next
  case (Beta A B S)
  have steps: "named_compatible_step book_printed_beta_contract (book_disj_encode A) (book_disj_encode B) \<or>
    named_compatible_step book_printed_beta_contract (book_disj_encode B) (book_disj_encode A)"
    using Beta.hyps(3) by (blast intro: book_disj_encode_printed_beta_step)
  show ?case by (simp only: book_disj_encode_imp; rule book_conj_theory_derivable.Beta[
    OF book_disj_encode_language[OF Beta.hyps(1)] book_disj_encode_language[OF Beta.hyps(2)] steps])
next
  case (Eta A B S)
  have steps: "named_compatible_step named_eta_contract (book_disj_encode A) (book_disj_encode B) \<or>
    named_compatible_step named_eta_contract (book_disj_encode B) (book_disj_encode A)"
    using Eta.hyps(3) by (blast intro: book_disj_encode_eta_step)
  show ?case by (simp only: book_disj_encode_imp; rule book_conj_theory_derivable.Eta[
    OF book_disj_encode_language[OF Eta.hyps(1)] book_disj_encode_language[OF Eta.hyps(2)] steps])
next
  case (MP S A B)
  have conditional: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_conj_imp (book_disj_encode A) (book_disj_encode B))"
    using MP.IH(2) by (simp only: book_disj_encode_imp)
  show ?case by (rule book_conj_theory_derivable.MP[
    OF MP.IH(1) conditional book_disj_encode_language[OF MP.hyps(3)]])
next
  case (Gen S A B n)
  have conditional: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_conj_imp (book_disj_encode A) (book_disj_encode B))"
    using Gen.IH by (simp only: book_disj_encode_imp)
  have fresh: "n \<notin> named_fv (book_disj_encode A)"
    by (simp only: book_disj_encode_fv; rule Gen.hyps(4))
  have generalized: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S)
      (book_conj_imp (book_disj_encode A) (book_conj_all G n (book_disj_encode B)))"
    by (rule book_conj_theory_derivable.Gen[OF conditional
      book_disj_encode_language[OF Gen.hyps(2)] book_disj_encode_language[OF Gen.hyps(3)] fresh])
  show ?case using generalized by (simp only: book_disj_encode_imp book_disj_encode_all)
next
  case AndI
  show ?case by (simp only: book_disj_encode_imp book_disj_encode_conj;
    rule book_conj_theory_derivable.AndI[
      OF book_disj_encode_language[OF AndI.hyps(1)] book_disj_encode_language[OF AndI.hyps(2)]])
next
  case AndE1
  show ?case by (simp only: book_disj_encode_imp book_disj_encode_conj;
    rule book_conj_theory_derivable.AndE1[
      OF book_disj_encode_language[OF AndE1.hyps(1)] book_disj_encode_language[OF AndE1.hyps(2)]])
next
  case AndE2
  show ?case by (simp only: book_disj_encode_imp book_disj_encode_conj;
    rule book_conj_theory_derivable.AndE2[
      OF book_disj_encode_language[OF AndE2.hyps(1)] book_disj_encode_language[OF AndE2.hyps(2)]])
next
  case (OrE A B C S)
  let ?A = "book_disj_encode A"
  let ?B = "book_disj_encode B"
  let ?C = "book_disj_encode C"
  let ?F = "book_conj_imp (book_conj_imp ?A ?C)
    (book_conj_imp (book_conj_imp ?B ?C) (book_conj_imp (book_disj_target_apply ?A ?B) ?C))"
  have member: "?F \<in> book_disj_axioms \<Sigma> G"
    by (rule book_disj_axioms.Elim[OF book_disj_encode_language[OF OrE.hyps(1)]
      book_disj_encode_language[OF OrE.hyps(2)] book_disj_encode_language[OF OrE.hyps(3)]])
  have target: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) ?F"
    by (rule book_disj_background_assumption[OF member book_disj_background_in_encoded])
  show ?case using target by (simp only: book_disj_encode_imp book_disj_apply_encode book_disj_target_apply_def)
next
  case (OrI1 A B S)
  let ?A = "book_disj_encode A"
  let ?B = "book_disj_encode B"
  have member: "book_conj_imp ?A (book_disj_target_apply ?A ?B) \<in> book_disj_axioms \<Sigma> G"
    by (rule book_disj_axioms.Intro1[
      OF book_disj_encode_language[OF OrI1.hyps(1)] book_disj_encode_language[OF OrI1.hyps(2)]])
  have target: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_conj_imp ?A (book_disj_target_apply ?A ?B))"
    by (rule book_disj_background_assumption[OF member book_disj_background_in_encoded])
  show ?case using target by (simp only: book_disj_encode_imp book_disj_apply_encode book_disj_target_apply_def)
next
  case (OrI2 A B S)
  let ?A = "book_disj_encode A"
  let ?B = "book_disj_encode B"
  have member: "book_conj_imp ?B (book_disj_target_apply ?A ?B) \<in> book_disj_axioms \<Sigma> G"
    by (rule book_disj_axioms.Intro2[
      OF book_disj_encode_language[OF OrI2.hyps(1)] book_disj_encode_language[OF OrI2.hyps(2)]])
  have target: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_conj_imp ?B (book_disj_target_apply ?A ?B))"
    by (rule book_disj_background_assumption[OF member book_disj_background_in_encoded])
  show ?case using target by (simp only: book_disj_encode_imp book_disj_apply_encode book_disj_target_apply_def)
qed

end

