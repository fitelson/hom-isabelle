theory Bacon_C_Propositional_Presentation
  imports Bacon_C_Equivalence_Development.Bacon_C_Appendix_A3
    Bacon_Classicism.Bacon_Modal_Derivations
begin

section \<open>Axiom-based C and propositional Equivalence have the same theorems\<close>

text \<open>
  ⊢CE A iff ⊢C A.  In the nontrivial direction, induct on the CE
  derivation.  The propositional Equivalence case translates its premise
  ⊢CE A ↔ B to ⊢C A ↔ B, then invokes the independently proved
  zeroary instance of Appendix A.3 to obtain ⊢C A =ₜ B.
  Source: Bacon–Dorr Appendix A, pp.65–67; compare Bacon, Theorem 6.1,
  pp.126–127, on the equivalence of the axiom and rule presentations.

  Isabelle representation.  CE is the repository's extension of C by the
  propositional, zeroary Equivalence rule, together with MP, Gen, and Inst.
  The C-only Appendix A derivation is imported as a completed dependency;
  it does not depend on this reconciliation theory.

  Scope.  This is equality of the represented theorem predicates for full
  F types and the unrestricted string constant stock.  Primitive Imp, its
  operation bridge, dedicated logical constructors, and the represented H
  existence rule remain source-translation qualifications.  Reconciliation
  with the separate full-vector CEV presentation is not asserted here.
\<close>

theorem CE_proves_to_C:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using derivation
proof (induction rule: CE_proves.induct)
  case (C \<Gamma> A)
  show ?case by (rule C.hyps)
next
  case (PropEquivalence \<Gamma> A B)
  show ?case by (rule C_Appendix_A3_zeroary[OF PropEquivalence.IH])
next
  case (MP \<Gamma> A B)
  show ?case by (rule C_proves.MP[OF MP.IH])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule C_proves.Gen[OF Gen.hyps(1,2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule C_proves.Inst[OF Inst.hyps(1,2) Inst.IH])
qed

theorem CE_proves_iff_C_proves:
  "\<Gamma> \<turnstile>\<^sub>CE A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
proof
  assume "\<Gamma> \<turnstile>\<^sub>CE A"
  then show "\<Gamma> \<turnstile>\<^sub>C A" by (rule CE_proves_to_C)
next
  assume "\<Gamma> \<turnstile>\<^sub>C A"
  then show "\<Gamma> \<turnstile>\<^sub>CE A" by (rule CE_proves.C)
qed

section \<open>The matching MP-based local consequence relations\<close>

text \<open>
  Γ; S ⊢CE A iff Γ; S ⊢C A for the same finite premise list S.
  This follows by translating theorem leaves in the local proof tree.
  Source role: the local-consequence corollary of the presentation
  equivalence above, not an extra local Equivalence or generalization rule.

  Isabelle representation.  CE_derivable below mirrors C_derivable:
  typed assumptions, CE theorem leaves, and MP only.  In particular, neither
  relation applies Gen, Inst, or Equivalence directly to undischarged local
  assumptions.  No new local rule is silently identified with theoremhood.
\<close>

inductive CE_derivable :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool"
  for \<Gamma> :: ctx and \<Delta> :: "oterm list" where
  Assumption: "A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> CE_derivable \<Gamma> \<Delta> A"
| Theorem: "\<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow> CE_derivable \<Gamma> \<Delta> A"
| MP: "CE_derivable \<Gamma> \<Delta> A \<Longrightarrow> CE_derivable \<Gamma> \<Delta> (Imp A B) \<Longrightarrow>
    CE_derivable \<Gamma> \<Delta> B"

lemma CE_derivable_to_C:
  assumes derivation: "CE_derivable \<Gamma> \<Delta> A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  using derivation
proof (induction rule: CE_derivable.induct)
  case (Assumption A)
  show ?case by (rule C_derivable.Assumption[OF Assumption.hyps])
next
  case (Theorem A)
  show ?case by (rule C_derivable.Theorem[OF CE_proves_to_C[OF Theorem.hyps]])
next
  case (MP A B)
  show ?case by (rule C_derivable.Derive_MP[OF MP.IH])
qed

lemma C_derivable_to_CE:
  assumes derivation: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "CE_derivable \<Gamma> \<Delta> A"
  using derivation
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  show ?case by (rule CE_derivable.Assumption[OF Assumption.hyps])
next
  case (Theorem \<Gamma> A \<Delta>)
  show ?case by (rule CE_derivable.Theorem[OF CE_proves.C[OF Theorem.hyps]])
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  show ?case by (rule CE_derivable.MP[OF Derive_MP.IH])
qed

theorem CE_derivable_iff_C_derivable:
  "CE_derivable \<Gamma> \<Delta> A \<longleftrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof
  assume "CE_derivable \<Gamma> \<Delta> A"
  then show "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A" by (rule CE_derivable_to_C)
next
  assume "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  then show "CE_derivable \<Gamma> \<Delta> A" by (rule C_derivable_to_CE)
qed

corollary CE_derivable_formula:
  "CE_derivable \<Gamma> \<Delta> A \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  by (rule C_derivable_formula, rule CE_derivable_to_C, assumption)

end
