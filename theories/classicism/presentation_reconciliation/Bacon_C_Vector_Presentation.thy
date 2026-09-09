theory Bacon_C_Vector_Presentation
  imports Bacon_C_Propositional_Presentation Bacon_C_Zeta_Permutation
begin

section \<open>The represented vector-rule presentation has exactly C's theorems\<close>

text \<open>
  ⊢CEV A iff ⊢C A, and hence ⊢CE A iff ⊢CEV A.
  Source: Bacon–Dorr Appendix A, pp.65–67; compare Bacon, Theorem 6.1,
  pp.126–127, on the axiom and Equivalence-rule presentations.

  Isabelle representation.  Induct on CEV_proves.  Its CE constructor
  uses the propositional presentation bridge.  Its VectorEquivalence
  constructor uses C_zeta_rule, whose typed premises and ascending-slot
  ζ convention match that constructor exactly.  The independent adapter
  proves the required permutation to source-order application; the
  induction below does not silently reverse a context or argument list.

  Scope.  These are equalities of represented syntactic theorem predicates:
  full F types, string names, and unrestricted constant stock, with the
  primitive-Imp operation bridge and represented H existence rule.  No
  semantic completeness or equivalence of model classes is asserted.
  C-only Appendix A proofs remain in their separate dependency folder.
\<close>

theorem CEV_proves_to_C:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using derivation
proof (induction rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  show ?case by (rule CE_proves_to_C[OF CE.hyps])
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  show ?case by (rule C_zeta_rule[OF VectorEquivalence.hyps(1,2) VectorEquivalence.IH])
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

lemma C_proves_to_CEV:
  "\<Gamma> \<turnstile>\<^sub>C A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  by (rule CEV_proves.CE, rule CE_proves.C, assumption)

theorem CEV_proves_iff_C_proves:
  "\<Gamma> \<turnstile>\<^sub>CEV A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
proof
  assume "\<Gamma> \<turnstile>\<^sub>CEV A"
  then show "\<Gamma> \<turnstile>\<^sub>C A" by (rule CEV_proves_to_C)
next
  assume "\<Gamma> \<turnstile>\<^sub>C A"
  then show "\<Gamma> \<turnstile>\<^sub>CEV A" by (rule C_proves_to_CEV)
qed

corollary CE_proves_iff_CEV_proves:
  "\<Gamma> \<turnstile>\<^sub>CE A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  by (simp only: CE_proves_iff_C_proves CEV_proves_iff_C_proves)

section \<open>The existing one-assumption local relations coincide\<close>

text \<open>
  A ⊢CEV B iff A ⊢C B for the existing MP-based one-assumption
  relations.  Theorem leaves translate using the theoremhood result;
  no Equivalence or quantifier rule is applied to an undischarged local
  assumption.  This is a local-consequence corollary, not a stronger rule.
\<close>

lemma CEV_from_to_C_closure_from:
  assumes derivation: "CEV_from \<Gamma> A B"
  shows "C_closure_from \<Gamma> A B"
  using derivation
proof (induction rule: CEV_from.induct)
  case (Assumption \<Gamma> A)
  show ?case by (rule C_closure_from.Assumption[OF Assumption.hyps])
next
  case (Theorem \<Gamma> B A)
  show ?case by (rule C_closure_from.Theorem[OF CEV_proves_to_C[OF Theorem.hyps]])
next
  case (MP \<Gamma> A B C)
  show ?case by (rule C_closure_from.MP[OF MP.IH])
qed

lemma C_closure_from_to_CEV_from:
  assumes derivation: "C_closure_from \<Gamma> A B"
  shows "CEV_from \<Gamma> A B"
  using derivation
proof (induction rule: C_closure_from.induct)
  case (Assumption \<Gamma> A)
  show ?case by (rule CEV_from.Assumption[OF Assumption.hyps])
next
  case (Theorem \<Gamma> B A)
  show ?case by (rule CEV_from.Theorem[OF C_proves_to_CEV[OF Theorem.hyps]])
next
  case (MP \<Gamma> A B C)
  show ?case by (rule CEV_from.MP[OF MP.IH])
qed

theorem CEV_from_iff_C_closure_from:
  "CEV_from \<Gamma> A B \<longleftrightarrow> C_closure_from \<Gamma> A B"
proof
  assume "CEV_from \<Gamma> A B"
  then show "C_closure_from \<Gamma> A B" by (rule CEV_from_to_C_closure_from)
next
  assume "C_closure_from \<Gamma> A B"
  then show "CEV_from \<Gamma> A B" by (rule C_closure_from_to_CEV_from)
qed

section \<open>Set consequence retains its finite-proof meaning\<close>

text \<open>
  Γ; S ⊢CEV A iff Γ; S ⊢C A.  C_set_derivable uses a finite
  supporting premise list; CEV_set_derivable has assumption, theorem,
  and MP constructors.  The forward induction uses the corresponding C
  set rules.  The converse translates the finite C support list into the
  existing CEV set relation.  S itself is not assumed finite.
\<close>

lemma CEV_set_derivable_to_C_set:
  assumes derivation: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  using derivation
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  show ?case by (rule C_set_Assumption[OF Assumption.hyps])
next
  case (Theorem \<Gamma> A T)
  show ?case by (rule C_set_Theorem[OF CEV_proves_to_C[OF Theorem.hyps]])
next
  case (Derive_MP \<Gamma> T A B)
  show ?case by (rule C_set_MP[OF Derive_MP.IH])
qed

lemma C_derivable_to_CEV_set:
  assumes derivation: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A" and support: "set \<Delta> \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  using derivation support
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  have member: "A \<in> T" by (rule subsetD[OF Assumption.prems Assumption.hyps(1)])
  show ?case by (rule CEV_set_derivable.Assumption[OF member Assumption.hyps(2)])
next
  case (Theorem \<Gamma> A \<Delta>)
  show ?case by (rule CEV_set_derivable.Theorem[OF C_proves_to_CEV[OF Theorem.hyps]])
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have left: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A" by (rule Derive_MP.IH(1)[OF Derive_MP.prems])
  have right: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B" by (rule Derive_MP.IH(2)[OF Derive_MP.prems])
  show ?case by (rule CEV_set_derivable.Derive_MP[OF left right])
qed

lemma C_set_derivable_to_CEV_set:
  assumes derivation: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
proof -
  obtain \<Delta> where support: "set \<Delta> \<subseteq> T" and local: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using derivation unfolding C_set_derivable_def by (elim exE conjE)
  show ?thesis by (rule C_derivable_to_CEV_set[OF local support])
qed

theorem CEV_set_derivable_iff_C_set_derivable:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A \<longleftrightarrow> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  then show "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A" by (rule CEV_set_derivable_to_C_set)
next
  assume "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  then show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A" by (rule C_set_derivable_to_CEV_set)
qed

corollary CE_derivable_iff_CEV_set_derivable:
  "CE_derivable \<Gamma> \<Delta> A \<longleftrightarrow> \<Gamma> ; set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s A"
proof
  assume local: "CE_derivable \<Gamma> \<Delta> A"
  have c_local: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A" by (rule CE_derivable_to_C[OF local])
  show "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s A"
    by (rule C_set_derivable_to_CEV_set[OF C_set_derivable_of_list[OF c_local]])
next
  assume local: "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s A"
  have c_set: "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A" by (rule CEV_set_derivable_to_C_set[OF local])
  show "CE_derivable \<Gamma> \<Delta> A"
    by (rule C_derivable_to_CE[OF C_derivable_of_set_derivable[OF c_set]])
qed

end
