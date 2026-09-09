theory Bacon_H_Only_Classicism_Equivalence
  imports Bacon_H_Only_To_Classicism
    Bacon_H_Only_Classicism_Development.Bacon_HLE_Boolean_Identities
    Bacon_H_Only_Classicism_Development.Bacon_HLE_Identity_Identity
    Bacon_H_Only_Classicism_Development.Bacon_HLE_Quantifier_Identities
begin

section \<open>The three independently defined represented presentations coincide\<close>

text \<open>
  H closed under the Rule of Equivalence, H plus Logical Equivalence,
  and H plus the Boolean and Classical identity axioms have the same
  theorems.  Source: Bacon, Theorem 6.1, pp.126–127; compare the axiom
  presentation and Appendix A of Bacon–Dorr, pp.65–67.

  Isabelle representation.  The inclusion C ⊆ HLE is a proof induction.
  Each added identity axiom is supplied by an independently proved
  HLE instance whose biconditional eligibility premise is in H itself.
  The other inclusions are HLE ⊆ HE, proved directly from the two H-only
  definitions, and HE ⊆ C, proved using C's checked Rule of Equivalence.
  These are not merely the earlier C-based extensions CE and CEV.

  Scope.  The final theorem equates three represented proof predicates:
  full F types, unrestricted string-named constants, source-order fresh
  argument vectors, primitive Imp and dedicated logical constructors, and
  the represented H existence rule.  The Boolean list includes the explicit
  material-implication representation bridge alongside the six source
  Boolean identities.  This is the represented counterpart of Theorem 6.1,
  not a completed literal source-language or named-variable translation,
  a separate relational-type theorem, or a semantic completeness result.
\<close>

theorem C_proves_to_HLE:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>C A"
  shows "HLE_proves \<Gamma> A"
  using derivation
proof (induction rule: C_proves.induct)
  case (H \<Gamma> A)
  show ?case by (rule HLE_proves.H[OF H.hyps])
next
  case (BooleanIdentity A \<Gamma>)
  show ?case by (rule HLE_BooleanIdentity[OF BooleanIdentity.hyps])
next
  case (IdentityIdentity \<Gamma> \<sigma>)
  show ?case by (rule HLE_IdentityIdentity)
next
  case (AbsorbDisjForall \<Gamma> \<sigma>)
  show ?case by (rule HLE_absorb_disj_forall)
next
  case (DistDisjForall \<Gamma> \<sigma>)
  show ?case by (rule HLE_dist_disj_forall)
next
  case (AbsorbConjExists \<Gamma> \<sigma>)
  show ?case by (rule HLE_absorb_conj_exists)
next
  case (DistConjExists \<Gamma> \<sigma>)
  show ?case by (rule HLE_dist_conj_exists)
next
  case (MP \<Gamma> A B)
  show ?case by (rule HLE_proves.MP[OF MP.IH])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule HLE_proves.Gen[OF Gen.hyps(1,2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule HLE_proves.Inst[OF Inst.hyps(1,2) Inst.IH])
qed

theorem HLE_proves_iff_C_proves:
  "HLE_proves \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
proof
  assume "HLE_proves \<Gamma> A"
  then show "\<Gamma> \<turnstile>\<^sub>C A" by (rule HLE_proves_to_C)
next
  assume "\<Gamma> \<turnstile>\<^sub>C A"
  then show "HLE_proves \<Gamma> A" by (rule C_proves_to_HLE)
qed

theorem HE_proves_iff_C_proves:
  "HE_proves \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
proof
  assume "HE_proves \<Gamma> A"
  then show "\<Gamma> \<turnstile>\<^sub>C A" by (rule HE_proves_to_C)
next
  assume derivation: "\<Gamma> \<turnstile>\<^sub>C A"
  show "HE_proves \<Gamma> A" by (rule HLE_proves_to_HE[OF C_proves_to_HLE[OF derivation]])
qed

corollary HE_proves_iff_HLE_proves:
  "HE_proves \<Gamma> A \<longleftrightarrow> HLE_proves \<Gamma> A"
  by (simp only: HE_proves_iff_C_proves HLE_proves_iff_C_proves)

theorem Bacon_Theorem_6_1_represented:
  "HE_proves = HLE_proves \<and> HLE_proves = C_proves"
proof (rule conjI)
  show "HE_proves = HLE_proves"
    by (rule ext, rule ext, rule HE_proves_iff_HLE_proves)
  show "HLE_proves = C_proves"
    by (rule ext, rule ext, rule HLE_proves_iff_C_proves)
qed

end
