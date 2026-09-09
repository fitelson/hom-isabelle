theory Bacon_Source_Local_Deduction
  imports Bacon_Source_Global_Proof_Basics
begin

section \<open>Independent local consequence in the literal source language\<close>

text \<open>
  Write Σ; G; S ⊢H A for a finite proof from assumptions in S, source
  H theorems, and modus ponens.  Each used assumption belongs to ℒ(Σ)
  at proposition type in the fixed stock G.  Source role: the finite-proof
  reading of consequence associated with Bacon–Dorr Figure 2, p.8, and
  the consistent sentence sets in Theorem 3.2, pp.44–45.

  Isabelle representation.  paper_global_derivable is defined directly
  below; it is not an alias for a target consequence relation.  Its MP
  constructor uses the literal Figure 1 paper_imp.  The conclusion's
  language guard follows from the implication premise, as the invariant
  proves.  S need not be finite or consist entirely of well-formed formulas:
  every assumption actually used is individually guarded.

  Status.  There are no local Gen, Inst, or Equivalence constructors.
  Quantifier inferences occur only within theorem leaves, not directly on
  undischarged assumptions.  Richness is not needed for these structural
  results; source applications may separately supply a rich stock.
  No target correspondence, consistency reflection, or model result is
  assumed or asserted by this definition.
\<close>

inductive paper_global_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_term set \<Rightarrow> 'c paper_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> sgterm_in_language paper_logical_type \<Sigma> G A Prop \<Longrightarrow>
    paper_global_derivable \<Sigma> G S A"
| Theorem: "paper_global_H \<Sigma> G A \<Longrightarrow> paper_global_derivable \<Sigma> G S A"
| MP: "paper_global_derivable \<Sigma> G S A \<Longrightarrow>
    paper_global_derivable \<Sigma> G S (paper_imp A B) \<Longrightarrow> paper_global_derivable \<Sigma> G S B"

lemma paper_global_derivable_language:
  assumes derivation: "paper_global_derivable \<Sigma> G S A"
  shows "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
  using derivation
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A S)
  show ?case by (rule Assumption.hyps(2))
next
  case (Theorem A S)
  show ?case by (rule paper_global_H_language[OF Theorem.hyps])
next
  case (MP S A B)
  have parts: "sgterm_in_language paper_logical_type \<Sigma> G A Prop \<and>
    sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule iffD1[OF paper_global_imp_language_iff MP.IH(2)])
  show ?case by (rule conjunct2[OF parts])
qed

lemma paper_global_derivable_mono:
  assumes derivation: "paper_global_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "paper_global_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A S)
  have member: "A \<in> T" by (rule subsetD[OF Assumption.prems Assumption.hyps(1)])
  show ?case by (rule paper_global_derivable.Assumption[OF member Assumption.hyps(2)])
next
  case (Theorem A S)
  show ?case by (rule paper_global_derivable.Theorem[OF Theorem.hyps])
next
  case (MP S A B)
  have left: "paper_global_derivable \<Sigma> G T A" by (rule MP.IH(1)[OF MP.prems])
  have right: "paper_global_derivable \<Sigma> G T (paper_imp A B)" by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule paper_global_derivable.MP[OF left right])
qed

subsection \<open>Every local derivation has a finite subset of assumptions\<close>

text \<open>
  S ⊢H A implies T ⊢H A for some finite T ⊆ S.  The assumption
  case chooses a singleton, a theorem leaf chooses ∅, and MP takes the
  union of its two finite supports.  This concerns assumption support,
  not the distinct finite-variable-prefix bound used to translate proofs.
\<close>

theorem paper_global_derivable_finite_support:
  assumes derivation: "paper_global_derivable \<Sigma> G S A"
  shows "\<exists>T. finite T \<and> T \<subseteq> S \<and> paper_global_derivable \<Sigma> G T A"
  using derivation
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A S)
  have finite: "finite {A}" by simp
  have inclusion: "{A} \<subseteq> S" using Assumption.hyps(1) by simp
  have local: "paper_global_derivable \<Sigma> G {A} A"
    by (rule paper_global_derivable.Assumption[OF insertI1 Assumption.hyps(2)])
  show ?case by (rule exI[where x="{A}"], rule conjI[OF finite conjI[OF inclusion local]])
next
  case (Theorem A S)
  have local: "paper_global_derivable \<Sigma> G {} A" by (rule paper_global_derivable.Theorem[OF Theorem.hyps])
  show ?case by (rule exI[where x="{}"], rule conjI[OF finite.emptyI conjI[OF empty_subsetI local]])
next
  case (MP S A B)
  obtain U where uf: "finite U" and us: "U \<subseteq> S" and left: "paper_global_derivable \<Sigma> G U A"
    using MP.IH(1) by (elim exE conjE)
  obtain V where vf: "finite V" and vs: "V \<subseteq> S" and right: "paper_global_derivable \<Sigma> G V (paper_imp A B)"
    using MP.IH(2) by (elim exE conjE)
  have finite: "finite (U \<union> V)" by (rule finite_UnI[OF uf vf])
  have inclusion: "U \<union> V \<subseteq> S" by (rule Un_least[OF us vs])
  have left': "paper_global_derivable \<Sigma> G (U \<union> V) A"
    by (rule paper_global_derivable_mono[OF left Un_upper1])
  have right': "paper_global_derivable \<Sigma> G (U \<union> V) (paper_imp A B)"
    by (rule paper_global_derivable_mono[OF right Un_upper2])
  have local: "paper_global_derivable \<Sigma> G (U \<union> V) B" by (rule paper_global_derivable.MP[OF left' right'])
  show ?case by (rule exI[where x="U \<union> V"], rule conjI[OF finite conjI[OF inclusion local]])
qed

corollary paper_global_derivable_finite_support_iff:
  "paper_global_derivable \<Sigma> G S A \<longleftrightarrow>
    (\<exists>T. finite T \<and> T \<subseteq> S \<and> paper_global_derivable \<Sigma> G T A)"
proof
  assume derivation: "paper_global_derivable \<Sigma> G S A"
  show "\<exists>T. finite T \<and> T \<subseteq> S \<and> paper_global_derivable \<Sigma> G T A"
    by (rule paper_global_derivable_finite_support[OF derivation])
next
  assume supported: "\<exists>T. finite T \<and> T \<subseteq> S \<and> paper_global_derivable \<Sigma> G T A"
  from supported obtain T where "finite T" and inclusion: "T \<subseteq> S" and local: "paper_global_derivable \<Sigma> G T A"
    by (elim exE conjE)
  show "paper_global_derivable \<Sigma> G S A" by (rule paper_global_derivable_mono[OF local inclusion])
qed

subsection \<open>No assumptions gives exactly source H theoremhood\<close>

lemma paper_global_derivable_from_theorems:
  assumes derivation: "paper_global_derivable \<Sigma> G S A"
    and premises_are_theorems: "\<And>B. B \<in> S \<Longrightarrow> paper_global_H \<Sigma> G B"
  shows "paper_global_H \<Sigma> G A"
  using derivation premises_are_theorems
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A S)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case (Theorem A S)
  show ?case by (rule Theorem.hyps)
next
  case (MP S A B)
  have left: "paper_global_H \<Sigma> G A" by (rule MP.IH(1)[OF MP.prems])
  have right: "paper_global_H \<Sigma> G (paper_imp A B)" by (rule MP.IH(2)[OF MP.prems])
  have language: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule conjunct2[OF iffD1[OF paper_global_imp_language_iff paper_global_H_language[OF right]]])
  show ?case by (rule paper_global_H.MP[OF left right language])
qed

theorem paper_global_derivable_empty_iff:
  "paper_global_derivable \<Sigma> G {} A \<longleftrightarrow> paper_global_H \<Sigma> G A"
proof
  assume local: "paper_global_derivable \<Sigma> G {} A"
  show "paper_global_H \<Sigma> G A"
    by (rule paper_global_derivable_from_theorems[OF local]) simp
next
  assume theorem_H: "paper_global_H \<Sigma> G A"
  show "paper_global_derivable \<Sigma> G {} A" by (rule paper_global_derivable.Theorem[OF theorem_H])
qed

end
