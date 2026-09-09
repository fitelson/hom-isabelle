theory Bacon_Source_Named_Local_Forward
  imports Bacon_Source_Named_H_Forward Bacon_Source_Local_Deduction
begin

section \<open>Forward encoding of independent named local consequence\<close>

text \<open>
  S ⊢H A implies ⟦S⟧ ⊢H ⟦A⟧, where ⟦S⟧ is the direct
  image of the premise set under empty-stack named encoding.
  Source role: finite derivability from assumptions and Figure 2,
  Bacon–Dorr pp.7–8.

  Isabelle representation. Both local judgments are independently defined
  by Assumption, Theorem, and MP. Used assumptions carry their language
  guards; theorem leaves use the separately proved named-H encoding.
  MP uses literal encoding of the named Figure 1 implication operator.
  The image includes every member of S, not only a selected finite support.

  Status. Arbitrary premise sets and nonlogical-name carriers. No local
  Gen/Inst rule, model premise, or reverse consequence theorem is added.
  Richness is needed for the forward theorem, not finite support itself.
\<close>

theorem paper_named_derivable_encoding:
  assumes derivation: "paper_named_derivable \<Sigma> G S A" and rich: "sg_rich G"
  shows "paper_global_derivable \<Sigma> G (image (named_to_source G []) S) (named_to_source G [] A)"
  using derivation
proof (induction rule: paper_named_derivable.induct)
  case (Assumption A S)
  have member: "named_to_source G [] A \<in> image (named_to_source G []) S"
    by (rule imageI[OF Assumption.hyps(1)])
  have language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] A) Prop"
    by (rule paper_named_H_encoding_language[OF Assumption.hyps(2)])
  show ?case by (rule paper_global_derivable.Assumption[OF member language])
next
  case (Theorem A S)
  have encoded: "paper_global_H \<Sigma> G (named_to_source G [] A)"
    by (rule paper_named_H_encoding[OF Theorem.hyps rich])
  show ?case by (rule paper_global_derivable.Theorem[OF encoded])
next
  case (MP S A B)
  have implication: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S)
    (paper_imp (named_to_source G [] A) (named_to_source G [] B))"
    using MP.IH(2) by (simp only: named_paper_imp_encoding[OF rich])
  show ?case by (rule paper_global_derivable.MP[OF MP.IH(1) implication])
qed

section \<open>Finite premise support in the named judgment itself\<close>

text \<open>
  A finite proof from S uses some finite U ⊆ S. An assumption selects
  a singleton, a theorem selects ∅, and MP takes the union of its two
  supports. This is distinct from the free-variable prefix needed to
  encode a proof, and does not require the whole premise set to be finite.
\<close>

lemma paper_named_derivable_mono:
  assumes derivation: "paper_named_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "paper_named_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction rule: paper_named_derivable.induct)
  case (Assumption A S)
  have member: "A \<in> T" by (rule subsetD[OF Assumption.prems Assumption.hyps(1)])
  show ?case by (rule paper_named_derivable.Assumption[OF member Assumption.hyps(2)])
next
  case (Theorem A S)
  show ?case by (rule paper_named_derivable.Theorem[OF Theorem.hyps])
next
  case (MP S A B)
  have left: "paper_named_derivable \<Sigma> G T A" by (rule MP.IH(1)[OF MP.prems])
  have right: "paper_named_derivable \<Sigma> G T (named_paper_imp G A B)"
    by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule paper_named_derivable.MP[OF left right MP.hyps(3)])
qed

theorem paper_named_derivable_finite_support:
  assumes derivation: "paper_named_derivable \<Sigma> G S A"
  shows "\<exists>U. finite U \<and> U \<subseteq> S \<and> paper_named_derivable \<Sigma> G U A"
  using derivation
proof (induction rule: paper_named_derivable.induct)
  case (Assumption A S)
  have finite: "finite {A}" by simp
  have inclusion: "{A} \<subseteq> S" using Assumption.hyps(1) by simp
  have local: "paper_named_derivable \<Sigma> G {A} A"
    by (rule paper_named_derivable.Assumption[OF insertI1 Assumption.hyps(2)])
  show ?case by (rule exI[where x="{A}"], rule conjI[OF finite conjI[OF inclusion local]])
next
  case (Theorem A S)
  have local: "paper_named_derivable \<Sigma> G {} A" by (rule paper_named_derivable.Theorem[OF Theorem.hyps])
  show ?case by (rule exI[where x="{}"], rule conjI[OF finite.emptyI conjI[OF empty_subsetI local]])
next
  case (MP S A B)
  obtain U where uf: "finite U" and us: "U \<subseteq> S" and left: "paper_named_derivable \<Sigma> G U A"
    using MP.IH(1) by (elim exE conjE)
  obtain V where vf: "finite V" and vs: "V \<subseteq> S"
    and right: "paper_named_derivable \<Sigma> G V (named_paper_imp G A B)"
    using MP.IH(2) by (elim exE conjE)
  have finite: "finite (U \<union> V)" by (rule finite_UnI[OF uf vf])
  have inclusion: "U \<union> V \<subseteq> S" by (rule Un_least[OF us vs])
  have left': "paper_named_derivable \<Sigma> G (U \<union> V) A"
    by (rule paper_named_derivable_mono[OF left Un_upper1])
  have right': "paper_named_derivable \<Sigma> G (U \<union> V) (named_paper_imp G A B)"
    by (rule paper_named_derivable_mono[OF right Un_upper2])
  have local: "paper_named_derivable \<Sigma> G (U \<union> V) B"
    by (rule paper_named_derivable.MP[OF left' right' MP.hyps(3)])
  show ?case by (rule exI[where x="U \<union> V"], rule conjI[OF finite conjI[OF inclusion local]])
qed

end
