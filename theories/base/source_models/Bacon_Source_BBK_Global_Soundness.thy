theory Bacon_Source_BBK_Global_Soundness
  imports Bacon_Source_BBK_Closed_Soundness
    "Bacon_Source_Vocabulary_Development.Bacon_Source_BBK_Global_Assignments"
begin

context paper_db_bbk_structure
begin

section \<open>Global source theoremhood is sound at total typed assignments\<close>

text \<open>
  If source H proves A in the fixed stock G, every G-typed total
  assignment makes A true in the independently specified source structure.
  Source role: theorem soundness for the represented global calculus,
  corresponding to the soundness direction of Bacon--Dorr Theorem 3.2.

  Isabelle representation.  Construct the reverse target model, choose a
  sufficiently large proof prefix with its typed environment, apply target
  H soundness, then recover source denotation by the guarded source round trip.
  Status.  The result holds in the weaker finite-frame source structure
  on arbitrary carriers and signatures.  No richness or countability is
  required.  The interpretation of total global slots is not yet the
  separate named-variable/adequate-partial-assignment correspondence.
\<close>

theorem paper_db_global_H_soundness:
  assumes derivation: "paper_global_H signature G A"
    and env: "paper_global_env_typed domain G g"
  shows "valuation (denote g A)"
proof -
  interpret Target: pbbk_model signature domain "\<lambda>h M. denote h (pterm_to_paper M)" valuation
    by (rule paper_db_to_pbbk_model[OF paper_db_bbk_structure_axioms])
  obtain N where eventual: "\<forall>m\<ge>N.
    pH_proves signature (source_prefix G m) (paper_to_pterm A) \<and>
    pbbk_env_typed domain (source_prefix G m) g"
    using paper_global_H_target_prefix_with_env[OF derivation env] by (elim exE)
  have selected: "pH_proves signature (source_prefix G N) (paper_to_pterm A) \<and>
    pbbk_env_typed domain (source_prefix G N) g"
    using eventual by blast
  have target_truth: "valuation (denote g (pterm_to_paper (paper_to_pterm A)))"
    by (rule Target.pH_BBK_soundness_at_assignment[OF conjunct1[OF selected] conjunct2[OF selected]])
  have language: "sgterm_in_language paper_logical_type signature G A Prop"
    by (rule paper_global_H_language[OF derivation])
  show ?thesis using target_truth by (simp only: paper_db_global_roundtrip_denotation[OF language env])
qed

lemma paper_db_global_imp_truth:
  assumes A: "sgterm_in_language paper_logical_type signature G A Prop"
    and B: "sgterm_in_language paper_logical_type signature G B Prop"
    and env: "paper_global_env_typed domain G g"
  shows "valuation (denote g (paper_imp A B)) =
    (valuation (denote g A) \<longrightarrow> valuation (denote g B))"
proof -
  let ?m = "max (source_free_bound A) (source_free_bound B)"
  have A_prefix: "sterm_in_language paper_logical_type signature (source_prefix G ?m) A Prop"
    by (rule source_language_in_prefix[OF A]) simp
  have B_prefix: "sterm_in_language paper_logical_type signature (source_prefix G ?m) B Prop"
    by (rule source_language_in_prefix[OF B]) simp
  have prefix_env: "pbbk_env_typed domain (source_prefix G ?m) g"
    by (rule paper_global_env_prefix[OF env])
  show ?thesis by (rule paper_db_imp_truth[OF A_prefix B_prefix prefix_env])
qed

section \<open>Soundness of the independent local source relation\<close>

text \<open>
  If S ⊢H A and every assumed formula in S is true at the same
  G-typed assignment g, then A is true at g.  S may be arbitrary and
  need not be finite or globally well typed as a whole: each assumption
  actually used has its own language guard in paper_global_derivable.

  Isabelle representation.  Induct on Assumption, Theorem, and MP only.
  The MP operand languages follow from the implication derivation's
  language invariant; no local quantifier rule is used.
  Status.  This includes open formulas in the represented global stock,
  not the unproved named adequate-assignment model bridge.
\<close>

theorem paper_db_global_set_soundness:
  assumes derivation: "paper_global_derivable signature G S A"
    and env: "paper_global_env_typed domain G g"
    and assumed_true: "\<And>B. B \<in> S \<Longrightarrow> valuation (denote g B)"
  shows "valuation (denote g A)"
  using derivation assumed_true
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A S)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case (Theorem A S)
  show ?case by (rule paper_db_global_H_soundness[OF Theorem.hyps env])
next
  case (MP S A B)
  have A_true: "valuation (denote g A)" by (rule MP.IH(1)[OF MP.prems])
  have implication_true: "valuation (denote g (paper_imp A B))" by (rule MP.IH(2)[OF MP.prems])
  have implication_language: "sgterm_in_language paper_logical_type signature G (paper_imp A B) Prop"
    by (rule paper_global_derivable_language[OF MP.hyps(2)])
  have languages: "sgterm_in_language paper_logical_type signature G A Prop \<and>
    sgterm_in_language paper_logical_type signature G B Prop"
    by (rule iffD1[OF paper_global_imp_language_iff implication_language])
  have material: "valuation (denote g A) \<longrightarrow> valuation (denote g B)"
    using implication_true
    by (simp only: paper_db_global_imp_truth[OF conjunct1[OF languages] conjunct2[OF languages] env])
  show ?case by (rule mp[OF material A_true])
qed

end

end
