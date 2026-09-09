theory Bacon_Parametric_Set_Soundness
  imports Bacon_Parametric_H_Soundness Bacon_Parametric_Local_Derivability
begin

section \<open>Soundness with local assumptions\<close>

text \<open>
  Σ; Γ; Δ ⊢ₕ A and 𝔐,g ⊨ B for every B ∈ Δ imply 𝔐,g ⊨ A,
  provided g is a typed assignment in the Σ-model 𝔐.
  Source: Bacon–Dorr, Theorem 3.2, pp. 44–45; Bacon,
  Theorem 15.1, p. 318.

  Isabelle representation: pH_derivable has Assumption, Theorem, and MP
  constructors.  Its invariants retain the typing and signature of every
  used formula.  The Theorem case invokes the established H soundness
  theorem; MP uses its typed and signature-guarded semantic clause.

  Status: arbitrary name and semantic carriers, with no completeness or
  model-existence premise.  Unused members of the assumption collection
  need no additional typing hypothesis for this conditional result.
\<close>

context pbbk_model
begin

theorem pH_derivable_BBK_soundness:
  assumes derivation: "pH_derivable signature \<Gamma> \<Delta> A"
    and env: "pbbk_env_typed domain \<Gamma> g"
    and assumed_true: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> valuation (denote g B)"
  shows "valuation (denote g A)"
  using derivation
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  show ?case by (rule assumed_true[OF Assumption.hyps(1)])
next
  case (Theorem A)
  show ?case by (rule pH_BBK_soundness_at_assignment[OF Theorem.hyps env])
next
  case (MP A B)
  have at: "has_ptype \<Gamma> A Prop" by (rule pH_derivable_formula[OF MP.hyps(1)])
  have implication_type: "has_ptype \<Gamma> (PImp A B) Prop"
    by (rule pH_derivable_formula[OF MP.hyps(2)])
  have typing_parts: "Prop = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    by (rule iffD1[OF ptype_imp_iff[where \<Gamma>=\<Gamma> and A=A and B=B and \<tau>=Prop] implication_type])
  have bt: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF conjunct2[OF typing_parts]])
  have sa: "pterm_in_signature signature A" by (rule pH_derivable_in_signature[OF MP.hyps(1)])
  have implication_sig: "pterm_in_signature signature (PImp A B)"
    by (rule pH_derivable_in_signature[OF MP.hyps(2)])
  have sig_parts: "pterm_in_signature signature A \<and> pterm_in_signature signature B"
    using implication_sig by (simp only: pterm_in_signature.simps)
  have sb: "pterm_in_signature signature B" by (rule conjunct2[OF sig_parts])
  show ?case by (rule pH_BBK_MP[OF at bt sa sb env MP.IH(1,2)])
qed

section \<open>Soundness with an arbitrary set of assumptions\<close>

text \<open>
  Σ; Γ; S ⊢ₕ A and 𝔐,g ⊨ S imply 𝔐,g ⊨ A.
  Source: the finite-proof interpretation of consequence in Bacon,
  Theorem 15.2, p. 318, and Bacon–Dorr, Theorem 3.2, pp. 44–45.

  Isabelle representation: pH_set_derivable supplies a finite supporting
  list Δ with set(Δ) ⊆ S.  Restrict the semantic premises to that list and
  apply local soundness in the same typed assignment.

  Status: S may be infinite or uncountable.  This proves the soundness
  direction of strong completeness, not its model-existence direction.
\<close>

theorem pH_set_BBK_soundness:
  assumes derivation: "pH_set_derivable signature \<Gamma> S A"
    and env: "pbbk_env_typed domain \<Gamma> g"
    and assumed_true: "\<And>B. B \<in> S \<Longrightarrow> valuation (denote g B)"
  shows "valuation (denote g A)"
proof -
  have supported: "\<exists>\<Delta>. set \<Delta> \<subseteq> S \<and> pH_derivable signature \<Gamma> \<Delta> A"
    using derivation unfolding pH_set_derivable_def .
  obtain \<Delta> where data: "set \<Delta> \<subseteq> S \<and> pH_derivable signature \<Gamma> \<Delta> A"
  proof (rule exE[OF supported])
    fix \<Delta>
    assume data: "set \<Delta> \<subseteq> S \<and> pH_derivable signature \<Gamma> \<Delta> A"
    show thesis by (rule that[OF data])
  qed
  have subset: "set \<Delta> \<subseteq> S" by (rule conjunct1[OF data])
  have local: "pH_derivable signature \<Gamma> \<Delta> A" by (rule conjunct2[OF data])
  have local_premises: "valuation (denote g B)" if member: "B \<in> set \<Delta>" for B
  proof -
    have "B \<in> S" by (rule subsetD[OF subset member])
    then show ?thesis by (rule assumed_true)
  qed
  show ?thesis by (rule pH_derivable_BBK_soundness[OF local env local_premises])
qed

corollary pH_set_BBK_satisfies:
  assumes derivation: "pH_set_derivable signature \<Gamma> S A"
    and env: "pbbk_env_typed domain \<Gamma> g"
    and assumed_true: "\<And>B. B \<in> S \<Longrightarrow> pbbk_satisfies g B"
  shows "pbbk_satisfies g A"
proof -
  have truths: "valuation (denote g B)" if member: "B \<in> S" for B
  using assumed_true[OF member] unfolding pbbk_satisfies_def .
  have "valuation (denote g A)"
    by (rule pH_set_BBK_soundness[OF derivation env truths])
  then show ?thesis unfolding pbbk_satisfies_def .
qed

end

end
