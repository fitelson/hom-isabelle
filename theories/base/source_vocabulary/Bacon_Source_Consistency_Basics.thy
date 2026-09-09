theory Bacon_Source_Consistency_Basics
  imports Bacon_Source_Local_Deduction Bacon_Source_Target_Local_Conversion
begin

section \<open>Source consistency excludes every derivable contradictory pair\<close>

text \<open>
  A source theory S is consistent when there is no formula A for which
  both S ⊢H A and S ⊢H ¬A.  A is not required to be closed.
  Source role: consistency for the sentence-set metatheory of
  Bacon--Dorr Theorem 3.2, with Figure 2's PC and MP consequence rules.

  Isabelle representation.  paper_global_consistent is defined directly
  using the independent paper_global_derivable relation.  Its language
  guards already ensure that each derivable A is well formed in Σ,G.
  Status.  No paper falsity abbreviation is stipulated.  This definition
  is not an alias for target consistency, and no source/target consistency
  equivalence is claimed in this leaf.
\<close>

definition paper_global_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_term set \<Rightarrow> bool" where
  "paper_global_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> (\<exists>A. paper_global_derivable \<Sigma> G S A \<and>
      paper_global_derivable \<Sigma> G S (paper_not A))"

lemma paper_global_consistent_no_pair:
  assumes consistent: "paper_global_consistent \<Sigma> G S"
    and positive: "paper_global_derivable \<Sigma> G S A"
    and negative: "paper_global_derivable \<Sigma> G S (paper_not A)"
  shows False
  using consistent positive negative unfolding paper_global_consistent_def by blast

theorem paper_global_local_explosion:
  assumes positive: "paper_global_derivable \<Sigma> G S A"
    and negative: "paper_global_derivable \<Sigma> G S (paper_not A)"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
  shows "paper_global_derivable \<Sigma> G S B"
proof -
  have A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule paper_global_derivable_language[OF positive])
  let ?T = "SPImp (SPAtom 0) (SPImp (SPNot (SPAtom 0)) (SPAtom 1)) :: nat sprop_template"
  have tautology: "sprop_tautology ?T"
    by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have schema: "paper_global_H \<Sigma> G (paper_imp A (paper_imp (paper_not A) B))"
    using paper_global_PC_two[OF A B tautology] by simp
  have local_schema: "paper_global_derivable \<Sigma> G S (paper_imp A (paper_imp (paper_not A) B))"
    by (rule paper_global_derivable.Theorem[OF schema])
  have implication: "paper_global_derivable \<Sigma> G S (paper_imp (paper_not A) B)"
    by (rule paper_global_derivable.MP[OF positive local_schema])
  show ?thesis by (rule paper_global_derivable.MP[OF negative implication])
qed

corollary paper_global_inconsistent_explosion:
  assumes inconsistent: "\<not> paper_global_consistent \<Sigma> G S"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
  shows "paper_global_derivable \<Sigma> G S B"
proof -
  obtain A where positive: "paper_global_derivable \<Sigma> G S A"
    and negative: "paper_global_derivable \<Sigma> G S (paper_not A)"
    using inconsistent unfolding paper_global_consistent_def by blast
  show ?thesis by (rule paper_global_local_explosion[OF positive negative B])
qed

section \<open>The target contradictory-pair calculation\<close>

text \<open>
  In the target calculus, derivations of A and ¬A yield every target
  formula B ∈ ℒ(Σ), hence the already defined target PObjFalse.
  Isabelle representation.  Typing and signature membership of A come
  from the positive local derivation; the target formula carries its own
  language guard.  PC supplies A → (¬A → B), and local MP applies twice.
  Status.  PObjFalse is the existing target expression, not an asserted
  transcription of a paper ⊥ convention.  No closedness restriction on A
  or semantic premise is used.
\<close>

lemma source_target_set_explosion:
  assumes positive: "pH_set_derivable \<Sigma> \<Gamma> S A"
    and negative: "pH_set_derivable \<Sigma> \<Gamma> S (PNeg A)"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pH_set_derivable \<Sigma> \<Gamma> S B"
proof -
  have A_type: "has_ptype \<Gamma> A Prop" by (rule pH_set_formula[OF positive])
  have A_sig: "pterm_in_signature \<Sigma> A" by (rule pH_set_in_signature[OF positive])
  have B_type: "has_ptype \<Gamma> B Prop" using B unfolding pterm_in_language_def by (rule conjunct1)
  have B_sig: "pterm_in_signature \<Sigma> B" using B unfolding pterm_in_language_def by (rule conjunct2)
  have schema: "pH_proves \<Sigma> \<Gamma> (PImp A (PImp (PNeg A) B))"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PImp A (PImp (PNeg A) B)) Prop"
      by (rule has_ptype.PImp[OF A_type has_ptype.PImp[OF has_ptype.PNeg[OF A_type] B_type]])
    show "pterm_in_signature \<Sigma> (PImp A (PImp (PNeg A) B))" using A_sig B_sig by simp
    show "\<And>v. pprop_eval v (PImp A (PImp (PNeg A) B))" by simp
  qed
  have implication: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PNeg A) B)"
    by (rule pH_set_MP[OF positive pH_set_Theorem[OF schema]])
  show ?thesis by (rule pH_set_MP[OF negative implication])
qed

corollary source_target_set_contradiction_false:
  fixes \<Sigma> :: "'c psignature" and A :: "'c pterm"
  assumes positive: "pH_set_derivable \<Sigma> \<Gamma> S A"
    and negative: "pH_set_derivable \<Sigma> \<Gamma> S (PNeg A)"
  shows "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
proof -
  have false_type: "has_ptype \<Gamma> (PObjFalse :: 'c pterm) Prop"
    unfolding PObjFalse_def PObjTrue_def
    by (intro has_ptype.PNeg has_ptype.PForall has_ptype.PImp has_ptype.PVar) simp_all
  have false_sig: "pterm_in_signature \<Sigma> PObjFalse"
    by (simp add: PObjFalse_def PObjTrue_def)
  have false_language: "pterm_in_language \<Sigma> \<Gamma> PObjFalse Prop"
    unfolding pterm_in_language_def by (rule conjI[OF false_type false_sig])
  show ?thesis by (rule source_target_set_explosion[OF positive negative false_language])
qed

end
