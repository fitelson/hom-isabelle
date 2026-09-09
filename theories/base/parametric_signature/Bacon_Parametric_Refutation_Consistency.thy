theory Bacon_Parametric_Refutation_Consistency
  imports Bacon_Parametric_Lindenbaum
begin

section \<open>Quantified truth, guarded refutation, and consistent negation extension\<close>

text \<open>
  Write ⊤₀ = ∀p(p → p) and ⊥₀ = ¬⊤₀.  We first prove Σ; Γ ⊢H ⊤₀
  by PC and Gen, then derive Σ; Γ ⊢H (¬A → ⊥₀) → A.  Consequently,
  S ⊬H A implies ConH(S ∪ {¬A}) for A:t in ℒ(Σ).
  These are the refutation steps used in the Henkin/Lindenbaum argument of
  Bacon, Chapter 15, and Bacon–Dorr, Theorem 3.2, p.45 n.64.

  Isabelle representation: PObjTrue remains a quantified formula, hence an
  unconstrained atom for pprop_eval.  Its theoremhood is established by the
  quantifier rule; no propositional valuation is stipulated to make it true.

  Status: syntactic theorems for arbitrary signatures and name carriers.
  No semantic completeness, countability, or fresh-name assumption is used.
\<close>

lemma pH_PObjTrue_type:
  "has_ptype \<Gamma> (PObjTrue :: 'a pterm) Prop"
  unfolding PObjTrue_def
  by (intro has_ptype.PForall has_ptype.PImp has_ptype.PVar) simp_all

lemma pH_PObjTrue_signature:
  "pterm_in_signature \<Sigma> PObjTrue"
  by (simp add: PObjTrue_def)

subsection \<open>PC and Gen prove the quantified truth representative\<close>

theorem pH_proves_PObjTrue:
  fixes \<Sigma> :: "'a psignature"
  shows "pH_proves \<Sigma> \<Gamma> PObjTrue"
proof -
  let ?T = "PObjTrue :: 'a pterm"
  let ?P = "PImp ?T ?T"
  let ?Q = "PImp (PVar 0) (PVar 0) :: 'a pterm"
  have T_type: "has_ptype \<Gamma> ?T Prop" by (rule pH_PObjTrue_type)
  have P_type: "has_ptype \<Gamma> ?P Prop" by (rule has_ptype.PImp[OF T_type T_type])
  have zero_type: "has_ptype (Prop # \<Gamma>) (PVar 0 :: 'a pterm) Prop"
    by (rule has_ptype.PVar) simp
  have Q_type: "has_ptype (Prop # \<Gamma>) ?Q Prop"
    by (rule has_ptype.PImp[OF zero_type zero_type])
  have shifted_type: "has_ptype (Prop # \<Gamma>) (pshift ?P) Prop"
    by (rule pshift_preserves_typing[OF P_type])
  have P_sig: "pterm_in_signature \<Sigma> ?P"
    using pH_PObjTrue_signature[where \<Sigma>=\<Sigma>] by simp
  have Q_sig: "pterm_in_signature \<Sigma> ?Q" by simp
  have shifted_sig: "pterm_in_signature \<Sigma> (pshift ?P)"
    using P_sig by (simp add: pshift_def)
  have step_type: "has_ptype (Prop # \<Gamma>) (PImp (pshift ?P) ?Q) Prop"
    by (rule has_ptype.PImp[OF shifted_type Q_type])
  have step_eval: "\<forall>v. pprop_eval v (PImp (pshift ?P) ?Q)"
    by (rule allI) (simp only: pprop_eval.simps; simp)
  have step_taut: "pprop_tautology (Prop # \<Gamma>) (PImp (pshift ?P) ?Q)"
    unfolding pprop_tautology_def by (rule conjI[OF step_type step_eval])
  have step_sig: "pterm_in_signature \<Sigma> (PImp (pshift ?P) ?Q)"
    using shifted_sig Q_sig by simp
  have step: "pH_proves \<Sigma> (Prop # \<Gamma>) (PImp (pshift ?P) ?Q)"
    by (rule pH_proves.PC[OF step_taut step_sig])
  have generalized: "pH_proves \<Sigma> \<Gamma> (PImp ?P (PForall Prop ?Q))"
    by (rule pH_proves.Gen[OF P_type Q_type P_sig Q_sig step])
  have P_eval: "\<forall>v. pprop_eval v ?P"
    by (rule allI) (simp only: pprop_eval.simps; simp)
  have P_taut: "pprop_tautology \<Gamma> ?P"
    unfolding pprop_tautology_def by (rule conjI[OF P_type P_eval])
  have P_theorem: "pH_proves \<Sigma> \<Gamma> ?P" by (rule pH_proves.PC[OF P_taut P_sig])
  have result_sig: "pterm_in_signature \<Sigma> (PForall Prop ?Q)" using Q_sig by simp
  have quantified: "pH_proves \<Sigma> \<Gamma> (PForall Prop ?Q)"
    by (rule pH_proves.MP[OF P_theorem generalized P_sig result_sig])
  show ?thesis using quantified by (simp only: PObjTrue_def)
qed

subsection \<open>The guarded refutation theorem uses proved truth\<close>

theorem pH_refutation_theorem:
  fixes \<Sigma> :: "'a psignature" and A :: "'a pterm"
  assumes A_type: "has_ptype \<Gamma> A Prop"
    and A_sig: "pterm_in_signature \<Sigma> A"
  shows "pH_proves \<Sigma> \<Gamma> (PImp (PImp (PNeg A) PObjFalse) A)"
proof -
  let ?R = "PImp (PImp (PNeg A) PObjFalse) A"
  have neg_type: "has_ptype \<Gamma> (PNeg A) Prop" by (rule has_ptype.PNeg[OF A_type])
  have false_type: "has_ptype \<Gamma> (PObjFalse :: 'a pterm) Prop"
    by (rule pH_lindenbaum_false_type)
  have R_type: "has_ptype \<Gamma> ?R Prop"
    by (rule has_ptype.PImp[OF has_ptype.PImp[OF neg_type false_type] A_type])
  have R_sig: "pterm_in_signature \<Sigma> ?R"
    using A_sig pH_lindenbaum_false_signature[where \<Sigma>=\<Sigma>] by simp
  have guarded_type: "has_ptype \<Gamma> (PImp PObjTrue ?R) Prop"
    by (rule has_ptype.PImp[OF pH_PObjTrue_type R_type])
  have guarded_sig: "pterm_in_signature \<Sigma> (PImp PObjTrue ?R)"
    using pH_PObjTrue_signature[where \<Sigma>=\<Sigma>] R_sig by simp
  have guarded_eval: "\<forall>v. pprop_eval v (PImp PObjTrue ?R)"
    by (rule allI) (simp only: PObjFalse_def pprop_eval.simps; blast)
  have guarded_taut: "pprop_tautology \<Gamma> (PImp PObjTrue ?R)"
    unfolding pprop_tautology_def by (rule conjI[OF guarded_type guarded_eval])
  have guarded_theorem: "pH_proves \<Sigma> \<Gamma> (PImp PObjTrue ?R)"
    by (rule pH_proves.PC[OF guarded_taut guarded_sig])
  show ?thesis by (rule pH_proves.MP
    [OF pH_proves_PObjTrue guarded_theorem pH_PObjTrue_signature R_sig])
qed

lemma pH_set_refutation:
  assumes A_type: "has_ptype \<Gamma> A Prop" and A_sig: "pterm_in_signature \<Sigma> A"
    and refutation: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PNeg A) PObjFalse)"
  shows "pH_set_derivable \<Sigma> \<Gamma> S A"
proof -
  have theorem_R: "pH_proves \<Sigma> \<Gamma> (PImp (PImp (PNeg A) PObjFalse) A)"
    by (rule pH_refutation_theorem[OF A_type A_sig])
  have local_R: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PImp (PNeg A) PObjFalse) A)"
    by (rule pH_set_Theorem[OF theorem_R])
  show ?thesis by (rule pH_set_MP[OF refutation local_R])
qed

subsection \<open>Nonderivability permits adjoining the negation\<close>

theorem pH_consistent_neg_of_not_set_derivable:
  assumes A_type: "has_ptype \<Gamma> A Prop" and A_sig: "pterm_in_signature \<Sigma> A"
    and not_derivable: "\<not> pH_set_derivable \<Sigma> \<Gamma> S A"
  shows "pH_consistent \<Sigma> \<Gamma> (insert (PNeg A) S)"
proof (unfold pH_consistent_def, rule notI)
  assume contradiction:
    "pH_set_derivable \<Sigma> \<Gamma> (insert (PNeg A) S) PObjFalse"
  have neg_type: "has_ptype \<Gamma> (PNeg A) Prop" by (rule has_ptype.PNeg[OF A_type])
  have neg_sig: "pterm_in_signature \<Sigma> (PNeg A)" using A_sig by simp
  have refutation: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PNeg A) PObjFalse)"
    by (rule pH_set_deduction[OF neg_type neg_sig contradiction])
  have derivable: "pH_set_derivable \<Sigma> \<Gamma> S A"
    by (rule pH_set_refutation[OF A_type A_sig refutation])
  show False by (rule notE[OF not_derivable derivable])
qed

text \<open>
  The last theorem needs typing and a signature guard for A, not an extra
  consistency premise for S: nonderivability supplies the needed condition.
  When S is a typed theory, the new premise ¬A is also typed and in ℒ(Σ).
  The proof never treats the quantified subformula ⊤₀ as a fixed-true
  propositional atom; the guarded PC step is discharged by its H theorem.
\<close>

end
