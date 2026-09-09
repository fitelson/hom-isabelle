theory Bacon_Book_Quantifier_Proof_Basics
  imports Bacon_Book_Theory_Consistency Bacon_Book_Existential_Conversion
begin

section \<open>Double-negation elimination from literal negation conversion\<close>

text \<open>
  ∅ ⊢ ¬¬A→A. Unfolding the outer negation gives
  ¬¬A→(¬A→⊥); the separately proved refutation schema gives
  (¬A→⊥)→A. Implication transitivity chains these two theorems.
  Source: Table 4.1 and the propositional and β schemas, pp.93,97–98.
  No semantic tautology principle or open theory discharge is used.
\<close>

theorem book_theory_double_negation_schema:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G {} (book_imp (book_not G (book_not G A)) A)"
proof -
  have nal: "book_theory_formula \<Sigma> G (book_not G A)"
    by (rule book_not_language[OF rich al])
  have nnal: "book_theory_formula \<Sigma> G (book_not G (book_not G A))"
    by (rule book_not_language[OF rich nal])
  have expanded: "book_theory_formula \<Sigma> G (book_imp (book_not G A) (book_bottom G))"
    by (rule book_imp_language[OF nal book_bottom_language[OF rich]])
  have unfolding_step: "book_theory_derivable \<Sigma> G {}
    (book_imp (book_not G (book_not G A)) (book_imp (book_not G A) (book_bottom G)))"
    by (rule book_theory_not_unfold[OF rich nal])
  have refutation: "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
    by (rule book_theory_refutation_schema[OF rich al])
  show ?thesis by (rule book_theory_imp_trans[OF nnal expanded al unfolding_step refutation])
qed

corollary book_theory_double_negation_elim:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and negative: "book_theory_derivable \<Sigma> G S (book_not G (book_not G A))"
  shows "book_theory_derivable \<Sigma> G S A"
proof -
  have schema: "book_theory_derivable \<Sigma> G {} (book_imp (book_not G (book_not G A)) A)"
    by (rule book_theory_double_negation_schema[OF rich al])
  have lifted: "book_theory_derivable \<Sigma> G S (book_imp (book_not G (book_not G A)) A)"
    by (rule book_theory_derivable_mono[OF schema empty_subsetI])
  show ?thesis by (rule book_theory_derivable.MP[OF negative lifted al])
qed

section \<open>η connects primitive quantifier application with its binder notation\<close>

text \<open>
  For closed F:σ→t, put y=book_exists_argument_name G σ.
  The contraction λy.Fy →η F lifts through application by ∀σ.
  The printed η axiom therefore supplies BOTH implications between
  ∀σF and ∀y.Fy. These are formula implications, not an identity
  between logical operators.

  Closedness of F supplies y∉FV(F), and the rich stock supplies
  G(y)=σ. A general open-predicate version without these guards is
  not asserted. The premise set S remains unchanged throughout.
\<close>

theorem book_theory_forall_eta_pair:
  assumes rich: "sg_rich G"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "book_theory_derivable \<Sigma> G S
      (book_imp (NApp (NLogical (SBAll \<sigma>)) F)
        (book_all G (book_exists_argument_name G \<sigma>) (NApp F (NVar (book_exists_argument_name G \<sigma>))))) \<and>
    book_theory_derivable \<Sigma> G S
      (book_imp (book_all G (book_exists_argument_name G \<sigma>) (NApp F (NVar (book_exists_argument_name G \<sigma>))))
        (NApp (NLogical (SBAll \<sigma>)) F))"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  let ?Q = "NApp (NLogical (SBAll \<sigma>)) F"
  let ?B = "book_all G ?y (NApp F (NVar ?y))"
  have ytype: "G ?y = \<sigma>" by (rule book_exists_argument_name_type[OF rich])
  have yfresh: "?y \<notin> named_fv F" by (simp only: closed; simp)
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) \<sigma>"
    by (simp only: book_language_var_iff ytype)
  have body_language: "book_theory_formula \<Sigma> G (NApp F (NVar ?y))"
    by (rule book_language_App[OF predicate variable])
  have binder_language: "book_theory_formula \<Sigma> G ?B"
    by (rule book_all_language[OF body_language])
  have primitive_language: "book_theory_formula \<Sigma> G ?Q"
    by (rule book_language_App[OF book_all_operator_language predicate])
  have contraction: "named_compatible_step named_eta_contract ?B ?Q"
    by (simp only: book_all_def ytype; rule named_compatible_step.App_right,
      rule named_compatible_step.root, rule named_eta_contract.eta[OF yfresh])
  have forward: "book_theory_derivable \<Sigma> G S (book_imp ?Q ?B)"
    by (rule book_theory_derivable.Eta[OF primitive_language binder_language],
      rule disjI2, rule contraction)
  have backward: "book_theory_derivable \<Sigma> G S (book_imp ?B ?Q)"
    by (rule book_theory_derivable.Eta[OF binder_language primitive_language],
      rule disjI1, rule contraction)
  show ?thesis by (rule conjI[OF forward backward])
qed

text \<open>
  Remaining duality step: for Q=λy.¬Fy, derive ¬∃σQ→∀σF.
  The literal existential fold gives ¬P→∃σQ with P=∀y.¬Qy.
  Under ¬∃σQ, closed refutation yields P. UI and β give ¬¬Fy;
  double-negation elimination, theory generalization, and the backward
  η implication above give ∀σF. The final discharged assumption is
  closed because F is closed. This paragraph records the next proof
  obligation; it does not assert the duality theorem.
\<close>

end
