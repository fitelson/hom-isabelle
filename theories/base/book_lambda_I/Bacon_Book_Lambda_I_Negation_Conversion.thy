theory Bacon_Book_Lambda_I_Negation_Conversion
  imports Bacon_Book_Lambda_I_Conversion
begin

section \<open>Folding and unfolding the literal negation application\<close>

text \<open>
  ¬ = λp.(p→⊥), so ¬A contracts by β to A→⊥. Consequently the
  selected exact-capture β schema gives both ⊢ ¬A→(A→⊥) and
  ⊢ (A→⊥)→¬A (no λI printed/exact correspondence is claimed).
  Source: Bacon, Table 4.1, p.93, and the β schema, pp.97–98.

  Representation. book_not G A remains an application of the closed
  λ-defined operator. We prove a contraction and formula implications,
  not a raw equality of these two syntactic formulas or an identity
  between operators. The selected p may occur freely in A: A is outside
  the redex binder, and the only other subterm of its body is closed ⊥.
  No model, semantic truth lemma, H identification, or added rule is used.
\<close>

lemma book_not_beta_contract:
  "named_beta_contract (book_not G A) (book_imp A (book_bottom G))"
proof -
  let ?p = "book_prop_name G"
  let ?body = "book_imp (NVar ?p) (book_bottom G)"
  have bottom_fresh: "?p \<notin> named_fv (book_bottom G)"
    by (simp only: book_bottom_closed; simp)
  have bottom_free: "named_free_for A ?p (book_bottom G)"
    by (rule named_free_for_fresh[OF bottom_fresh])
  have body_free: "named_free_for A ?p ?body"
    by (simp add: book_imp_def bottom_free)
  have bottom_fixed: "named_subst ?p A (book_bottom G) = book_bottom G"
    by (rule named_subst_fresh[OF bottom_fresh])
  have instantiated: "named_subst ?p A ?body = book_imp A (book_bottom G)"
    by (simp add: book_imp_def bottom_fixed)
  have contraction: "named_beta_contract (NApp (NLam ?p ?body) A) (named_subst ?p A ?body)"
    by (rule named_beta_contract.beta[OF body_free])
  show ?thesis using contraction
    by (simp only: book_not_def book_not_const_def instantiated)
qed

lemma book_not_beta_step:
  "named_compatible_step named_beta_contract (book_not G A) (book_imp A (book_bottom G))"
  by (rule named_compatible_step.root; rule book_not_beta_contract)

theorem book_lambda_I_not_unfold:
  assumes rich: "sg_rich G" and formula: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_not G A) (book_imp A (book_bottom G)))"
proof -
  have negated: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich formula])
  have expanded: "book_lambda_I_formula \<Sigma> G (book_imp A (book_bottom G))"
    by (rule book_lambda_I_imp_language[OF formula book_lambda_I_bottom_language[OF rich]])
  show ?thesis by (rule book_lambda_I_derivable.Beta[OF negated expanded],
      rule disjI1, rule book_not_beta_step)
qed

theorem book_lambda_I_not_fold:
  assumes rich: "sg_rich G" and formula: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp A (book_bottom G)) (book_not G A))"
proof -
  have negated: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich formula])
  have expanded: "book_lambda_I_formula \<Sigma> G (book_imp A (book_bottom G))"
    by (rule book_lambda_I_imp_language[OF formula book_lambda_I_bottom_language[OF rich]])
  show ?thesis by (rule book_lambda_I_derivable.Beta[OF expanded negated],
      rule disjI2, rule book_not_beta_step)
qed

corollary book_lambda_I_not_conversion_pair:
  assumes rich: "sg_rich G" and formula: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp (book_not G A) (book_imp A (book_bottom G))) \<and>
    book_lambda_I_derivable \<Sigma> G S (book_imp (book_imp A (book_bottom G)) (book_not G A))"
  by (rule conjI[OF book_lambda_I_not_unfold[OF rich formula] book_lambda_I_not_fold[OF rich formula]])

text \<open>
  Since ⊢ ⊥→⊥, folding gives ⊢ ¬⊥. This is a proof in the original
  calculus, not an appeal to the truth of ⊤ in a model.
\<close>

theorem book_lambda_I_not_bottom:
  assumes rich: "sg_rich G"
  shows "book_lambda_I_derivable \<Sigma> G S (book_not G (book_bottom G))"
proof -
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have reflexive: "book_lambda_I_derivable \<Sigma> G S (book_imp (book_bottom G) (book_bottom G))"
    by (rule book_lambda_I_imp_refl[OF bottom])
  have folded: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp (book_bottom G) (book_bottom G)) (book_not G (book_bottom G)))"
    by (rule book_lambda_I_not_fold[OF rich bottom])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF reflexive folded book_lambda_I_not_language[OF rich bottom]])
qed

end
