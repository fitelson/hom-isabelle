theory Bacon_Book_Open_Propositional_Decision
  imports Bacon_Book_Theory_Variable_Substitution Bacon_Book_Negation_Conversion
begin

section \<open>Literal negation commutes with free-variable replacement\<close>

text \<open>
  (¬A)[B/n] = ¬(A[B/n]), because the λ-defined negation operator is
  closed. Also, B is free for n in ¬A exactly when it is free for n
  in A. Source: Table 4.1, p.93, and the literal replacement convention.

  Representation. These are syntactic equations about applications of
  book_not_const. They do not identify that operator with an alternative
  definition, and they do not silently rename a binder.
\<close>

lemma book_not_variable_subst:
  "named_subst n B (book_not G A) = book_not G (named_subst n B A)"
proof -
  have fresh: "n \<notin> named_fv (book_not_const G)"
    by (simp only: book_not_const_closed; simp)
  have fixed: "named_subst n B (book_not_const G) = book_not_const G"
    by (rule named_subst_fresh[OF fresh])
  show ?thesis by (simp only: book_not_def named_subst.simps fixed)
qed

lemma book_not_variable_free_for_iff:
  "named_free_for B n (book_not G A) \<longleftrightarrow> named_free_for B n A"
proof -
  have fresh: "n \<notin> named_fv (book_not_const G)"
    by (simp only: book_not_const_closed; simp)
  have operator_free: "named_free_for B n (book_not_const G)"
    by (rule named_free_for_fresh[OF fresh])
  show ?thesis by (simp add: book_not_def operator_free)
qed

section \<open>Either decision of an open propositional variable generates falsity\<close>

text \<open>
  Put p = book_prop_name G. If S ⊢ p, substituting ⊥ for p gives
  S ⊢ ⊥. If S ⊢ ¬p, substitute T = ⊥→⊥ for p. The result ¬T,
  together with the theorem T, again gives S ⊢ ⊥.
  Source rules: Definition 5.1 and Definition 5.4, pp.98 and 102.

  Scope. S is arbitrary, without a formula guard. The derived variable
  substitution rule is valid for theory-level premises, which assert open
  formulas universally; it is not an MP-only local-assignment rule.
  Thus deciding EVERY open formula as a theorem cannot preserve consistency
  in this calculus. This isolates the open-formula reading of Definition
  15.3, p.319: canonical decisions must instead concern closed formulas
  (or use a separately justified consequence relation). No model or
  consistency premise is used here, and this is not a refutation of the
  overall model-existence theorem.
\<close>

theorem book_theory_open_positive_bottom:
  assumes rich: "sg_rich G"
    and positive: "book_theory_derivable \<Sigma> G S (NVar (book_prop_name G))"
  shows "book_theory_derivable \<Sigma> G S (book_bottom G)"
proof -
  let ?p = "book_prop_name G"
  have ptype: "G ?p = Prop" by (rule book_prop_name_type[OF rich])
  have bottom: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_bottom G) (G ?p)"
    by (simp only: ptype; rule book_bottom_language[OF rich])
  have free_for: "named_free_for (book_bottom G) ?p (NVar ?p)" by simp
  have substituted: "book_theory_derivable \<Sigma> G S (named_subst ?p (book_bottom G) (NVar ?p))"
    by (rule book_theory_variable_substitution[OF rich positive bottom free_for])
  show ?thesis using substituted by simp
qed

theorem book_theory_open_negative_bottom:
  assumes rich: "sg_rich G"
    and negative: "book_theory_derivable \<Sigma> G S (book_not G (NVar (book_prop_name G)))"
  shows "book_theory_derivable \<Sigma> G S (book_bottom G)"
proof -
  let ?p = "book_prop_name G"
  let ?T = "book_imp (book_bottom G) (book_bottom G)"
  have ptype: "G ?p = Prop" by (rule book_prop_name_type[OF rich])
  have bottom: "book_theory_formula \<Sigma> G (book_bottom G)"
    by (rule book_bottom_language[OF rich])
  have tl: "book_theory_formula \<Sigma> G ?T" by (rule book_imp_language[OF bottom bottom])
  have replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?T (G ?p)"
    by (simp only: ptype; rule tl)
  have free_for: "named_free_for ?T ?p (book_not G (NVar ?p))"
    by (simp only: book_not_variable_free_for_iff named_free_for.simps)
  have substituted: "book_theory_derivable \<Sigma> G S
    (named_subst ?p ?T (book_not G (NVar ?p)))"
    by (rule book_theory_variable_substitution[OF rich negative replacement free_for])
  have negative_T: "book_theory_derivable \<Sigma> G S (book_not G ?T)"
    using substituted by (simp add: book_not_variable_subst)
  have positive_T: "book_theory_derivable \<Sigma> G S ?T"
    by (rule book_theory_imp_refl[OF bottom])
  have unfolding_step: "book_theory_derivable \<Sigma> G S
    (book_imp (book_not G ?T) (book_imp ?T (book_bottom G)))"
    by (rule book_theory_not_unfold[OF rich tl])
  have conditional: "book_theory_derivable \<Sigma> G S (book_imp ?T (book_bottom G))"
    by (rule book_theory_derivable.MP[OF negative_T unfolding_step book_imp_language[OF tl bottom]])
  show ?thesis by (rule book_theory_derivable.MP[OF positive_T conditional bottom])
qed

theorem book_theory_open_propositional_decision:
  assumes rich: "sg_rich G"
    and decided: "book_theory_derivable \<Sigma> G S (NVar (book_prop_name G)) \<or>
      book_theory_derivable \<Sigma> G S (book_not G (NVar (book_prop_name G)))"
  shows "book_theory_derivable \<Sigma> G S (book_bottom G)"
proof (rule disjE[OF decided])
  assume positive: "book_theory_derivable \<Sigma> G S (NVar (book_prop_name G))"
  show ?thesis by (rule book_theory_open_positive_bottom[OF rich positive])
next
  assume negative: "book_theory_derivable \<Sigma> G S (book_not G (NVar (book_prop_name G)))"
  show ?thesis by (rule book_theory_open_negative_bottom[OF rich negative])
qed

section \<open>The all-open-formula reading of negation completeness\<close>

text \<open>
  Definition 15.3, p.319, quantifies over every formula. If a theory
  satisfies that condition, it contains ⊥: apply it to the open variable
  p and use the preceding decision theorem. Thus that completion condition
  cannot describe a consistent theory with global Gen. This does not
  refute Theorem 15.3's model-existence conclusion. Universal closure
  provides a consequence-preserving reduction to closed premises.
  The required closed-formula completion and model construction remain
  separate obligations, with the final arbitrary-theory scope retained.
\<close>

theorem book_theory_all_open_decisions_bottom:
  assumes rich: "sg_rich G" and theory_ok: "book_higher_order_theory \<Sigma> G T"
    and complete: "\<And>A. book_theory_formula \<Sigma> G A \<Longrightarrow> A \<in> T \<or> book_not G A \<in> T"
  shows "book_bottom G \<in> T"
proof -
  let ?p = "NVar (book_prop_name G)"
  have pl: "book_theory_formula \<Sigma> G ?p"
    using book_language_Var[where L=book_minimal_logical_type and \<Lambda>=UNIV
        and \<Sigma>=\<Sigma> and G=G and n="book_prop_name G"]
    by (simp only: book_prop_name_type[OF rich])
  have npl: "book_theory_formula \<Sigma> G (book_not G ?p)"
    by (rule book_not_language[OF rich pl])
  have decision: "book_theory_derivable \<Sigma> G T ?p \<or>
      book_theory_derivable \<Sigma> G T (book_not G ?p)"
    using complete[OF pl]
    by (blast intro: book_theory_derivable.Assumption[OF _ pl]
        book_theory_derivable.Assumption[OF _ npl])
  have contradiction: "book_theory_derivable \<Sigma> G T (book_bottom G)"
    by (rule book_theory_open_propositional_decision[OF rich decision])
  show ?thesis by (rule book_theory_contains_derivation[OF theory_ok contradiction subset_refl])
qed

end
