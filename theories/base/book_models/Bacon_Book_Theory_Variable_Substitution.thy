theory Bacon_Book_Theory_Variable_Substitution
  imports Bacon_Book_Theory_Conversion
begin

section \<open>Generalization and free-variable substitution are derived rules\<close>

text \<open>
  From S ⊢ A derive S ⊢ ∀x.A using the closed theorem T = ⊥→⊥:
  first infer T→A, apply the printed antecedent-guarded Gen, then MP
  with T. UI and the immediate β axiom then yield S ⊢ A[B/x]
  whenever B is free for x in A and has x's type.

  Source role: the free-variable part of substitution in Definition 5.2,
  p.99, using only Definition 5.1's rules. This works for theory-level
  assumptions because their formulas are asserted universally. It is not
  a local substitution rule keeping the original values of free variables
  fixed, and it does not justify nonlogical-constant replacement. That
  additional part of least-theory/least-logic identification remains.

  No new rule constructor, arbitrary-tautology axiom, model or deduction
  theorem is introduced. Literal substitution keeps its free-for proviso.
\<close>

lemma book_theory_generalize:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
  shows "book_theory_derivable \<Sigma> G S (book_all G n A)"
proof -
  let ?T = "book_imp (book_bottom G) (book_bottom G)"
  have al: "book_theory_formula \<Sigma> G A" by (rule book_theory_derivable_language[OF derivation rich])
  have bottom: "book_theory_formula \<Sigma> G (book_bottom G)" by (rule book_bottom_language[OF rich])
  have tl: "book_theory_formula \<Sigma> G ?T" by (rule book_imp_language[OF bottom bottom])
  have tautology: "book_theory_derivable \<Sigma> G S ?T" by (rule book_theory_imp_refl[OF bottom])
  have conditional: "book_theory_derivable \<Sigma> G S (book_imp ?T A)"
    by (rule book_theory_imp_weaken[OF derivation tl al])
  have fresh: "n \<notin> named_fv ?T" by (simp add: book_imp_fv book_bottom_closed)
  have generalized: "book_theory_derivable \<Sigma> G S (book_imp ?T (book_all G n A))"
    by (rule book_theory_derivable.Gen[OF conditional tl al fresh])
  show ?thesis by (rule book_theory_derivable.MP[OF tautology generalized book_all_language[OF al]])
qed

theorem book_theory_variable_substitution:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
    and replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G n)"
    and free_for: "named_free_for B n A"
  shows "book_theory_derivable \<Sigma> G S (named_subst n B A)"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_theory_derivable_language[OF derivation rich])
  have predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLam n A) (Arr (G n) Prop)"
    by (rule book_language_Lam[OF al])
  have redex_language: "book_theory_formula \<Sigma> G (NApp (NLam n A) B)"
    by (rule book_language_App[OF predicate replacement])
  have result_language: "book_theory_formula \<Sigma> G (named_subst n B A)"
    by (simp only: book_language_UNIV;
      rule named_subst_language[OF book_language_named[OF al] book_language_named[OF replacement]])
  have generalized: "book_theory_derivable \<Sigma> G S (book_all G n A)"
    by (rule book_theory_generalize[OF rich derivation])
  have ui_instance: "book_theory_derivable \<Sigma> G S
    (book_imp (book_all G n A) (NApp (NLam n A) B))"
    by (simp only: book_all_def; rule book_theory_derivable.UI[OF predicate replacement])
  have redex: "book_theory_derivable \<Sigma> G S (NApp (NLam n A) B)"
    by (rule book_theory_derivable.MP[OF generalized ui_instance redex_language])
  have beta: "book_theory_derivable \<Sigma> G S
    (book_imp (NApp (NLam n A) B) (named_subst n B A))"
    by (rule book_theory_derivable.Beta[OF redex_language result_language], rule disjI1,
      rule named_compatible_step.root, rule named_beta_contract.beta[OF free_for])
  show ?thesis by (rule book_theory_derivable.MP[OF redex beta result_language])
qed

corollary book_theory_free_variable_closed:
  assumes rich: "sg_rich G" and theory_ok: "book_higher_order_theory \<Sigma> G T"
    and member: "A \<in> T"
    and replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G n)"
    and free_for: "named_free_for B n A"
  shows "named_subst n B A \<in> T"
proof -
  have al: "book_theory_formula \<Sigma> G A"
    using theory_ok member unfolding book_higher_order_theory_def by blast
  have derivation: "book_theory_derivable \<Sigma> G T A"
    by (rule book_theory_derivable.Assumption[OF member al])
  have substituted: "book_theory_derivable \<Sigma> G T (named_subst n B A)"
    by (rule book_theory_variable_substitution[OF rich derivation replacement free_for])
  show ?thesis by (rule book_theory_contains_derivation[OF theory_ok substituted subset_refl])
qed

end
