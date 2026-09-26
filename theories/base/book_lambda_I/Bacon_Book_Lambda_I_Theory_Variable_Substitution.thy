theory Bacon_Book_Lambda_I_Theory_Variable_Substitution
  imports Bacon_Book_Lambda_I_Conversion Bacon_Book_Lambda_I_Theory_Closure
begin

section \<open>Generalization and free-variable substitution are derived rules\<close>

text \<open>
  From S ⊢ A with x ∈ FV(A) derive S ⊢ ∀x.A using the closed theorem
  T = ⊥→⊥: first infer T→A, apply the guarded λI binder Gen (x not free
  in T, x free in A), then MP with T. UI and the exact-capture β axiom
  then yield S ⊢ A[B/x] whenever B is a λI term free for x in A of x's
  type and x occurs in A; when x is absent, A[B/x] = A and nothing is
  needed.

  Source role: the free-variable part of substitution in Definition 5.2,
  p.99, using only Definition 5.1's rules; in this session those are
  the rules of Definition 9.8, p.197, restricted to λI formulas, i.e.
  the same schemas (see Bacon_Book_Lambda_I_Calculus). This works for theory-level
  assumptions because their formulas are asserted universally. It is not
  a local substitution rule keeping the original values of free variables
  fixed, and it does not justify nonlogical-constant replacement. That
  additional part of least-theory/least-logic identification remains.

  No new rule constructor, arbitrary-tautology axiom, model or deduction
  theorem is introduced. Literal substitution keeps its free-for proviso.
\<close>

text \<open>
  λI variant. Generalization at n presupposes that n occurs free in A,
  since otherwise ∀n.A is not a λI formula. Variable substitution
  therefore splits on that occurrence: when n is absent the substitution
  is the identity, and otherwise the unrestricted argument applies with
  the λI language guards. The replacement term must itself be a λI term.
\<close>

lemma book_lambda_I_generalize:
  assumes rich: "sg_rich G" and derivation: "book_lambda_I_derivable \<Sigma> G S A"
    and occurs: "n \<in> named_fv A"
  shows "book_lambda_I_derivable \<Sigma> G S (book_all G n A)"
proof -
  let ?T = "book_imp (book_bottom G) (book_bottom G)"
  have al: "book_lambda_I_formula \<Sigma> G A" by (rule book_lambda_I_derivable_language[OF derivation rich])
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)" by (rule book_lambda_I_bottom_language[OF rich])
  have tl: "book_lambda_I_formula \<Sigma> G ?T" by (rule book_lambda_I_imp_language[OF bottom bottom])
  have tautology: "book_lambda_I_derivable \<Sigma> G S ?T" by (rule book_lambda_I_imp_refl[OF bottom])
  have conditional: "book_lambda_I_derivable \<Sigma> G S (book_imp ?T A)"
    by (rule book_lambda_I_imp_weaken[OF derivation tl al])
  have fresh: "n \<notin> named_fv ?T" by (simp add: book_imp_fv book_bottom_closed)
  have generalized: "book_lambda_I_derivable \<Sigma> G S (book_imp ?T (book_all G n A))"
    by (rule book_lambda_I_derivable.Gen[OF conditional tl al fresh occurs])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF tautology generalized book_lambda_I_all_language[OF al occurs]])
qed

theorem book_lambda_I_variable_substitution:
  assumes rich: "sg_rich G" and derivation: "book_lambda_I_derivable \<Sigma> G S A"
    and replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G n)"
    and lambda_I_B: "book_lambda_I B"
    and free_for: "named_free_for B n A"
  shows "book_lambda_I_derivable \<Sigma> G S (named_subst n B A)"
proof (cases "n \<in> named_fv A")
  case False
  show ?thesis by (simp only: named_subst_fresh[OF False]; rule derivation)
next
  case True
  note occurs = True
  have al: "book_lambda_I_formula \<Sigma> G A" by (rule book_lambda_I_derivable_language[OF derivation rich])
  have predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLam n A) (Arr (G n) Prop)"
    by (rule book_language_Lam[OF conjunct1[OF al]])
  have predicate_lambda_I: "NLam n A \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G (Arr (G n) Prop)"
    by (rule book_lambda_I_termsI[OF predicate]; simp add: conjunct2[OF al] occurs)
  have replacement_lambda_I: "B \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G (G n)"
    by (rule book_lambda_I_termsI[OF replacement lambda_I_B])
  have redex_language: "book_lambda_I_formula \<Sigma> G (NApp (NLam n A) B)"
    by (rule conjI[OF book_language_App[OF predicate replacement]]; simp add: conjunct2[OF al] occurs lambda_I_B)
  have result_language: "book_lambda_I_formula \<Sigma> G (named_subst n B A)"
    by (rule conjI[OF _ book_lambda_I_subst[OF conjunct2[OF al] lambda_I_B free_for]];
      simp only: book_language_UNIV;
      rule named_subst_language[OF book_language_named[OF conjunct1[OF al]] book_language_named[OF replacement]])
  have generalized: "book_lambda_I_derivable \<Sigma> G S (book_all G n A)"
    by (rule book_lambda_I_generalize[OF rich derivation occurs])
  have ui_instance: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_all G n A) (NApp (NLam n A) B))"
    by (simp only: book_all_def; rule book_lambda_I_derivable.UI[OF predicate_lambda_I replacement_lambda_I])
  have redex: "book_lambda_I_derivable \<Sigma> G S (NApp (NLam n A) B)"
    by (rule book_lambda_I_derivable.MP[OF generalized ui_instance redex_language])
  have beta: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (NApp (NLam n A) B) (named_subst n B A))"
    by (rule book_lambda_I_derivable.Beta[OF redex_language result_language], rule disjI1,
      rule named_compatible_step.root, rule named_beta_contract.beta[OF free_for])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF redex beta result_language])
qed

corollary book_lambda_I_free_variable_closed:
  assumes rich: "sg_rich G" and theory_ok: "book_lambda_I_higher_order_theory \<Sigma> G T"
    and member: "A \<in> T"
    and replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G n)"
    and lambda_I_B: "book_lambda_I B"
    and free_for: "named_free_for B n A"
  shows "named_subst n B A \<in> T"
proof -
  have al: "book_lambda_I_formula \<Sigma> G A"
    using theory_ok member unfolding book_lambda_I_higher_order_theory_def by blast
  have derivation: "book_lambda_I_derivable \<Sigma> G T A"
    by (rule book_lambda_I_derivable.Assumption[OF member al])
  have substituted: "book_lambda_I_derivable \<Sigma> G T (named_subst n B A)"
    by (rule book_lambda_I_variable_substitution[OF rich derivation replacement lambda_I_B free_for])
  show ?thesis by (rule book_lambda_I_contains_derivation[OF theory_ok substituted subset_refl])
qed

end
