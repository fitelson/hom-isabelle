theory Bacon_Book_Negative_Predicate_Generalization
  imports Bacon_Book_Open_Propositional_Decision Bacon_Book_Minimal_Existential_Syntax
begin

section \<open>Moving a negative instance to a specified variable\<close>

text \<open>
  If x∉FV(F), replacing x by y in ¬(F x) gives ¬(F y), and this
  literal replacement is free for x. Thus S ⊢ ¬(F x) implies
  S ⊢ ¬(F y) when x and y have the same type.
  Source: the derived variable-substitution rule from Bacon's
  Definition 5.1, pp.97–98, and Definition 5.2, p.99.

  Representation. The closed negation operator is unchanged. Since x
  does not occur freely in F, replacing x does not enter any free slot
  of F. There is no requirement that y be fresh for F and no assumption
  that F be closed. This is a proof transformation, not α-rebinding.
\<close>

lemma book_negative_predicate_free_for:
  assumes fresh: "x \<notin> named_fv F"
  shows "named_free_for (NVar y) x (book_not G (NApp F (NVar x)))"
proof -
  have head_free: "named_free_for (NVar y) x F"
    by (rule named_free_for_fresh[OF fresh])
  show ?thesis by (simp only: book_not_variable_free_for_iff named_free_for.simps head_free; simp)
qed

lemma book_negative_predicate_subst:
  assumes fresh: "x \<notin> named_fv F"
  shows "named_subst x (NVar y) (book_not G (NApp F (NVar x))) =
    book_not G (NApp F (NVar y))"
proof -
  have head_fixed: "named_subst x (NVar y) F = F"
    by (rule named_subst_fresh[OF fresh])
  show ?thesis by (simp add: book_not_variable_subst head_fixed)
qed

theorem book_theory_negative_predicate_rename:
  assumes rich: "sg_rich G"
    and negative: "book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar x)))"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and xtype: "G x = \<sigma>" and ytype: "G y = \<sigma>"
    and fresh: "x \<notin> named_fv F"
  shows "book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar y)))"
proof -
  have replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar y) (G x)"
    by (simp only: book_language_var_iff xtype ytype)
  have free_for: "named_free_for (NVar y) x (book_not G (NApp F (NVar x)))"
    by (rule book_negative_predicate_free_for[OF fresh])
  have substituted: "book_theory_derivable \<Sigma> G S
    (named_subst x (NVar y) (book_not G (NApp F (NVar x))))"
    by (rule book_theory_variable_substitution[OF rich negative replacement free_for])
  show ?thesis using substituted by (simp only: book_negative_predicate_subst[OF fresh])
qed

section \<open>Generalizing at the literal existential operator's binder\<close>

text \<open>
  Choose the exact y used by ∃σ = λX.¬(∀σ y.¬(X y)).
  Moving the negative instance to y and applying the derived
  generalization rule yields S ⊢ ∀σ y.¬(F y).
  Source: Table 4.1, p.93, and the witness-construction setting of
  Proposition 15.4, p.319.

  The resulting binder is literal book_all at that name. If y was
  already free in F, it is bound in the resulting formula as well;
  no α-equivalence with another displayed binder is inferred.
  No model, H, consistency premise, or new proof rule is introduced.
\<close>

theorem book_theory_negative_predicate_generalize:
  assumes rich: "sg_rich G"
    and negative: "book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar x)))"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and xtype: "G x = \<sigma>"
    and fresh: "x \<notin> named_fv F"
  shows "book_theory_derivable \<Sigma> G S
    (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp F (NVar (book_exists_argument_name G \<sigma>)))))"
proof -
  let ?y = "book_exists_argument_name G \<sigma>"
  have ytype: "G ?y = \<sigma>" by (rule book_exists_argument_name_type[OF rich])
  have moved: "book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar ?y)))"
    by (rule book_theory_negative_predicate_rename[OF rich negative predicate xtype ytype fresh])
  show ?thesis by (rule book_theory_generalize[OF rich moved])
qed

end
