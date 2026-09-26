theory Bacon_Book_Lambda_I_Audit
  imports Bacon_Book_Lambda_I_Canonical_Completeness
begin

ML_file "../../core_audit/Bacon_Core_Audit_Check.ML"

section \<open>Conditional truth lemma: a typed assignment for ⊥ → ⊥ in any λI model\<close>

text \<open>
  In any λI model, the assignment-existence clause supplies a typed total
  assignment and the implication clause makes ⊥ → ⊥ true at it. This is a
  conditional lemma inside the model class; it does not exhibit a model.
  The actual model-and-assignment witness for {⊥ → ⊥}, together with its
  λI consistency, is the separate regression session
  Bacon_Book_Lambda_I_Regressions, which uses the auxiliary-bridge full
  minimal model existence theorem and the restriction of full minimal
  models to λI models.
\<close>

context book_lambda_I_model
begin

theorem book_lambda_I_bottom_implication_satisfied:
  assumes rich: "sg_rich stock"
  shows "\<exists>g. book_env_typed domain stock g \<and>
    V (denote g (book_imp (book_bottom stock) (book_bottom stock)))"
proof -
  obtain g where typed: "book_env_typed domain stock g" using assignment_exists by blast
  have bottom: "book_lambda_I_formula signature stock (book_bottom stock)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have truth: "V (denote g (book_imp (book_bottom stock) (book_bottom stock))) =
    (V (denote g (book_bottom stock)) \<longrightarrow> V (denote g (book_bottom stock)))"
    by (rule imp_truth[OF typed bottom bottom])
  show ?thesis by (rule exI[where x=g], rule conjI[OF typed]; simp only: truth; blast)
qed

end

ML \<open>
local
  val targets =
   [("the λI language satisfies every clause of Definition 9.1", "book_lambda_I_general_lambda_language"),
    ("λI is closed under substitution of λI terms for variables", "book_lambda_I_subst"),
    ("λI is closed under α-inclusive directed βη-reduction", "book_lambda_I_source_reduces"),
    ("λI is closed under relettering of free variables", "book_lambda_I_reletter"),
    ("a vacuous abstraction is not a λI term", "book_lambda_I_vacuous_abstraction"),
    ("every λI derivation has a λI formula conclusion", "book_lambda_I_derivable_formula"),
    ("λI derivability is monotone in the premises", "book_lambda_I_derivable_mono"),
    ("every λI derivation is a full-H derivation (one-way embedding)", "book_lambda_I_derivable_embeds"),
    ("full consistency gives λI consistency", "book_lambda_I_consistent_of_theory"),
    ("internal λI conversion is ambient in-language βη-conversion", "book_lambda_I_conv_in_language"),
    ("internal λI conversion preserves free variables", "book_lambda_I_conv_fv"),
    ("internal λI conversion lifts through application", "book_lambda_I_conv_App"),
    ("internal λI conversion lifts through relevant abstraction", "book_lambda_I_conv_Lam"),
    ("renaming a binder is an internal λI conversion", "book_lambda_I_fresh_binder_conv"),
    ("α-conversion between λI terms is internal", "book_lambda_I_alpha_conv"),
    ("internal conversion at Prop derives both implications", "book_lambda_I_conv_derivable_pair"),
    ("internal conversion transports λI derivability", "book_lambda_I_conv_derivable_iff"),
    ("α-variants are inter-derivable in the λI calculus", "book_lambda_I_alpha_derivable_iff"),
    ("the constant-form Gen of Definition 9.8 is derivable from binder Gen", "book_lambda_I_Gen_constant"),
    ("the constant-form calculus embeds into the binder calculus", "book_lambda_I_derivable_c_to_binder"),
    ("the binder calculus embeds into the constant-form calculus", "book_lambda_I_derivable_binder_to_c"),
    ("the two Gen presentations derive the same formulas", "book_lambda_I_presentations_iff"),
    ("applications of a predicate to two α-variants of the identity are inter-derivable", "book_lambda_I_alpha_regression"),
    ("nothing λI reaches the vacuous abstraction by an immediate β step", "book_lambda_I_omission_regression_beta"),
    ("nothing λI reaches the vacuous abstraction by an immediate η step", "book_lambda_I_omission_regression_eta"),
    ("λI models satisfy the implication truth clause", "book_lambda_I_model.imp_truth"),
    ("λI models satisfy the relevant abstraction application law", "book_lambda_I_model.lambda_application"),
    ("λI models satisfy the universal truth clause for relevant binders", "book_lambda_I_model.all_truth"),
    ("bottom is false in every λI model", "book_lambda_I_model.bottom_false"),
    ("the literal negation operator negates in every λI model", "book_lambda_I_model.not_truth"),
    ("the λI calculus is sound for every λI model", "book_lambda_I_model.book_lambda_I_soundness"),
    ("satisfiable λI premise sets are λI-consistent", "book_lambda_I_model.book_lambda_I_satisfiable_consistent"),
    ("every full minimal model restricts to a λI model", "book_full_minimal_model_lambda_I"),
    ("nonvacuous generalization is derived in the λI calculus", "book_lambda_I_generalize"),
    ("variable substitution with a λI replacement, split on occurrence", "book_lambda_I_variable_substitution"),
    ("λI derivations retract foreign constants to fresh variables", "book_lambda_I_retraction"),
    ("foreign constants are eliminated from λI derivations", "book_lambda_I_foreign_constants_eliminate"),
    ("λI signature extension is conservative", "book_lambda_I_signature_conservativity"),
    ("a fresh-constant negative instance generalizes at a relevant binder", "book_lambda_I_fresh_constant_generalization"),
    ("adjoining one conditional witness for a λI predicate preserves λI consistency", "book_lambda_I_consistent_conditional_witness"),
    ("an arbitrary family of fresh conditional witnesses preserves λI consistency", "book_lambda_I_consistent_witness_family"),
    ("each λI Henkin stage is consistent", "book_lambda_I_henkin_stage_consistent"),
    ("the union of all λI Henkin stages is consistent", "book_lambda_I_henkin_full_premises_consistent"),
    ("every closed λI predicate of the full signature has a declared witness constant", "book_lambda_I_henkin_full_premises_witness"),
    ("the closed λI Henkin extension exists and is witness complete", "book_lambda_I_closed_henkin_extension_exists"),
    ("conditional witnesses and closed maximality give λI witness completeness", "book_lambda_I_closed_constant_witness_complete_from_conditionals"),
    ("membership in the maximal set respects internal conversion", "book_lambda_I_closed_maximal_conv_iff"),
    ("membership in the maximal set interprets implication materially", "book_lambda_I_closed_maximal_implication_iff"),
    ("membership in the maximal set interprets the universal quantifier over closed λI terms", "book_lambda_I_closed_maximal_forall_iff"),
    ("every full-signature domain of closed λI classes is inhabited", "book_lambda_I_henkin_conversion_domain_nonempty"),
    ("the full λI witness signature has a typed total assignment", "book_lambda_I_henkin_conversion_assignment_exists"),
    ("closed substitution of λI representatives preserves internal conversion", "book_lambda_I_environment_subst_conv"),
    ("the constructed denotation satisfies the internal environment clause", "book_lambda_I_conversion_environment"),
    ("the constructed valuation has a false propositional class", "book_lambda_I_conversion_false_exists"),
    ("the closed λI conversion classes form a λI model", "book_lambda_I_henkin_conversion_model"),
    ("truth of a closed λI formula in the term model is membership", "book_lambda_I_henkin_conversion_closed_valid_iff"),
    ("universal closure preserves all-assignment truth in λI models", "book_lambda_I_model.book_formula_valid_universal_closure_iff"),
    ("the BookOriginal-renamed premises hold in the expanded term model", "book_lambda_I_henkin_conversion_original_valid"),
    ("the unrenamed original premises hold after the original-signature pullback", "book_lambda_I_henkin_original_model_exists"),
    ("constant renaming preserves internal conversion", "book_lambda_I_constant_rename_conv"),
    ("a λI model pulls back along a constant renaming", "book_lambda_I_model.book_lambda_I_constant_pullback_model"),
    ("λI original-signature model existence (Theorem 15.3, λI instance)", "book_lambda_I_canonical_model_existence"),
    ("the least λI theory over S is the set of λI consequences of S", "book_lambda_I_derivable_iff_all_theories"),
    ("injective constant renaming reflects λI consistency", "book_lambda_I_consistent_constant_rename_iff"),
    ("a finite family of fresh conditional witnesses preserves λI consistency", "book_lambda_I_consistent_finite_witness_family"),
    ("the stage-one inhabitation predicate is a closed λI predicate of every type", "book_lambda_I_inhabitation_predicate_facts"),
    ("the full λI witness signature has a closed λI term of every type", "book_lambda_I_henkin_full_closed_term_exists"),
    ("a nonderivable λI formula has a countermodel with a falsifying assignment", "book_lambda_I_canonical_countermodel_with_assignment"),
    ("λI soundness over the canonical carrier", "book_lambda_I_canonical_soundness"),
    ("λI completeness over the canonical carrier", "book_lambda_I_canonical_completeness"),
    ("λI global strong completeness (Corollary 15.2, λI instance)", "book_lambda_I_canonical_strong_completeness"),
    ("λI theoremhood is validity over the canonical carrier", "book_lambda_I_canonical_theoremhood"),
    ("in any λI model a typed assignment satisfies ⊥ → ⊥ (conditional truth lemma)", "book_lambda_I_model.book_lambda_I_bottom_implication_satisfied")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-lambda-I"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL\n"
    ^ "SCOPE: Bacon's relevant (λI) language of Definition 9.2 as an instance of Definition 9.1; the independently defined λI theory calculus (Definition 9.8 restricted, binder Gen with occurrence guard, exact-capture β) and its constant-form presentation; internal βη/α conversion with derivability transport; λI models with the internal conversion clause (Definition 14.13 read through Proposition 9.1), soundness, retraction and signature conservativity, λI Henkin witness stages, the term model on internal conversion classes of closed λI terms, original-signature model existence and global strong completeness for arbitrary well-formed λI premise sets over the internal-clause model class on the canonical carrier; minimal logical basis, rich variable stock for the main endpoints, and an actual typed assignment required of every model; one-way embedding into full H. Open and distinct: identification of the λI calculus with HJ (the least relevant-language logic of Definitions 9.9–9.10, whose substitution closure is not proved), conservativity of full H over the λI calculus (the restriction of H to λI formulas), the λI printed/exact β correspondence (the calculus uses exact-capture β only), and internalization of raw βη-conversion between λI endpoints, hence no completeness claim for the raw-invariant model subclass; the actual {⊥ → ⊥} model witness is the separate regression session\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-lambda-I-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
