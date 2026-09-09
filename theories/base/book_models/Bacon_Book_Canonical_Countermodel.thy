theory Bacon_Book_Canonical_Countermodel
  imports Bacon_Book_Canonical_Model_Existence Bacon_Book_Universal_Closure_Truth
begin

section \<open>A negated universal closure excludes validity of the original formula\<close>

text \<open>
  If M ⊨ ¬UC(A), then M ⊭ A. Were A true under every typed
  assignment, UC(A) would be too. An ACTUAL typed assignment would
  then satisfy both UC(A) and its literal negation, contradicting the
  proved negation truth clause. Thus the argument is not based on an
  empty assignment space.
\<close>

context book_full_minimal_model
begin

lemma book_not_universal_closure_not_valid:
  assumes rich: "sg_rich stock"
    and language: "book_theory_formula signature stock A"
    and negative: "book_formula_valid domain stock denote V
      (book_not stock (book_universal_closure stock A))"
  shows "\<not> book_formula_valid domain stock denote V A"
proof
  assume valid: "book_formula_valid domain stock denote V A"
  let ?U = "book_universal_closure stock A"
  have ul: "book_theory_formula signature stock ?U"
    by (rule book_universal_closure_language[OF language])
  have universal_valid: "book_formula_valid domain stock denote V ?U"
    by (rule iffD2[OF book_formula_valid_universal_closure_iff[OF language] valid])
  obtain g where typed: "book_env_typed domain stock g"
    using book_minimal_assignment_exists by blast
  have positive_value: "V (denote g ?U)" by (rule book_formula_validE[OF universal_valid typed])
  have negative_value: "V (denote g (book_not stock ?U))"
    by (rule book_formula_validE[OF negative typed])
  have negation: "V (denote g (book_not stock ?U)) = (\<not> V (denote g ?U))"
    by (rule book_not_truth[OF rich typed ul])
  show False using positive_value negative_value negation by blast
qed

end

section \<open>An original-signature countermodel for a nonderivable formula\<close>

text \<open>
  If S ⊬ A, construct a model of S∪{¬UC(A)}. It globally satisfies
  S but fails A at some typed assignment. This applies to arbitrary
  typed S and A, including open formulas and infinite S.
  Source role: the repaired completeness argument of Corollary 15.2,
  p.321. For open A, the added premise is ¬UC(A), NOT ¬A.

  The displayed canonical carrier retains classes of expanded-name
  closed terms, while the model interprets the ORIGINAL signature Σ.
  No separate consistency premise on S is required. No conclusion of
  all-assignment truth of ¬A is asserted for an open A.
\<close>

theorem book_canonical_countermodel_with_assignment:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and nonderivable: "\<not> book_theory_derivable \<Sigma> G S A"
  shows "\<exists>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
    book_full_minimal_model D app \<Sigma> G J V k \<and>
    (\<forall>B\<in>S. book_formula_valid D G J V B) \<and>
    \<not> book_formula_valid D G J V A \<and>
    (\<exists>g. book_env_typed D G g \<and> \<not> V (J g A))"
proof -
  let ?N = "book_not G (book_universal_closure G A)"
  let ?T = "insert ?N S"
  have nl: "book_theory_formula \<Sigma> G ?N"
    by (rule book_not_language[OF rich book_universal_closure_language[OF al]])
  have enlarged_language: "book_theory_formula \<Sigma> G B" if "B \<in> ?T" for B
    using that nl language by blast
  have enlarged_consistent: "book_theory_consistent \<Sigma> G ?T"
    by (rule book_theory_consistent_insert_not_universal_closure[OF rich al nonderivable])
  obtain D app J V k where model:
      "book_full_minimal_model (D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app \<Sigma> G J V k"
    and all_valid: "\<forall>B\<in>?T. book_formula_valid D G J V B"
    using book_canonical_model_existence[OF rich enlarged_language enlarged_consistent] by blast
  interpret Model: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
  have premises_valid: "\<forall>B\<in>S. book_formula_valid D G J V B"
  proof (rule ballI)
    fix B
    assume member: "B \<in> S"
    show "book_formula_valid D G J V B" by (rule bspec[OF all_valid insertI2[OF member]])
  qed
  have negative_valid: "book_formula_valid D G J V ?N"
    by (rule bspec[OF all_valid insertI1])
  have invalid: "\<not> book_formula_valid D G J V A"
    by (rule Model.book_not_universal_closure_not_valid[OF rich al negative_valid])
  have counterassignment: "\<exists>g. book_env_typed D G g \<and> \<not> V (J g A)"
    using invalid unfolding book_formula_valid_def by blast
  show ?thesis by (rule exI[where x=D], rule exI[where x=app], rule exI[where x=J],
    rule exI[where x=V], rule exI[where x=k],
    rule conjI[OF model conjI[OF premises_valid conjI[OF invalid counterassignment]]])
qed

corollary book_canonical_countermodel:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and nonderivable: "\<not> book_theory_derivable \<Sigma> G S A"
  shows "\<exists>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
    book_full_minimal_model D app \<Sigma> G J V k \<and>
    (\<forall>B\<in>S. book_formula_valid D G J V B) \<and>
    \<not> book_formula_valid D G J V A"
  using book_canonical_countermodel_with_assignment[OF rich language al nonderivable] by blast

end
