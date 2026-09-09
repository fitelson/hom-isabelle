theory Bacon_Book_Minimal_Validity
  imports Bacon_Book_Minimal_Truth
begin

section \<open>Truth in a model and the book's two inference rules\<close>

text \<open>
  A formula is true in a model when every typed assignment satisfies it
  (Bacon, Definition 15.2, p.317). This convention applies also to open
  formulas. The definitions below are used with explicit formula-language
  guards; truth does not by itself assert that an arbitrary raw term is
  a formula in the chosen signature.

  Modus Ponens preserves such truth. For Gen, if A→B is true and
  x ∉ FV(A), then A→∀x.B is true: changing the value of x leaves
  A's denotation unchanged. Source: Definitions 5.1, p.98, and the
  soundness argument of Theorem 15.1, p.318. This is theory-level
  validity, not a local consequence relation that fixes values of free
  variables in undischarged assumptions.
\<close>

definition book_formula_valid ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> sgcontext \<Rightarrow>
    ((nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v) \<Rightarrow>
    ('v \<Rightarrow> bool) \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_formula_valid D G J V A \<longleftrightarrow> (\<forall>g. book_env_typed D G g \<longrightarrow> V (J g A))"

text \<open>
  Validity itself is independent of the logical-symbol alphabet. The
  polymorphic definition serves both the minimal language and extensions
  with primitive symbols. The model-specific lemmas below still explicitly
  concern full minimal models; their scope is not enlarged by this typing
  generalization of the common all-assignment truth predicate.
\<close>

lemma book_formula_validI:
  assumes truth: "\<And>g. book_env_typed D G g \<Longrightarrow> V (J g A)"
  shows "book_formula_valid D G J V A"
  unfolding book_formula_valid_def by (intro allI impI, rule truth, assumption)

lemma book_formula_validE:
  assumes valid: "book_formula_valid D G J V A" and typed: "book_env_typed D G g"
  shows "V (J g A)"
  using valid typed unfolding book_formula_valid_def by blast

context book_full_minimal_model
begin

lemma book_MP_valid:
  assumes al: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
    and antecedent: "book_formula_valid domain stock denote V A"
    and conditional: "book_formula_valid domain stock denote V (book_imp A B)"
  shows "book_formula_valid domain stock denote V B"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have a: "V (denote g A)" by (rule book_formula_validE[OF antecedent typed])
  have ab: "V (denote g (book_imp A B))" by (rule book_formula_validE[OF conditional typed])
  have material: "V (denote g (book_imp A B)) = (V (denote g A) \<longrightarrow> V (denote g B))"
    by (rule book_imp_truth[OF typed al bl])
  show "V (denote g B)" using a ab material by blast
qed

lemma book_Gen_valid:
  assumes al: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
    and fresh: "n \<notin> named_fv A"
    and conditional: "book_formula_valid domain stock denote V (book_imp A B)"
  shows "book_formula_valid domain stock denote V (book_imp A (book_all stock n B))"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have quantified: "book_in_language book_minimal_logical_type UNIV signature stock (book_all stock n B) Prop"
    by (rule book_all_language[OF bl])
  have implication: "V (denote g A) \<longrightarrow> V (denote g (book_all stock n B))"
  proof
    assume a: "V (denote g A)"
    have all: "\<forall>x \<in> domain (stock n). V (denote (g(n := x)) B)"
    proof (rule ballI)
      fix x
      assume xm: "x \<in> domain (stock n)"
      have updated: "book_env_typed domain stock (g(n := x))" by (rule book_env_update[OF typed xm])
      have same_a: "denote (g(n := x)) A = denote g A"
      proof (rule book_denote_locality[OF UNIV_I al updated typed])
        fix m
        assume free: "m \<in> named_fv A"
        have distinct: "m \<noteq> n" using free fresh by blast
        show "(g(n := x)) m = g m" by (simp add: distinct)
      qed
      have ab: "V (denote (g(n := x)) (book_imp A B))"
        by (rule book_formula_validE[OF conditional updated])
      have material: "V (denote (g(n := x)) (book_imp A B)) =
        (V (denote (g(n := x)) A) \<longrightarrow> V (denote (g(n := x)) B))"
        by (rule book_imp_truth[OF updated al bl])
      have updated_a: "V (denote (g(n := x)) A)" by (simp only: same_a; rule a)
      show "V (denote (g(n := x)) B)" using updated_a ab material by blast
    qed
    show "V (denote g (book_all stock n B))"
      using all book_all_truth[OF typed bl] by blast
  qed
  show "V (denote g (book_imp A (book_all stock n B)))"
    using implication book_imp_truth[OF typed al quantified] by blast
qed

lemma book_conversion_valid:
  assumes al: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
    and conversion: "named_raw_beta_eta book_minimal_logical_type stock Prop A B"
  shows "book_formula_valid domain stock denote V (book_imp A B)"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have same: "denote g A = denote g B"
    by (rule book_denote_conversion[OF UNIV_I UNIV_I al bl conversion typed])
  show "V (denote g (book_imp A B))"
    using book_imp_truth[OF typed al bl] same by simp
qed

end

end
