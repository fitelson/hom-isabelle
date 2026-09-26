theory Bacon_Book_Lambda_I_Canonical_Completeness
  imports Bacon_Book_Lambda_I_Canonical_Countermodel
begin

section \<open>Semantic consequence over the independently specified λI model class\<close>

text \<open>
  S⊨A means that EVERY λI model on the displayed canonical carrier
  which makes every member of S globally true also makes A globally
  true. The predicate does not restrict the quantified models to those
  returned by the canonical construction. Global truth quantifies all
  typed assignments; S and A may be open.

  Soundness is the λI soundness theorem of the model class; completeness
  is the countermodel construction. Both are stated for the
  independently defined λI theory calculus; identification with the
  restriction of H to λI formulas and completeness for the raw-invariant
  subclass are recorded as open.
\<close>

definition book_lambda_I_canonical_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_lambda_I_canonical_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
      book_lambda_I_model D app \<Sigma> G J V k \<longrightarrow>
      (\<forall>B\<in>S. book_formula_valid D G J V B) \<longrightarrow>
      book_formula_valid D G J V A)"

theorem book_lambda_I_canonical_soundness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G" and derivation: "book_lambda_I_derivable \<Sigma> G S A"
  shows "book_lambda_I_canonical_consequence \<Sigma> G S A"
proof (unfold book_lambda_I_canonical_consequence_def, intro allI impI)
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set"
    and app J V k
  assume model: "book_lambda_I_model D app \<Sigma> G J V k"
    and premise_truth: "\<forall>B\<in>S. book_formula_valid D G J V B"
  interpret Model: book_lambda_I_model D app \<Sigma> G J V k by (rule model)
  show "book_formula_valid D G J V A"
    by (rule Model.book_lambda_I_soundness[OF rich derivation]; rule bspec[OF premise_truth]; assumption)
qed

theorem book_lambda_I_canonical_completeness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G B"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and consequence: "book_lambda_I_canonical_consequence \<Sigma> G S A"
  shows "book_lambda_I_derivable \<Sigma> G S A"
proof (rule ccontr)
  assume nonderivable: "\<not> book_lambda_I_derivable \<Sigma> G S A"
  obtain D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set"
    and app J V k where model: "book_lambda_I_model D app \<Sigma> G J V k"
    and premise_truth: "\<forall>B\<in>S. book_formula_valid D G J V B"
    and failure: "\<not> book_formula_valid D G J V A"
    using book_lambda_I_canonical_countermodel[OF rich language al nonderivable] by blast
  have valid: "book_formula_valid D G J V A"
    using consequence model premise_truth unfolding book_lambda_I_canonical_consequence_def by blast
  show False by (rule notE[OF failure valid])
qed

theorem book_lambda_I_canonical_strong_completeness:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G B"
    and al: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G S A \<longleftrightarrow> book_lambda_I_canonical_consequence \<Sigma> G S A"
proof
  assume derivation: "book_lambda_I_derivable \<Sigma> G S A"
  show "book_lambda_I_canonical_consequence \<Sigma> G S A"
    by (rule book_lambda_I_canonical_soundness[OF rich derivation])
next
  assume consequence: "book_lambda_I_canonical_consequence \<Sigma> G S A"
  show "book_lambda_I_derivable \<Sigma> G S A"
    by (rule book_lambda_I_canonical_completeness[OF rich language al consequence])
qed

corollary book_lambda_I_canonical_theoremhood:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G {} A \<longleftrightarrow> book_lambda_I_canonical_consequence \<Sigma> G {} A"
  by (rule book_lambda_I_canonical_strong_completeness[OF rich _ al]; simp)

end
