theory Bacon_Book_Conjunction_Completeness
  imports Bacon_Book_Conjunction_Countermodel Bacon_Book_Conjunction_Theory_Soundness
begin

section \<open>Global consequence over every native conjunction model\<close>

text \<open>
  S⊨∧A ranges over EVERY independently specified native conjunction
  model on the displayed canonical carrier. It does not restrict the
  quantified models to encoded constructions. Truth of premises and
  conclusion is global: every typed assignment must satisfy them.
  Source role: the §5.2 primitive extension and the completeness theorem
  of Chapter 15, retaining their full-language, rich-stock setting.

  Soundness is separately carrier-polymorphic. The completeness carrier
  consists of minimal term classes over tagged Henkin names. Other logical
  primitives, arbitrary partial bases and general sublanguages require
  separate extensions; no operator-identity or Functionality axiom is added.
\<close>

definition book_conj_canonical_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> 'c book_conj_term \<Rightarrow> bool" where
  "book_conj_canonical_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>(D::otype \<Rightarrow> 'c book_conj_canonical_value set) app J V k.
      book_conjunction_model D app \<Sigma> G J V k \<longrightarrow>
      (\<forall>B\<in>S. book_formula_valid D G J V B) \<longrightarrow>
      book_formula_valid D G J V A)"

theorem book_conj_canonical_soundness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G" and derivation: "book_conj_theory_derivable \<Sigma> G S A"
  shows "book_conj_canonical_consequence \<Sigma> G S A"
proof (unfold book_conj_canonical_consequence_def, intro allI impI)
  fix D :: "otype \<Rightarrow> 'c book_conj_canonical_value set" and app J V k
  assume model: "book_conjunction_model D app \<Sigma> G J V k"
    and premise_truth: "\<forall>B\<in>S. book_formula_valid D G J V B"
  interpret Model: book_conjunction_model D app \<Sigma> G J V k by (rule model)
  show "book_formula_valid D G J V A"
    by (rule Model.book_conj_theory_soundness[OF rich derivation]; rule bspec[OF premise_truth]; assumption)
qed

theorem book_conj_canonical_completeness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G B"
    and al: "book_conj_formula \<Sigma> G A"
    and consequence: "book_conj_canonical_consequence \<Sigma> G S A"
  shows "book_conj_theory_derivable \<Sigma> G S A"
proof (rule ccontr)
  assume nonderivable: "\<not> book_conj_theory_derivable \<Sigma> G S A"
  obtain D :: "otype \<Rightarrow> 'c book_conj_canonical_value set" and app J V k where
    model: "book_conjunction_model D app \<Sigma> G J V k"
    and premise_truth: "\<forall>B\<in>S. book_formula_valid D G J V B"
    and failure: "\<not> book_formula_valid D G J V A"
    using book_conj_canonical_countermodel[OF rich language al nonderivable] by blast
  have truth: "book_formula_valid D G J V A"
    using consequence model premise_truth unfolding book_conj_canonical_consequence_def by blast
  show False by (rule notE[OF failure truth])
qed

theorem book_conj_canonical_strong_completeness:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G B"
    and al: "book_conj_formula \<Sigma> G A"
  shows "book_conj_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_conj_canonical_consequence \<Sigma> G S A"
proof
  assume derivation: "book_conj_theory_derivable \<Sigma> G S A"
  show "book_conj_canonical_consequence \<Sigma> G S A"
    by (rule book_conj_canonical_soundness[OF rich derivation])
next
  assume consequence: "book_conj_canonical_consequence \<Sigma> G S A"
  show "book_conj_theory_derivable \<Sigma> G S A"
    by (rule book_conj_canonical_completeness[OF rich language al consequence])
qed

end
