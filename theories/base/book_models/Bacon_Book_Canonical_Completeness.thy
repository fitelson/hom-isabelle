theory Bacon_Book_Canonical_Completeness
  imports Bacon_Book_Canonical_Countermodel Bacon_Book_Theory_Soundness Bacon_Book_Logic
begin

section \<open>Semantic consequence over an independently specified model class\<close>

text \<open>
  S⊨A means that EVERY full minimal model on the displayed canonical
  carrier which makes every member of S globally true also makes A
  globally true. The predicate below does not restrict the quantified
  models to those returned by the canonical construction.

  Source: Definition 15.2, p.317, and Corollary 15.2, p.321. Global
  truth quantifies all typed assignments. Consequently S and A may be
  open: the countermodel has an assignment falsifying A, not necessarily
  global truth of ¬A. The consistent refutation extension uses ¬UC(A).

  The carrier is explicit because HOL quantifies over values of a fixed
  type. Soundness is separately carrier-polymorphic. The completeness
  theorem retains full F, the minimal primitive basis, rich G and
  witnessed closed values; it does not claim arbitrary-𝒥 or richer-basis
  completeness, or any Classicism semantic theorem.
\<close>

definition book_canonical_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_canonical_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
      book_full_minimal_model D app \<Sigma> G J V k \<longrightarrow>
      (\<forall>B\<in>S. book_formula_valid D G J V B) \<longrightarrow>
      book_formula_valid D G J V A)"

theorem book_canonical_soundness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
  shows "book_canonical_consequence \<Sigma> G S A"
proof (unfold book_canonical_consequence_def, intro allI impI)
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set"
    and app J V k
  assume model: "book_full_minimal_model D app \<Sigma> G J V k"
    and premise_truth: "\<forall>B\<in>S. book_formula_valid D G J V B"
  interpret Model: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
  show "book_formula_valid D G J V A"
    by (rule Model.book_theory_soundness[OF rich derivation]; rule bspec[OF premise_truth]; assumption)
qed

theorem book_canonical_completeness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and consequence: "book_canonical_consequence \<Sigma> G S A"
  shows "book_theory_derivable \<Sigma> G S A"
proof (rule ccontr)
  assume nonderivable: "\<not> book_theory_derivable \<Sigma> G S A"
  obtain D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set"
    and app J V k where model: "book_full_minimal_model D app \<Sigma> G J V k"
    and premise_truth: "\<forall>B\<in>S. book_formula_valid D G J V B"
    and failure: "\<not> book_formula_valid D G J V A"
    using book_canonical_countermodel[OF rich language al nonderivable] by blast
  have valid: "book_formula_valid D G J V A"
    using consequence model premise_truth unfolding book_canonical_consequence_def by blast
  show False by (rule notE[OF failure valid])
qed

theorem book_canonical_strong_completeness:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_canonical_consequence \<Sigma> G S A"
proof
  assume derivation: "book_theory_derivable \<Sigma> G S A"
  show "book_canonical_consequence \<Sigma> G S A"
    by (rule book_canonical_soundness[OF rich derivation])
next
  assume consequence: "book_canonical_consequence \<Sigma> G S A"
  show "book_theory_derivable \<Sigma> G S A"
    by (rule book_canonical_completeness[OF rich language al consequence])
qed

corollary book_H_canonical_completeness:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_H \<Sigma> G A \<longleftrightarrow> book_canonical_consequence \<Sigma> G {} A"
proof -
  have equivalence: "book_theory_derivable \<Sigma> G {} A \<longleftrightarrow>
    book_canonical_consequence \<Sigma> G {} A"
    by (rule book_canonical_strong_completeness[OF rich _ al]; simp)
  show ?thesis by (simp only: book_H_iff_theory[OF rich] equivalence)
qed

end
