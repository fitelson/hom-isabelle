theory Bacon_Book_Printed_Completeness
  imports Bacon_Book_Printed_Theory_Correspondence Bacon_Book_Canonical_Completeness
begin

section \<open>Consistency and soundness for the printed-guard calculus\<close>

text \<open>
  The proved equivalence transports model existence and completeness to
  the independently defined Chapter 5 calculus using the printed free-for
  proviso. This is a theorem transfer, not a redefinition of either proof
  relation. The original premise set and conclusion remain unchanged.
\<close>

definition book_printed_theory_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_printed_theory_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> book_printed_theory_derivable \<Sigma> G S (book_bottom G)"

theorem book_consistency_iff_printed:
  assumes rich: "sg_rich G"
  shows "book_theory_consistent \<Sigma> G S \<longleftrightarrow> book_printed_theory_consistent \<Sigma> G S"
  by (simp only: book_theory_consistent_def book_printed_theory_consistent_def book_theory_iff_printed[OF rich])

context book_full_minimal_model
begin

theorem book_printed_theory_soundness:
  assumes rich: "sg_rich stock"
    and derivation: "book_printed_theory_derivable signature stock S A"
    and premise_truth: "\<And>B. B \<in> S \<Longrightarrow> book_formula_valid domain stock denote V B"
  shows "book_formula_valid domain stock denote V A"
  by (rule book_theory_soundness[OF rich book_printed_theory_to_theory[OF derivation] premise_truth])

end

section \<open>Original-signature existence and global strong completeness\<close>

text \<open>
  Every printed-consistent typed S has an original-signature full minimal
  model. Printed derivability from S is equivalent to global consequence
  over every independent full minimal model on the explicit canonical
  carrier. S and A may be open, and their signatures may be uncountable.
  Source: Theorem 15.3 and Corollary 15.2, pp.320–321, retaining the
  documented closed-completion/¬UC(A) repair of the proof route.

  The full F grammar, minimal logical basis, rich stock and witnessed
  closed-value scope remain. No general-𝒥, partial-basis or Classicism
  semantic completeness result follows merely from this transfer.
\<close>

theorem book_printed_canonical_model_existence:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_printed_theory_formula \<Sigma> G A"
    and consistent: "book_printed_theory_consistent \<Sigma> G S"
  shows "\<exists>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
    book_full_minimal_model D app \<Sigma> G J V k \<and>
    (\<forall>A\<in>S. book_formula_valid D G J V A)"
  by (rule book_canonical_model_existence[OF rich language
    iffD2[OF book_consistency_iff_printed[OF rich] consistent]])

theorem book_printed_canonical_strong_completeness:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_printed_theory_formula \<Sigma> G B"
    and al: "book_printed_theory_formula \<Sigma> G A"
  shows "book_printed_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_canonical_consequence \<Sigma> G S A"
  using book_canonical_strong_completeness[OF rich language al]
  by (simp only: book_theory_iff_printed[OF rich])

theorem book_printed_canonical_countermodel:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_printed_theory_formula \<Sigma> G B"
    and al: "book_printed_theory_formula \<Sigma> G A"
    and nonderivable: "\<not> book_printed_theory_derivable \<Sigma> G S A"
  shows "\<exists>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
    book_full_minimal_model D app \<Sigma> G J V k \<and>
    (\<forall>B\<in>S. book_formula_valid D G J V B) \<and>
    \<not> book_formula_valid D G J V A \<and>
    (\<exists>g. book_env_typed D G g \<and> \<not> V (J g A))"
proof -
  have old_nonderivable: "\<not> book_theory_derivable \<Sigma> G S A"
  proof
    assume derivation: "book_theory_derivable \<Sigma> G S A"
    have printed: "book_printed_theory_derivable \<Sigma> G S A"
      by (rule book_theory_to_printed[OF rich derivation])
    show False by (rule notE[OF nonderivable printed])
  qed
  show ?thesis by (rule book_canonical_countermodel_with_assignment[OF rich language al old_nonderivable])
qed

end
