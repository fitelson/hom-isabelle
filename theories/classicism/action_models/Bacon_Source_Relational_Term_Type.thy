theory Bacon_Source_Relational_Term_Type
  imports Bacon_Source_Relational_Syntax
begin

section \<open>The type index of a well-typed R term is uniquely determined\<close>

text \<open>
  The source writes the interpretation of A without passing its type
  as an extra argument. For the canonical class interpretation we
  therefore select the unique ρ with A:ρ. Uniqueness is proved by
  the independent R typing judgment. On an ill-typed term this total
  HOL selector has no asserted source meaning. No model, consistency,
  theoremhood or type-existence premise is introduced.
\<close>

definition paper_R_term_type :: "sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> otype" where
  "paper_R_term_type G A = (THE \<rho>. paper_R_has_type G A \<rho>)"

lemma paper_R_term_type_eq:
  assumes typed: "paper_R_has_type G A \<rho>"
  shows "paper_R_term_type G A = \<rho>"
  unfolding paper_R_term_type_def
proof (rule the_equality[where P="paper_R_has_type G A" and a=\<rho>, OF typed])
  fix \<sigma>
  assume other: "paper_R_has_type G A \<sigma>"
  show "\<sigma> = \<rho>" by (rule paper_R_type_unique[OF other typed])
qed

corollary paper_R_term_type_language:
  assumes language: "paper_R_in_language \<Sigma> G A \<rho>"
  shows "paper_R_term_type G A = \<rho>"
proof -
  have typed: "paper_R_has_type G A \<rho>" using language unfolding paper_R_in_language_def by blast
  show ?thesis by (rule paper_R_term_type_eq[OF typed])
qed

end
