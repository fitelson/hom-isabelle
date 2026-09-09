theory Bacon_Source_Relational_Naming_Syntax
  imports Bacon_Source_Relational_Syntax
begin

section \<open>The signature naming every typed domain value\<close>

text \<open>
  The expanded signature admits Inl(c):σ for each old c∈Σσ and
  Inr(a):σ for each a∈Dσ. Source role: the language ℒ_M in
  p.51 n.73, with new names intended to denote the corresponding values.
  Here D is only a family of sets: no model or interpretation is assumed.

  The same value may belong to different Dσ. Accordingly the finite
  support below records pairs (σ,a), not bare values a. These are
  typed occurrences of atomic names, not an assumption of disjoint domains.
\<close>

definition paper_R_naming_signature ::
  "'c ssignature \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow> ('c + 'v) ssignature" where
  "paper_R_naming_signature \<Sigma> D \<sigma> = Inl ` \<Sigma> \<sigma> \<union> Inr ` D \<sigma>"

lemma paper_R_naming_signature_old [simp]:
  "Inl c \<in> paper_R_naming_signature \<Sigma> D \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
  by (auto simp: paper_R_naming_signature_def)

lemma paper_R_naming_signature_value [simp]:
  "Inr a \<in> paper_R_naming_signature \<Sigma> D \<sigma> \<longleftrightarrow> a \<in> D \<sigma>"
  by (auto simp: paper_R_naming_signature_def)

lemma paper_R_naming_signature_old_inclusion:
  "Inl ` \<Sigma> \<sigma> \<subseteq> paper_R_naming_signature \<Sigma> D \<sigma>"
  by auto

section \<open>Finite typed support of the new names\<close>

fun paper_R_naming_support :: "('c + 'v, 'l) named_term \<Rightarrow> (otype \<times> 'v) set" where
  "paper_R_naming_support (NVar n) = {}"
| "paper_R_naming_support (NConst c \<sigma>) = (case c of Inl b \<Rightarrow> {} | Inr a \<Rightarrow> {(\<sigma>,a)})"
| "paper_R_naming_support (NLogical l) = {}"
| "paper_R_naming_support (NApp F A) = paper_R_naming_support F \<union> paper_R_naming_support A"
| "paper_R_naming_support (NLam n A) = paper_R_naming_support A"

lemma paper_R_naming_support_finite:
  "finite (paper_R_naming_support A)"
  by (induction A) (auto split: sum.splits)

lemma paper_R_naming_support_old_embedding:
  "paper_R_naming_support (map_named_term Inl id A) = {}"
  by (induction A) simp_all

lemma paper_R_naming_old_signature:
  "named_in_signature (paper_R_naming_signature \<Sigma> D) (map_named_term Inl id A) \<longleftrightarrow>
    named_in_signature \<Sigma> A"
  by (induction A) simp_all

lemma paper_R_naming_support_values:
  assumes names: "named_in_signature (paper_R_naming_signature \<Sigma> D) A"
  shows "\<forall>k\<in>paper_R_naming_support A. snd k \<in> D (fst k)"
  using names by (induction A) (auto split: sum.splits)

lemma paper_R_naming_support_R_types:
  assumes typed: "paper_R_has_type G A \<tau>"
  shows "\<forall>k\<in>paper_R_naming_support A. paper_R_type (fst k)"
  using typed by (induction rule: paper_R_has_type.induct) (auto split: sum.splits)

lemma paper_R_naming_support_language:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
    and member: "(\<sigma>,a) \<in> paper_R_naming_support A"
  shows "paper_R_type \<sigma> \<and> a \<in> D \<sigma>"
proof -
  have typed: "paper_R_has_type G A \<tau>"
    and names: "named_in_signature (paper_R_naming_signature \<Sigma> D) A"
    using language unfolding paper_R_in_language_def by blast+
  show ?thesis using paper_R_naming_support_R_types[OF typed]
    paper_R_naming_support_values[OF names] member by auto
qed

end
