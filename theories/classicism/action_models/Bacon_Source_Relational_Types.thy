theory Bacon_Source_Relational_Types
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Syntax
begin

section \<open>The paper's default type system R\<close>

text \<open>
  R contains e and t, and contains σ→τ precisely when σ,τ∈R and τ≠e.
  A relational type is a member of R other than e. Bacon–Dorr §1.1,
  p.5, distinguishes this default system from the larger unrestricted F.
  In particular, every relational type has the form σ₁→⋯→σₙ→t,
  with each σᵢ∈R; the empty vector represents t.

  Representation: paper_R_type is a predicate on the existing F datatype
  otype. paper_type_vector is an independent right-associated fold of Arr.
  No C proof theory, term restriction, signature restriction, or model
  predicate is imported or identified with its R counterpart here.
  Status: type classification only. Full-F profile definitions remain
  meaningful, but comparisons relying on this relational decomposition
  require R guards; this leaf does not establish their full-F extension.
\<close>

fun paper_R_type :: "otype \<Rightarrow> bool" where
  "paper_R_type Ind = True"
| "paper_R_type Prop = True"
| "paper_R_type (Arr \<sigma> \<tau>) =
    (paper_R_type \<sigma> \<and> paper_R_type \<tau> \<and> \<tau> \<noteq> Ind)"

definition paper_R_relational :: "otype \<Rightarrow> bool" where
  "paper_R_relational \<tau> \<longleftrightarrow> paper_R_type \<tau> \<and> \<tau> \<noteq> Ind"

fun paper_type_vector :: "otype list \<Rightarrow> otype \<Rightarrow> otype" where
  "paper_type_vector [] \<tau> = \<tau>"
| "paper_type_vector (\<sigma> # \<sigma>s) \<tau> = Arr \<sigma> (paper_type_vector \<sigma>s \<tau>)"

lemma paper_type_vector_foldr:
  "paper_type_vector \<sigma>s \<tau> = foldr Arr \<sigma>s \<tau>"
  by (induction \<sigma>s) simp_all

lemma paper_type_vector_append:
  "paper_type_vector (\<sigma>s @ \<tau>s) \<rho> =
    paper_type_vector \<sigma>s (paper_type_vector \<tau>s \<rho>)"
  by (induction \<sigma>s) simp_all

lemma paper_type_vector_Prop_not_Ind [simp]:
  "paper_type_vector \<sigma>s Prop \<noteq> Ind"
  by (cases \<sigma>s) simp_all

lemma paper_R_arrow_iff:
  "paper_R_type (Arr \<sigma> \<tau>) \<longleftrightarrow>
    paper_R_type \<sigma> \<and> paper_R_relational \<tau>"
  by (simp add: paper_R_relational_def)

lemma paper_R_arrow_domain:
  assumes "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_R_type \<sigma>"
  using assms by simp

lemma paper_R_arrow_codomain:
  assumes "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_R_relational \<tau>"
  using assms by (simp add: paper_R_relational_def)

lemma paper_R_arrow_relational:
  assumes "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_R_relational (Arr \<sigma> \<tau>)"
  using assms by (simp add: paper_R_relational_def)

lemma paper_R_vector_to_Prop_iff:
  "paper_R_type (paper_type_vector \<sigma>s Prop) \<longleftrightarrow> list_all paper_R_type \<sigma>s"
  by (induction \<sigma>s) simp_all

lemma paper_R_relational_vector_iff:
  "paper_R_relational (paper_type_vector \<sigma>s Prop) \<longleftrightarrow> list_all paper_R_type \<sigma>s"
  by (simp add: paper_R_relational_def paper_R_vector_to_Prop_iff)

lemma paper_R_relational_decomposition:
  assumes relational: "paper_R_relational \<tau>"
  shows "\<exists>\<sigma>s. list_all paper_R_type \<sigma>s \<and> \<tau> = paper_type_vector \<sigma>s Prop"
  using relational
proof (induction \<tau>)
  case Ind
  then show ?case by (simp add: paper_R_relational_def)
next
  case Prop
  have "list_all paper_R_type [] \<and> Prop = paper_type_vector [] Prop" by simp
  then show ?case by (rule exI)
next
  case (Arr \<sigma> \<tau>)
  have domain: "paper_R_type \<sigma>" and codomain: "paper_R_relational \<tau>"
    using Arr.prems by (auto simp: paper_R_relational_def)
  obtain \<sigma>s where all_types: "list_all paper_R_type \<sigma>s"
    and tail: "\<tau> = paper_type_vector \<sigma>s Prop"
    using Arr.IH(2)[OF codomain] by blast
  have "list_all paper_R_type (\<sigma> # \<sigma>s) \<and>
      Arr \<sigma> \<tau> = paper_type_vector (\<sigma> # \<sigma>s) Prop"
    using domain all_types tail by simp
  then show ?case by (rule exI)
qed

theorem paper_R_relational_iff_vector:
  "paper_R_relational \<tau> \<longleftrightarrow>
    (\<exists>\<sigma>s. list_all paper_R_type \<sigma>s \<and> \<tau> = paper_type_vector \<sigma>s Prop)"
proof
  assume "paper_R_relational \<tau>"
  then show "\<exists>\<sigma>s. list_all paper_R_type \<sigma>s \<and> \<tau> = paper_type_vector \<sigma>s Prop"
    by (rule paper_R_relational_decomposition)
next
  assume "\<exists>\<sigma>s. list_all paper_R_type \<sigma>s \<and> \<tau> = paper_type_vector \<sigma>s Prop"
  then obtain \<sigma>s where all_types: "list_all paper_R_type \<sigma>s"
    and shape: "\<tau> = paper_type_vector \<sigma>s Prop" by blast
  show "paper_R_relational \<tau>"
    using all_types by (simp only: shape paper_R_relational_vector_iff)
qed

lemma paper_R_type_classification:
  "paper_R_type \<tau> \<longleftrightarrow> \<tau> = Ind \<or>
    (\<exists>\<sigma>s. list_all paper_R_type \<sigma>s \<and> \<tau> = paper_type_vector \<sigma>s Prop)"
  using paper_R_relational_iff_vector[of \<tau>]
  by (cases "\<tau> = Ind") (auto simp: paper_R_relational_def)

text \<open>
  The restrictions are recursive: e→e and (e→e)→t are F types but
  not R types. Merely ending in t does not suffice unless every argument
  type also belongs to R. These examples mark the precise scope boundary.
\<close>

lemma paper_R_excludes_individual_functions:
  "\<not> paper_R_type (Arr \<sigma> Ind)"
  "\<not> paper_R_type (Arr (Arr Ind Ind) Prop)"
  by simp_all

end
