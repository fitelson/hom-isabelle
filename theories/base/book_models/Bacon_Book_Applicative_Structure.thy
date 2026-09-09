theory Bacon_Book_Applicative_Structure
  imports Bacon_Book_Total_Assignments
begin

section \<open>The book's raw typed applicative structure\<close>

text \<open>
  A = ⟨D,App⟩ has sets Dσ and typed operations
  Appστ:Dσ→τ × Dσ → Dτ (Bacon, Definition 14.1, p.290).
  These raw structures are not required here to have nonempty domains,
  to be functional, or to identify operations with mathematical functions.
  Valuation and language interpretation are additional structure.
\<close>

locale book_applicative_structure =
  fixes domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes app_type: "f \<in> domain (Arr \<sigma> \<tau>) \<Longrightarrow> a \<in> domain \<sigma> \<Longrightarrow>
    app \<sigma> \<tau> f a \<in> domain \<tau>"

lemma book_empty_applicative_structure:
  "book_applicative_structure (\<lambda>\<sigma>. {}) app"
  by unfold_locales simp

lemma book_empty_domains_have_no_assignment:
  "\<not> book_env_typed (\<lambda>\<sigma>. {}) G g"
proof
  assume typed: "book_env_typed (\<lambda>\<sigma>. {}) G g"
  have "g 0 \<in> {}" by (rule book_env_at[where n=0, OF typed])
  then show False by simp
qed

end
