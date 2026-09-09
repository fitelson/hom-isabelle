theory Bacon_Book_Variable_Relettering_Syntax
  imports Bacon_Book_Simultaneous_Substitution_Language
begin

section \<open>Finite simultaneous replacement of variable names\<close>

text \<open>
  A[y₁/x₁,…,yₙ/xₙ] is represented by the simultaneous table
  [(x₁:G(x₁),y₁),…,(xₙ:G(xₙ),yₙ)]. Payloads are literal variables;
  they are not substituted recursively into one another.
  Source role: the final relettering clause of Definition 9.1, p.190.

  This leaf establishes TYPING and ambient-language preservation only.
  Matching types G(xᵢ)=G(yᵢ) suffice for those properties. It assumes
  neither that the target variables are admitted in a chosen sublanguage
  nor that they avoid every name in A. Source free-for, distinctness, and
  FV conditions remain separate guards. Duplicated source keys use the
  existing first-match table convention.
\<close>

definition book_variable_relettering_table ::
  "sgcontext \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> ('c,'l) book_subst_table" where
  "book_variable_relettering_table G xs ys =
    zip (map (\<lambda>x. BSVar x (G x)) xs) (map NVar ys)"

definition book_variable_reletter ::
  "sgcontext \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "book_variable_reletter G xs ys A =
    book_simult_subst G (book_variable_relettering_table G xs ys) A"

definition book_variable_relettering_free_for ::
  "sgcontext \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_variable_relettering_free_for G xs ys A \<longleftrightarrow>
    book_simult_free_for G (book_variable_relettering_table G xs ys) A"

lemma book_variable_relettering_lookup:
  assumes found: "map_of (book_variable_relettering_table G xs ys) k = Some B"
  shows "\<exists>x y. (x,y) \<in> set (zip xs ys) \<and> k = BSVar x (G x) \<and> B = NVar y"
proof -
  have member: "(k,B) \<in> set (book_variable_relettering_table G xs ys)"
    by (rule map_of_SomeD[OF found])
  show ?thesis using member
    by (auto simp: book_variable_relettering_table_def zip_map_map)
qed

theorem book_variable_relettering_table_language:
  fixes L :: "'l \<Rightarrow> otype" and \<Sigma> :: "'c ssignature"
  assumes aligned: "list_all2 (\<lambda>x y. G x = G y) xs ys"
  shows "book_subst_table_language L \<Lambda> \<Sigma> G (book_variable_relettering_table G xs ys)"
proof (unfold book_subst_table_language_def, intro allI impI)
  fix k :: "'c book_subst_key" and B :: "('c,'l) named_term"
  assume found: "map_of (book_variable_relettering_table G xs ys) k = Some B"
  obtain x y where member: "(x,y) \<in> set (zip xs ys)"
    and key_shape: "k = BSVar x (G x)" and payload_shape: "B = NVar y"
    using book_variable_relettering_lookup[OF found] by blast
  have matching: "G x = G y" using aligned member by (auto simp: list_all2_iff)
  show "book_in_language L \<Lambda> \<Sigma> G B (book_subst_key_type k)"
    by (simp only: payload_shape key_shape book_subst_key_type.simps book_language_var_iff;
      rule matching)
qed

theorem book_variable_reletter_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and aligned: "list_all2 (\<lambda>x y. G x = G y) xs ys"
  shows "book_in_language L \<Lambda> \<Sigma> G (book_variable_reletter G xs ys A) \<tau>"
  unfolding book_variable_reletter_def
  by (rule book_simult_subst_language[OF language book_variable_relettering_table_language[OF aligned]])

corollary book_variable_reletter_type:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and aligned: "list_all2 (\<lambda>x y. G x = G y) xs ys"
  shows "has_ntype L G (book_variable_reletter G xs ys A) \<tau>"
  by (rule book_language_type[OF book_variable_reletter_language[OF language aligned]])

lemma book_variable_reletter_empty:
  "book_variable_reletter G [] [] A = A"
  by (simp add: book_variable_reletter_def book_variable_relettering_table_def book_simult_subst_empty)

text \<open>
  book_variable_relettering_free_for is only a wrapper for the existing
  simultaneous capture check on this exact generated table. No equivalence
  with a separately formulated printed free-for condition is asserted here.
  The language theorem remains valid for raw capturing replacement; it
  therefore must not be used by itself to establish legal relettering
  inside a general λ-language.
\<close>

end
