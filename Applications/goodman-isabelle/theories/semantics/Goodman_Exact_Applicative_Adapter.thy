theory Goodman_Exact_Applicative_Adapter
  imports
    "Goodman_Exact_Legacy_04.Bacon_PP_ZF_Exact_Frame"
    "Bacon_Book_Environment_Development.Bacon_Book_Applicative_Structure"
begin

section \<open>Bacon's exact carriers as the book's applicative structure\<close>

text \<open>
  This adapter changes only the interface: the HOL set Dσ consists of the
  members of Bacon's already constructed HOL–ZF carrier pp_b_domain σ,
  and Appστ(f,a) is the same set-theoretic function application f ´ a.
  No arrow carrier is enlarged, restricted, or replaced by a PER domain.

  The first target is Definition 14.1's typed applicative structure,
  together with inhabited domains and an explicit total assignment.
  These facts are prerequisites for an interpretation of the named
  language; they do not yet assert the environment condition, logical
  valuation, global soundness, or equality of closed-logical stocks.
\<close>

definition gi_exact_domain :: "otype \<Rightarrow> ZF set" where
  "gi_exact_domain \<sigma> = {x. Elem x (pp_b_domain \<sigma>)}"

definition gi_exact_app ::
  "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "gi_exact_app \<sigma> \<tau> f x = f \<acute> x"

lemma gi_exact_domain_member[simp]:
  "x \<in> gi_exact_domain \<sigma> \<longleftrightarrow> Elem x (pp_e_domain \<sigma>)"
  by (simp only: gi_exact_domain_def mem_Collect_eq)

lemma gi_exact_app_value[simp]:
  "gi_exact_app \<sigma> \<tau> f x = f \<acute> x"
  by (simp only: gi_exact_app_def)

lemma gi_exact_app_closed:
  assumes function_member: "f \<in> gi_exact_domain (Arr \<sigma> \<tau>)"
    and argument: "x \<in> gi_exact_domain \<sigma>"
  shows "gi_exact_app \<sigma> \<tau> f x \<in> gi_exact_domain \<tau>"
proof -
  have f: "Elem f (pp_e_domain (Arr \<sigma> \<tau>))"
    using function_member by (simp only: gi_exact_domain_member)
  have x: "Elem x (pp_e_domain \<sigma>)"
    using argument by (simp only: gi_exact_domain_member)
  have result_member: "Elem (f \<acute> x) (pp_e_domain \<tau>)"
    by (rule pp_e_app_closed[OF f x])
  show ?thesis using result_member
    by (simp only: gi_exact_app_value gi_exact_domain_member)
qed

theorem gi_exact_book_applicative_structure:
  "book_applicative_structure gi_exact_domain gi_exact_app"
  by standard (rule gi_exact_app_closed; assumption)

interpretation GI_Exact_App:
  book_applicative_structure gi_exact_domain gi_exact_app
  by (rule gi_exact_book_applicative_structure)

section \<open>Inhabited exact domains and total typed assignments\<close>

lemma gi_exact_default_member:
  "pp_e_default \<sigma> \<in> gi_exact_domain \<sigma>"
  using pp_e_default_in_domain[where \<sigma>=\<sigma>]
  by (simp only: gi_exact_domain_member)

theorem gi_exact_domain_nonempty:
  "gi_exact_domain \<sigma> \<noteq> {}"
  using gi_exact_default_member[where \<sigma>=\<sigma>] by blast

definition gi_exact_default_assignment :: "sgcontext \<Rightarrow> nat \<Rightarrow> ZF" where
  "gi_exact_default_assignment G n = pp_e_default (G n)"

lemma gi_exact_book_assignment_iff:
  "book_env_typed gi_exact_domain G g \<longleftrightarrow>
    (\<forall>n. Elem (g n) (pp_e_domain (G n)))"
  by (simp only: book_env_typed_def gi_exact_domain_member)

lemma gi_exact_default_assignment_typed:
  "book_env_typed gi_exact_domain G (gi_exact_default_assignment G)"
  unfolding book_env_typed_def gi_exact_default_assignment_def
  by (rule allI; rule gi_exact_default_member)

theorem gi_exact_total_assignment_exists:
  "\<exists>g. book_env_typed gi_exact_domain G g"
  by (rule exI[where x="gi_exact_default_assignment G"];
      rule gi_exact_default_assignment_typed)

lemma gi_exact_assignment_lookup:
  assumes typed: "book_env_typed gi_exact_domain G g"
  shows "Elem (g n) (pp_e_domain (G n))"
  using book_env_at[OF typed, where n=n]
  by (simp only: gi_exact_domain_member)

lemma gi_exact_assignment_update:
  assumes typed: "book_env_typed gi_exact_domain G g"
    and member: "Elem a (pp_e_domain (G n))"
  shows "book_env_typed gi_exact_domain G (g(n := a))"
proof (rule book_env_update[OF typed])
  show "a \<in> gi_exact_domain (G n)"
    using member by (simp only: gi_exact_domain_member)
qed

text \<open>
  Assignment existence here requires no richness premise on G: the
  recursively constructed exact default supplies a value at each assigned
  type. Richness will enter later where fresh names or source-language
  proof correspondence require it. The imported construction remains
  relative to HOL–ZF's set-theoretic assumptions.
\<close>

end
