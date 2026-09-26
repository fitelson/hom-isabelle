theory Bacon_Book_Lambda_I_Conversion_Denotation
  imports Bacon_Book_Lambda_I_Conversion_Application Bacon_Book_Lambda_I_Environment_Substitution_Conversion
    Bacon_Book_Environment_Development.Bacon_Book_Total_Assignments
begin

section \<open>Denotation by substitution of closed representatives\<close>

text \<open>
  Put r_g(n)=rep(g(n)) and J_g(A)=[A[r_g]]τ for a λI term A:τ of Σ.
  Source role: the representative-substitution interpretation in Bacon,
  Theorem 15.3, p.321, here over the internal λI-conversion quotient.

  Representation. The raw total definition selects τ by SOME; uniqueness
  identifies it with the stated type whenever A is typed. A typed total
  assignment gives each variable a class with a closed λI representative.
  Substitution protects bound names and inserts representatives single-pass.
  The typed/domain membership claims are proved for admitted λI terms
  only: typing alone does not give a legitimate class for a nonrelevant
  term. No semantic meaning of the choice defaults is asserted outside
  those guards. Locality and fixed closed-term substitution are separately
  proved syntactic facts.

  Scope. These are denotation basics: domain membership, variables,
  application, closed terms and locality. Invariance under internal
  conversion of the substituted terms and the λI model assembly are
  separate leaves. No Functionality, theoremhood or consistency
  assumption is introduced.
\<close>

definition book_lambda_I_conversion_result_type :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> otype" where
  "book_lambda_I_conversion_result_type G A = (SOME \<tau>. has_ntype book_minimal_logical_type G A \<tau>)"

definition book_lambda_I_conversion_representatives ::
  "(nat \<Rightarrow> 'c book_named_term set) \<Rightarrow> nat \<Rightarrow> 'c book_named_term" where
  "book_lambda_I_conversion_representatives g n = book_lambda_I_conversion_rep (g n)"

definition book_lambda_I_conversion_denote ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (nat \<Rightarrow> 'c book_named_term set) \<Rightarrow>
    'c book_named_term \<Rightarrow> 'c book_named_term set" where
  "book_lambda_I_conversion_denote \<Sigma> G g A =
    book_lambda_I_conversion_class \<Sigma> G (book_lambda_I_conversion_result_type G A)
      (book_environment_subst {} (book_lambda_I_conversion_representatives g) A)"

lemma book_lambda_I_conversion_result_type_eq:
  assumes typed: "has_ntype book_minimal_logical_type G A \<tau>"
  shows "book_lambda_I_conversion_result_type G A = \<tau>"
proof (unfold book_lambda_I_conversion_result_type_def, rule some_equality)
  show "has_ntype book_minimal_logical_type G A \<tau>" by (rule typed)
next
  fix \<rho>
  assume other: "has_ntype book_minimal_logical_type G A \<rho>"
  show "\<rho> = \<tau>" by (rule named_type_unique[OF other typed])
qed

lemma book_lambda_I_conversion_denote_eq:
  assumes typed: "has_ntype book_minimal_logical_type G A \<tau>"
  shows "book_lambda_I_conversion_denote \<Sigma> G g A =
    book_lambda_I_conversion_class \<Sigma> G \<tau> (book_environment_subst {} (book_lambda_I_conversion_representatives g) A)"
  by (simp only: book_lambda_I_conversion_denote_def book_lambda_I_conversion_result_type_eq[OF typed])

section \<open>Every selected representative has the variable's type\<close>

lemma book_lambda_I_conversion_representatives_closed_terms:
  assumes typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_lambda_I_conversion_representatives g n \<in> book_lambda_I_closed_terms \<Sigma> G (G n)"
proof -
  have member: "g n \<in> book_lambda_I_conversion_domain \<Sigma> G (G n)"
    by (rule book_env_at[where n=n, OF typed])
  show ?thesis unfolding book_lambda_I_conversion_representatives_def
    by (rule book_lambda_I_conversion_rep_closed_terms[OF member])
qed

lemma book_lambda_I_conversion_representatives_LI:
  assumes typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_lambda_I_conversion_representatives g n \<in> book_LI \<Sigma> G (G n)"
  by (rule book_lambda_I_closed_terms_LI[OF book_lambda_I_conversion_representatives_closed_terms[OF typed]])

lemma book_lambda_I_conversion_representatives_language:
  assumes typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_lambda_I_conversion_representatives g n) (G n)"
  by (rule book_lambda_I_closed_terms_language[OF book_lambda_I_conversion_representatives_closed_terms[OF typed]])

lemma book_lambda_I_conversion_representatives_type:
  assumes typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "has_ntype book_minimal_logical_type G (book_lambda_I_conversion_representatives g n) (G n)"
  by (rule book_lambda_I_closed_terms_type[OF book_lambda_I_conversion_representatives_closed_terms[OF typed]])

lemma book_lambda_I_conversion_representatives_closed:
  assumes typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "named_fv (book_lambda_I_conversion_representatives g n) = {}"
  by (rule book_lambda_I_closed_terms_closed[OF book_lambda_I_conversion_representatives_closed_terms[OF typed]])

lemma book_lambda_I_conversion_substituted_closed_terms:
  assumes member: "A \<in> book_LI \<Sigma> G \<tau>"
    and typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_environment_subst {} (book_lambda_I_conversion_representatives g) A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
proof -
  have substituted: "book_environment_subst {} (book_lambda_I_conversion_representatives g) A \<in> book_LI \<Sigma> G \<tau>"
    by (rule book_lambda_I_environment_subst_LI[OF member];
        rule book_lambda_I_conversion_representatives_LI[OF typed]
          book_lambda_I_conversion_representatives_closed[OF typed])
  have closed: "named_fv (book_environment_subst {} (book_lambda_I_conversion_representatives g) A) = {}"
    by (rule book_environment_subst_closed; rule book_lambda_I_conversion_representatives_closed[OF typed])
  show ?thesis by (rule book_lambda_I_closed_termsI_LI[OF substituted closed])
qed

theorem book_lambda_I_conversion_denote_type:
  assumes member: "A \<in> book_LI \<Sigma> G \<tau>"
    and typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_lambda_I_conversion_denote \<Sigma> G g A \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  by (simp only: book_lambda_I_conversion_denote_eq[OF book_language_type[OF book_lambda_I_terms_language[OF member]]];
      rule book_lambda_I_conversion_domainI[OF book_lambda_I_conversion_substituted_closed_terms[OF member typed]])

section \<open>Variables, closed terms and application\<close>

theorem book_lambda_I_conversion_denote_var:
  assumes typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_lambda_I_conversion_denote \<Sigma> G g (NVar n) = g n"
proof -
  have variable_type: "has_ntype book_minimal_logical_type G (NVar n) (G n)"
    by (rule has_ntype.Var)
  have member: "g n \<in> book_lambda_I_conversion_domain \<Sigma> G (G n)"
    by (rule book_env_at[where n=n, OF typed])
  have substituted: "book_environment_subst {} (book_lambda_I_conversion_representatives g) (NVar n) = book_lambda_I_conversion_rep (g n)"
    by (simp add: book_lambda_I_conversion_representatives_def)
  show ?thesis by (simp only: book_lambda_I_conversion_denote_eq[OF variable_type] substituted;
      rule book_lambda_I_conversion_rep_class[OF member])
qed

theorem book_lambda_I_conversion_denote_closed:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and closed: "named_fv A = {}"
  shows "book_lambda_I_conversion_denote \<Sigma> G g A = book_lambda_I_conversion_class \<Sigma> G \<tau> A"
  by (simp only: book_lambda_I_conversion_denote_eq[OF book_language_type[OF language]]
      book_environment_subst_closed_fixed[OF closed])

theorem book_lambda_I_conversion_denote_app:
  assumes head_member: "F \<in> book_LI \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument_member: "A \<in> book_LI \<Sigma> G \<sigma>"
    and typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_lambda_I_conversion_denote \<Sigma> G g (NApp F A) =
    book_lambda_I_conversion_app \<Sigma> G \<sigma> \<tau> (book_lambda_I_conversion_denote \<Sigma> G g F) (book_lambda_I_conversion_denote \<Sigma> G g A)"
proof -
  have head: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    by (rule book_lambda_I_terms_language[OF head_member])
  have argument: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    by (rule book_lambda_I_terms_language[OF argument_member])
  have application: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp F A) \<tau>"
    by (rule book_language_App[OF head argument])
  have substituted_head: "book_environment_subst {} (book_lambda_I_conversion_representatives g) F
    \<in> book_lambda_I_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    by (rule book_lambda_I_conversion_substituted_closed_terms[OF head_member typed])
  have substituted_argument: "book_environment_subst {} (book_lambda_I_conversion_representatives g) A
    \<in> book_lambda_I_closed_terms \<Sigma> G \<sigma>"
    by (rule book_lambda_I_conversion_substituted_closed_terms[OF argument_member typed])
  have represented: "book_lambda_I_conversion_app \<Sigma> G \<sigma> \<tau>
      (book_lambda_I_conversion_class \<Sigma> G (Arr \<sigma> \<tau>) (book_environment_subst {} (book_lambda_I_conversion_representatives g) F))
      (book_lambda_I_conversion_class \<Sigma> G \<sigma> (book_environment_subst {} (book_lambda_I_conversion_representatives g) A)) =
    book_lambda_I_conversion_class \<Sigma> G \<tau> (NApp (book_environment_subst {} (book_lambda_I_conversion_representatives g) F)
      (book_environment_subst {} (book_lambda_I_conversion_representatives g) A))"
    by (rule book_lambda_I_conversion_app_classes[OF substituted_head substituted_argument])
  show ?thesis by (simp only: book_lambda_I_conversion_denote_eq[OF book_language_type[OF application]]
      book_lambda_I_conversion_denote_eq[OF book_language_type[OF head]]
      book_lambda_I_conversion_denote_eq[OF book_language_type[OF argument]] book_environment_subst.simps;
      rule represented[symmetric])
qed

section \<open>Locality without a typing premise\<close>

theorem book_lambda_I_conversion_denote_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "book_lambda_I_conversion_denote \<Sigma> G g A = book_lambda_I_conversion_denote \<Sigma> G h A"
proof -
  have substituted: "book_environment_subst {} (book_lambda_I_conversion_representatives g) A =
    book_environment_subst {} (book_lambda_I_conversion_representatives h) A"
  proof (rule book_environment_subst_locality)
    fix n
    assume active: "n \<in> named_fv A - {}"
    have member: "n \<in> named_fv A" using active by simp
    have same: "g n = h n" by (rule agree[OF member])
    show "book_lambda_I_conversion_representatives g n = book_lambda_I_conversion_representatives h n"
      by (simp only: book_lambda_I_conversion_representatives_def same)
  qed
  show ?thesis by (simp only: book_lambda_I_conversion_denote_def substituted)
qed

end
