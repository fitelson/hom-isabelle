theory Bacon_Book_Term_Denotation
  imports Bacon_Book_Identity_Conversion
begin

section \<open>The canonical interpretation on identity classes\<close>

definition book_C_term_representatives ::
  "(nat \<Rightarrow> 'c book_named_term set) \<Rightarrow> nat \<Rightarrow> 'c book_named_term" where
  "book_C_term_representatives g n = book_C_identity_rep (g n)"

definition book_C_term_denote where
  "book_C_term_denote \<Sigma> G w g A =
    book_C_identity_class \<Sigma> G w (book_conversion_result_type G A)
      (book_environment_subst {} (book_C_term_representatives g) A)"

lemma book_C_term_denote_eq:
  "has_ntype book_minimal_logical_type G A \<tau> \<Longrightarrow>
    book_C_term_denote \<Sigma> G w g A =
      book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (book_C_term_representatives g) A)"
  by (simp only: book_C_term_denote_def book_conversion_result_type_eq)

lemma book_C_identity_domainI:
  "A \<in> book_closed_terms \<Sigma> G \<tau> \<Longrightarrow>
    book_C_identity_class \<Sigma> G w \<tau> A \<in> book_C_identity_domain \<Sigma> G w \<tau>"
  unfolding book_C_identity_domain_def by (rule imageI; assumption)

text \<open>
  At a canonical world w, put r_g(n)=rep(g(n)) and
  Jᵂ_g(A)=[A[r_g]]ᵂ. Classes are identity-in-w classes from
  Definition 18.9, not conversion classes. The previously defined
  result-type selector is reused only as syntax: uniqueness identifies
  its value with the displayed type. No old semantic denotation is used.
\<close>

context book_C_identity_world
begin

lemma book_C_term_representatives_closed_terms:
  assumes typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_C_term_representatives g n \<in> book_closed_terms \<Sigma> G (G n)"
proof -
  have member: "g n \<in> book_C_identity_domain \<Sigma> G w (G n)"
    by (rule book_env_at[where n=n, OF typed])
  show ?thesis unfolding book_C_term_representatives_def
    by (rule identity_rep_typed[OF member])
qed

lemma book_C_term_representatives_language:
  assumes typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_C_term_representatives g n) (G n)"
  by (rule book_closed_terms_language[OF book_C_term_representatives_closed_terms[OF typed]])

lemma book_C_term_representatives_type:
  assumes typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "has_ntype book_minimal_logical_type G (book_C_term_representatives g n) (G n)"
  by (rule book_closed_terms_type[OF book_C_term_representatives_closed_terms[OF typed]])

lemma book_C_term_representatives_closed:
  assumes typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "named_fv (book_C_term_representatives g n) = {}"
  by (rule book_closed_terms_closed[OF book_C_term_representatives_closed_terms[OF typed]])

lemma book_C_term_substituted_closed_terms:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_environment_subst {} (book_C_term_representatives g) A \<in> book_closed_terms \<Sigma> G \<tau>"
proof -
  have substituted_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_environment_subst {} (book_C_term_representatives g) A) \<tau>"
    by (rule book_environment_subst_language[OF language];
        rule book_C_term_representatives_language[OF typed])
  have closed: "named_fv (book_environment_subst {} (book_C_term_representatives g) A) = {}"
    by (rule book_environment_subst_closed; rule book_C_term_representatives_closed[OF typed])
  show ?thesis by (rule book_closed_termsI[OF substituted_language closed])
qed

theorem book_C_term_denote_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_C_term_denote \<Sigma> G w g A \<in> book_C_identity_domain \<Sigma> G w \<tau>"
  by (simp only: book_C_term_denote_eq[OF book_language_type[OF language]];
      rule book_C_identity_domainI[OF book_C_term_substituted_closed_terms[OF language typed]])

section \<open>Variables, closed terms and application\<close>

theorem book_C_term_denote_var:
  assumes typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_C_term_denote \<Sigma> G w g (NVar n) = g n"
proof -
  have variable_type: "has_ntype book_minimal_logical_type G (NVar n) (G n)"
    by (rule has_ntype.Var)
  have member: "g n \<in> book_C_identity_domain \<Sigma> G w (G n)"
    by (rule book_env_at[where n=n, OF typed])
  have substituted: "book_environment_subst {} (book_C_term_representatives g) (NVar n) = book_C_identity_rep (g n)"
    by (simp add: book_C_term_representatives_def)
  show ?thesis by (simp only: book_C_term_denote_eq[OF variable_type] substituted;
      rule identity_rep_class[OF member])
qed

theorem book_C_term_denote_closed:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and closed: "named_fv A = {}"
  shows "book_C_term_denote \<Sigma> G w g A = book_C_identity_class \<Sigma> G w \<tau> A"
  by (simp only: book_C_term_denote_eq[OF book_language_type[OF language]]
      book_environment_subst_closed_fixed[OF closed])

theorem book_C_term_denote_app:
  assumes head: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_C_term_denote \<Sigma> G w g (NApp F A) =
    book_C_term_app \<Sigma> G w \<sigma> \<tau> (book_C_term_denote \<Sigma> G w g F) (book_C_term_denote \<Sigma> G w g A)"
proof -
  have application: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp F A) \<tau>"
    by (rule book_language_App[OF head argument])
  have substituted_head: "book_environment_subst {} (book_C_term_representatives g) F
    \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    by (rule book_C_term_substituted_closed_terms[OF head typed])
  have substituted_argument: "book_environment_subst {} (book_C_term_representatives g) A
    \<in> book_closed_terms \<Sigma> G \<sigma>"
    by (rule book_C_term_substituted_closed_terms[OF argument typed])
  have represented: "book_C_term_app \<Sigma> G w \<sigma> \<tau>
      (book_C_identity_class \<Sigma> G w (Arr \<sigma> \<tau>) (book_environment_subst {} (book_C_term_representatives g) F))
      (book_C_identity_class \<Sigma> G w \<sigma> (book_environment_subst {} (book_C_term_representatives g) A)) =
    book_C_identity_class \<Sigma> G w \<tau> (NApp (book_environment_subst {} (book_C_term_representatives g) F)
      (book_environment_subst {} (book_C_term_representatives g) A))"
    by (rule term_app_classes[OF substituted_head substituted_argument])
  show ?thesis by (simp only: book_C_term_denote_eq[OF book_language_type[OF application]]
      book_C_term_denote_eq[OF book_language_type[OF head]]
      book_C_term_denote_eq[OF book_language_type[OF argument]] book_environment_subst.simps;
      rule represented[symmetric])
qed

section \<open>Locality without a typing premise\<close>

theorem book_C_term_denote_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "book_C_term_denote \<Sigma> G w g A = book_C_term_denote \<Sigma> G w h A"
proof -
  have substituted: "book_environment_subst {} (book_C_term_representatives g) A =
    book_environment_subst {} (book_C_term_representatives h) A"
  proof (rule book_environment_subst_locality)
    fix n
    assume active: "n \<in> named_fv A - {}"
    have member: "n \<in> named_fv A" using active by simp
    have same: "g n = h n" by (rule agree[OF member])
    show "book_C_term_representatives g n = book_C_term_representatives h n"
      by (simp only: book_C_term_representatives_def same)
  qed
  show ?thesis by (simp only: book_C_term_denote_def substituted)
qed

end

text \<open>
  Typed assignments supply actual closed representatives in the world's
  language. The interpretation has typed values and the variable,
  application, closed-term and locality equations. This is an ordinary
  interpretation on the term structure; transport into the recursive
  modal domains and the future abstraction equation remain separate.
\<close>

end
