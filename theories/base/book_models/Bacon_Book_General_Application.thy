theory Bacon_Book_General_Application
  imports Bacon_Book_General_Environment
begin

section \<open>Argument values with the source's variable convention\<close>

text \<open>
  For an argument A, use g(n) when A is the variable n and Jg(A)
  otherwise. Definition 9.1, p.190, permits a variable argument even
  when that variable is not a standalone term of the chosen language.
  This convention supplies the argument value in Definition 14.13's
  application equation without normalizing J outside its admitted domain.

  Representation: book_argument_value inspects only the outer constructor.
  It does not change J, extend the admitted set, or impose conversion
  requirements on unadmitted terms.
\<close>

definition book_argument_value ::
  "((nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v) \<Rightarrow>
    (nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v" where
  "book_argument_value J g A = (case A of NVar n \<Rightarrow> g n | _ \<Rightarrow> J g A)"

lemma book_argument_value_Var:
  "book_argument_value J g (NVar n) = g n"
  by (simp add: book_argument_value_def)

lemma book_argument_value_nonvariable:
  assumes nonvariable: "\<not> (\<exists>n. A = NVar n)"
  shows "book_argument_value J g A = J g A"
  using nonvariable by (cases A) (auto simp: book_argument_value_def)

context book_general_environment_conditions
begin

lemma book_argument_value_admitted:
  assumes member: "A \<in> admitted" and typed: "book_env_typed domain stock g"
  shows "book_argument_value denote g A = denote g A"
proof (cases "\<exists>n. A = NVar n")
  case True
  obtain n where shape: "A = NVar n" using True by blast
  have variable_member: "NVar n \<in> admitted" using member by (simp only: shape)
  have equation: "denote g (NVar n) = g n" by (rule denote_var[OF variable_member typed])
  show ?thesis by (simp only: shape book_argument_value_Var equation)
next
  case False
  show ?thesis by (rule book_argument_value_nonvariable[OF False])
qed

lemma book_argument_value_type:
  assumes language: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and typed: "book_env_typed domain stock g"
    and admissible: "A \<in> admitted \<or> (\<exists>n. A = NVar n)"
  shows "book_argument_value denote g A \<in> domain \<sigma>"
proof (rule disjE[OF admissible])
  assume member: "A \<in> admitted"
  have denotation_member: "denote g A \<in> domain \<sigma>" by (rule denote_type[OF member language typed])
  show ?thesis by (simp only: book_argument_value_admitted[OF member typed]; rule denotation_member)
next
  assume variable: "\<exists>n. A = NVar n"
  obtain n where shape: "A = NVar n" using variable by blast
  have type_eq: "\<sigma> = stock n" using language by (simp only: shape book_language_var_iff)
  have assignment_member: "g n \<in> domain (stock n)" by (rule book_env_at[OF typed])
  show ?thesis by (simp only: shape book_argument_value_Var type_eq; rule assignment_member)
qed

section \<open>One application equation for both kinds of argument\<close>

text \<open>
  Jg(FA)=Appστ(Jg(F),arg(g,A)) when F and FA are admitted,
  F:σ→τ, A:σ, g is typed, and A is either admitted or a variable.
  For admitted A, arg(g,A)=Jg(A). In the variable case, typing fixes
  σ=G(n), and the additional variable-application clause uses g(n).

  The admitted-or-variable condition remains an EXPLICIT premise.
  A later proof of Definition 9.1's decomposition conditions may supply
  it; no claim that an arbitrary admitted collection is a λ-language
  is made here. No richness, nonemptiness, or Functionality is assumed.
\<close>

theorem book_general_denote_app:
  assumes head_member: "F \<in> admitted"
    and application_member: "NApp F A \<in> admitted"
    and head: "book_in_language logical_type logical_signature signature stock F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and typed: "book_env_typed domain stock g"
    and admissible: "A \<in> admitted \<or> (\<exists>n. A = NVar n)"
  shows "denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (book_argument_value denote g A)"
proof (cases "A \<in> admitted")
  case True
  have equation: "denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (denote g A)"
    by (rule denote_app[OF head_member True application_member head argument typed])
  show ?thesis by (simp only: book_argument_value_admitted[OF True typed]; rule equation)
next
  case False
  obtain n where shape: "A = NVar n" using admissible False by blast
  have type_eq: "\<sigma> = stock n" using argument by (simp only: shape book_language_var_iff)
  have variable_head: "book_in_language logical_type logical_signature signature stock F (Arr (stock n) \<tau>)"
    using head by (simp only: type_eq)
  have variable_application: "NApp F (NVar n) \<in> admitted"
    using application_member by (simp only: shape)
  have equation: "denote g (NApp F (NVar n)) = app (stock n) \<tau> (denote g F) (g n)"
    by (rule denote_app_variable[OF head_member variable_application variable_head typed])
  show ?thesis by (simp only: shape type_eq book_argument_value_Var; rule equation)
qed

end

end
