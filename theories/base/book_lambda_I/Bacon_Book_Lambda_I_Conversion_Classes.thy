theory Bacon_Book_Lambda_I_Conversion_Classes
  imports Bacon_Book_Lambda_I_Conversion
begin

section \<open>Internal conversion classes of closed λI terms\<close>

text \<open>
  Dτ consists of classes [A]τ of closed λI terms A:τ of the declared
  language, where B∈[A]τ exactly when B is a closed λI term of Σ at τ
  and A and B are internally convertible (Definition 14.13 read through
  Proposition 9.1: finite chains of β/η steps whose nodes are λI terms
  of Σ). Source: Bacon, p.320, allows the term construction to use the
  βη quotient; the λI variant uses the internal relation, which is the
  one the λI model class is stated with. Closed representatives track the
  repaired universal-closure and closed-decision route.

  Representation. A class is an ordinary set of named terms. Every node
  of an internal chain is a λI term of Σ at τ, so reflexivity needs the
  λI closed-term guard and class equality reflects internal conversion
  exactly on closed λI endpoints.

  Scope. This is quotient syntax, not a PER function-space construction
  or a semantic model. It assumes no theoremhood, consistency, richness,
  domain inhabitation, separation, or Functionality. A SOME representative
  is justified only for a value already belonging to the indicated domain.
\<close>

definition book_lambda_I_closed_terms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term set" where
  "book_lambda_I_closed_terms \<Sigma> G \<tau> =
    {A. book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau> \<and> named_fv A = {} \<and> book_lambda_I A}"

definition book_lambda_I_conversion_class ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term set" where
  "book_lambda_I_conversion_class \<Sigma> G \<tau> A =
    {B \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>. book_lambda_I_conv \<Sigma> G \<tau> A B}"

definition book_lambda_I_conversion_domain ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term set set" where
  "book_lambda_I_conversion_domain \<Sigma> G \<tau> =
    image (book_lambda_I_conversion_class \<Sigma> G \<tau>) (book_lambda_I_closed_terms \<Sigma> G \<tau>)"

definition book_lambda_I_conversion_rep :: "'c book_named_term set \<Rightarrow> 'c book_named_term" where
  "book_lambda_I_conversion_rep X = (SOME A. A \<in> X)"

lemma book_lambda_I_closed_termsI:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and closed: "named_fv A = {}" and lambda_I: "book_lambda_I A"
  shows "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  unfolding book_lambda_I_closed_terms_def by (rule CollectI, rule conjI[OF language conjI[OF closed lambda_I]])

lemma book_lambda_I_closed_terms_relevant:
  "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau> \<Longrightarrow> book_lambda_I A"
  unfolding book_lambda_I_closed_terms_def by blast

lemma book_lambda_I_closed_terms_LI:
  "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau> \<Longrightarrow> A \<in> book_LI \<Sigma> G \<tau>"
  unfolding book_lambda_I_closed_terms_def book_lambda_I_terms_def by blast

lemma book_lambda_I_closed_terms_formula:
  assumes language: "book_lambda_I_formula \<Sigma> G A" and closed: "named_fv A = {}"
  shows "A \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
  by (rule book_lambda_I_closed_termsI[OF conjunct1[OF language] closed conjunct2[OF language]])

lemma book_lambda_I_closed_terms_prop:
  assumes member: "A \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
  shows "book_lambda_I_formula \<Sigma> G A"
  using member unfolding book_lambda_I_closed_terms_def by blast

lemma book_lambda_I_closed_termsI_LI:
  assumes member: "A \<in> book_LI \<Sigma> G \<tau>" and closed: "named_fv A = {}"
  shows "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  using member closed unfolding book_lambda_I_closed_terms_def book_lambda_I_terms_def by blast

lemma book_lambda_I_closed_terms_language:
  "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau> \<Longrightarrow>
    book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
  unfolding book_lambda_I_closed_terms_def by blast

lemma book_lambda_I_closed_terms_type:
  assumes member: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  shows "has_ntype book_minimal_logical_type G A \<tau>"
  by (rule book_language_type[OF book_lambda_I_closed_terms_language[OF member]])

lemma book_lambda_I_closed_terms_closed:
  "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau> \<Longrightarrow> named_fv A = {}"
  unfolding book_lambda_I_closed_terms_def by blast

lemma book_lambda_I_closed_terms_refl:
  assumes member: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  shows "book_lambda_I_conv \<Sigma> G \<tau> A A"
  by (rule book_lambda_I_conv.Refl[OF book_lambda_I_closed_terms_LI[OF member]])

lemma book_lambda_I_conversion_classI:
  assumes member: "B \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    and conversion: "book_lambda_I_conv \<Sigma> G \<tau> A B"
  shows "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A"
  unfolding book_lambda_I_conversion_class_def by (rule CollectI, rule conjI[OF member conversion])

lemma book_lambda_I_conversion_class_member_closed_terms:
  "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A \<Longrightarrow> B \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  unfolding book_lambda_I_conversion_class_def by blast

lemma book_lambda_I_conversion_class_member_conversion:
  "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A \<Longrightarrow>
    book_lambda_I_conv \<Sigma> G \<tau> A B"
  unfolding book_lambda_I_conversion_class_def by blast

lemma book_lambda_I_conversion_class_member_language:
  assumes member: "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<tau>"
  by (rule book_lambda_I_closed_terms_language[OF book_lambda_I_conversion_class_member_closed_terms[OF member]])

lemma book_lambda_I_conversion_class_member_closed:
  assumes member: "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A"
  shows "named_fv B = {}"
  by (rule book_lambda_I_closed_terms_closed[OF book_lambda_I_conversion_class_member_closed_terms[OF member]])

lemma book_lambda_I_conversion_class_self_member:
  assumes member: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  shows "A \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A"
  by (rule book_lambda_I_conversion_classI[OF member book_lambda_I_closed_terms_refl[OF member]])

lemma book_lambda_I_conversion_class_nonempty:
  assumes member: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  shows "book_lambda_I_conversion_class \<Sigma> G \<tau> A \<noteq> {}"
  using book_lambda_I_conversion_class_self_member[OF member] by blast

section \<open>Equality of classes reflects conversion on closed endpoints\<close>

theorem book_lambda_I_conversion_class_eq:
  assumes conversion: "book_lambda_I_conv \<Sigma> G \<tau> A B"
  shows "book_lambda_I_conversion_class \<Sigma> G \<tau> A = book_lambda_I_conversion_class \<Sigma> G \<tau> B"
proof (rule set_eqI, rule iffI)
  fix C
  assume member: "C \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A"
  have closed_C: "C \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    by (rule book_lambda_I_conversion_class_member_closed_terms[OF member])
  have AC: "book_lambda_I_conv \<Sigma> G \<tau> A C"
    by (rule book_lambda_I_conversion_class_member_conversion[OF member])
  have BC: "book_lambda_I_conv \<Sigma> G \<tau> B C"
    by (rule book_lambda_I_conv.Trans[OF book_lambda_I_conv.Sym[OF conversion] AC])
  show "C \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> B" by (rule book_lambda_I_conversion_classI[OF closed_C BC])
next
  fix C
  assume member: "C \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> B"
  have closed_C: "C \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    by (rule book_lambda_I_conversion_class_member_closed_terms[OF member])
  have BC: "book_lambda_I_conv \<Sigma> G \<tau> B C"
    by (rule book_lambda_I_conversion_class_member_conversion[OF member])
  have AC: "book_lambda_I_conv \<Sigma> G \<tau> A C"
    by (rule book_lambda_I_conv.Trans[OF conversion BC])
  show "C \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A" by (rule book_lambda_I_conversion_classI[OF closed_C AC])
qed

theorem book_lambda_I_conversion_class_eq_iff:
  assumes first: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    and second: "B \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  shows "book_lambda_I_conversion_class \<Sigma> G \<tau> A = book_lambda_I_conversion_class \<Sigma> G \<tau> B
    \<longleftrightarrow> book_lambda_I_conv \<Sigma> G \<tau> A B"
proof
  assume equality: "book_lambda_I_conversion_class \<Sigma> G \<tau> A = book_lambda_I_conversion_class \<Sigma> G \<tau> B"
  have self: "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> B"
    by (rule book_lambda_I_conversion_class_self_member[OF second])
  have member: "B \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A" using self equality by simp
  show "book_lambda_I_conv \<Sigma> G \<tau> A B"
    by (rule book_lambda_I_conversion_class_member_conversion[OF member])
next
  assume conversion: "book_lambda_I_conv \<Sigma> G \<tau> A B"
  show "book_lambda_I_conversion_class \<Sigma> G \<tau> A = book_lambda_I_conversion_class \<Sigma> G \<tau> B"
    by (rule book_lambda_I_conversion_class_eq[OF conversion])
qed

section \<open>Domain values and guarded representative choice\<close>

lemma book_lambda_I_conversion_domainI:
  assumes member: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  shows "book_lambda_I_conversion_class \<Sigma> G \<tau> A \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  unfolding book_lambda_I_conversion_domain_def by (rule imageI[OF member])

lemma book_lambda_I_conversion_domainE:
  assumes member: "X \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  obtains A where "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>" and "X = book_lambda_I_conversion_class \<Sigma> G \<tau> A"
proof -
  obtain A where closed_A: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    and shape: "X = book_lambda_I_conversion_class \<Sigma> G \<tau> A"
    using member unfolding book_lambda_I_conversion_domain_def by blast
  show thesis by (rule that[OF closed_A shape])
qed

lemma book_lambda_I_conversion_value_nonempty:
  assumes member: "X \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  shows "X \<noteq> {}"
proof -
  obtain A where closed_A: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    and shape: "X = book_lambda_I_conversion_class \<Sigma> G \<tau> A"
    by (rule book_lambda_I_conversion_domainE[OF member]; rule that; assumption)
  show ?thesis by (simp only: shape; rule book_lambda_I_conversion_class_nonempty[OF closed_A])
qed

lemma book_lambda_I_conversion_domain_member_closed_terms:
  assumes domain: "X \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>" and member: "A \<in> X"
  shows "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
proof -
  obtain B where closed_B: "B \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    and shape: "X = book_lambda_I_conversion_class \<Sigma> G \<tau> B"
    by (rule book_lambda_I_conversion_domainE[OF domain]; rule that; assumption)
  have in_class: "A \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> B" using member by (simp only: shape)
  show ?thesis by (rule book_lambda_I_conversion_class_member_closed_terms[OF in_class])
qed

lemma book_lambda_I_conversion_rep_member:
  assumes domain: "X \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  shows "book_lambda_I_conversion_rep X \<in> X"
proof -
  have inhabited: "\<exists>A. A \<in> X" using book_lambda_I_conversion_value_nonempty[OF domain] by blast
  show ?thesis unfolding book_lambda_I_conversion_rep_def by (rule someI_ex; rule inhabited)
qed

lemma book_lambda_I_conversion_rep_closed_terms:
  assumes domain: "X \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  shows "book_lambda_I_conversion_rep X \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
  by (rule book_lambda_I_conversion_domain_member_closed_terms[OF domain book_lambda_I_conversion_rep_member[OF domain]])

theorem book_lambda_I_conversion_rep_class:
  assumes domain: "X \<in> book_lambda_I_conversion_domain \<Sigma> G \<tau>"
  shows "book_lambda_I_conversion_class \<Sigma> G \<tau> (book_lambda_I_conversion_rep X) = X"
proof -
  obtain A where closed_A: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<tau>"
    and shape: "X = book_lambda_I_conversion_class \<Sigma> G \<tau> A"
    by (rule book_lambda_I_conversion_domainE[OF domain]; rule that; assumption)
  have member: "book_lambda_I_conversion_rep X \<in> book_lambda_I_conversion_class \<Sigma> G \<tau> A"
    using book_lambda_I_conversion_rep_member[OF domain] by (simp only: shape)
  have conversion: "book_lambda_I_conv \<Sigma> G \<tau> A (book_lambda_I_conversion_rep X)"
    by (rule book_lambda_I_conversion_class_member_conversion[OF member])
  have equality: "book_lambda_I_conversion_class \<Sigma> G \<tau> A =
    book_lambda_I_conversion_class \<Sigma> G \<tau> (book_lambda_I_conversion_rep X)"
    by (rule book_lambda_I_conversion_class_eq[OF conversion])
  show ?thesis by (rule trans[OF equality[symmetric] shape[symmetric]])
qed

end
