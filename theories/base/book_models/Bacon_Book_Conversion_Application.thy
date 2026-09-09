theory Bacon_Book_Conversion_Application
  imports Bacon_Book_Conversion_Classes
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Contexts
begin

section \<open>Typed application on ordinary conversion classes\<close>

text \<open>
  For X∈Dσ→τ and Y∈Dσ, define X·Y as [rep(X) rep(Y)]τ.
  Representatives belong to their classes, so they are typed closed
  terms. Application preserves that property and hence gives a member
  of Dτ. The input memberships justify representative choice; no
  nonemptiness assertion about an arbitrary type domain is needed.

  Source role: application in the βη term quotient on Bacon p.320.
  These domains are ordinary sets of conversion classes, not PER
  function spaces. No richness, theoremhood, model, Functionality, or
  pointwise extensionality assumption is used.
\<close>

definition book_conversion_app ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow>
    'c book_named_term set \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term set" where
  "book_conversion_app \<Sigma> G \<sigma> \<tau> X Y =
    book_conversion_class \<Sigma> G \<tau> (NApp (book_conversion_rep X) (book_conversion_rep Y))"

lemma book_closed_terms_App:
  assumes head: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
  shows "NApp F A \<in> book_closed_terms \<Sigma> G \<tau>"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp F A) \<tau>"
    by (rule book_language_App[
      OF book_closed_terms_language[OF head] book_closed_terms_language[OF argument]])
  have closed: "named_fv (NApp F A) = {}"
    by (simp only: named_fv.simps book_closed_terms_closed[OF head]
      book_closed_terms_closed[OF argument] Un_empty_left)
  show ?thesis by (rule book_closed_termsI[OF language closed])
qed

theorem book_conversion_app_type:
  assumes head: "X \<in> book_conversion_domain \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument: "Y \<in> book_conversion_domain \<Sigma> G \<sigma>"
  shows "book_conversion_app \<Sigma> G \<sigma> \<tau> X Y \<in> book_conversion_domain \<Sigma> G \<tau>"
proof -
  have typed_head: "book_conversion_rep X \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    by (rule book_conversion_rep_closed_terms[OF head])
  have typed_argument: "book_conversion_rep Y \<in> book_closed_terms \<Sigma> G \<sigma>"
    by (rule book_conversion_rep_closed_terms[OF argument])
  have application: "NApp (book_conversion_rep X) (book_conversion_rep Y) \<in> book_closed_terms \<Sigma> G \<tau>"
    by (rule book_closed_terms_App[OF typed_head typed_argument])
  show ?thesis unfolding book_conversion_app_def by (rule book_conversion_domainI[OF application])
qed

section \<open>Application agrees with representatives of the input classes\<close>

lemma book_conversion_class_rep_conversion:
  assumes member: "A \<in> book_closed_terms \<Sigma> G \<tau>"
  shows "named_raw_beta_eta book_minimal_logical_type G \<tau>
    A (book_conversion_rep (book_conversion_class \<Sigma> G \<tau> A))"
proof -
  have domain: "book_conversion_class \<Sigma> G \<tau> A \<in> book_conversion_domain \<Sigma> G \<tau>"
    by (rule book_conversion_domainI[OF member])
  have representative: "book_conversion_rep (book_conversion_class \<Sigma> G \<tau> A)
    \<in> book_conversion_class \<Sigma> G \<tau> A"
    by (rule book_conversion_rep_member[OF domain])
  show ?thesis by (rule book_conversion_class_member_conversion[OF representative])
qed

theorem book_conversion_app_classes:
  assumes head: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
  shows "book_conversion_app \<Sigma> G \<sigma> \<tau>
      (book_conversion_class \<Sigma> G (Arr \<sigma> \<tau>) F)
      (book_conversion_class \<Sigma> G \<sigma> A) =
    book_conversion_class \<Sigma> G \<tau> (NApp F A)"
proof -
  let ?X = "book_conversion_class \<Sigma> G (Arr \<sigma> \<tau>) F"
  let ?Y = "book_conversion_class \<Sigma> G \<sigma> A"
  have head_conversion: "named_raw_beta_eta book_minimal_logical_type G (Arr \<sigma> \<tau>)
    F (book_conversion_rep ?X)"
    by (rule book_conversion_class_rep_conversion[OF head])
  have argument_conversion: "named_raw_beta_eta book_minimal_logical_type G \<sigma>
    A (book_conversion_rep ?Y)"
    by (rule book_conversion_class_rep_conversion[OF argument])
  have application_conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau>
    (NApp F A) (NApp (book_conversion_rep ?X) (book_conversion_rep ?Y))"
    by (rule named_conversion_App[OF head_conversion argument_conversion])
  have equality: "book_conversion_class \<Sigma> G \<tau> (NApp F A) =
    book_conversion_class \<Sigma> G \<tau> (NApp (book_conversion_rep ?X) (book_conversion_rep ?Y))"
    by (rule book_conversion_class_eq[OF application_conversion])
  show ?thesis unfolding book_conversion_app_def by (rule equality[symmetric])
qed

corollary book_conversion_app_represents:
  assumes head: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and head_closed: "named_fv F = {}" and argument_closed: "named_fv A = {}"
  shows "book_conversion_app \<Sigma> G \<sigma> \<tau>
      (book_conversion_class \<Sigma> G (Arr \<sigma> \<tau>) F)
      (book_conversion_class \<Sigma> G \<sigma> A) =
    book_conversion_class \<Sigma> G \<tau> (NApp F A)"
  by (rule book_conversion_app_classes[
    OF book_closed_termsI[OF head head_closed] book_closed_termsI[OF argument argument_closed]])

end
