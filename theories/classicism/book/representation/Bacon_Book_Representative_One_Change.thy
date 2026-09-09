theory Bacon_Book_Representative_One_Change
  imports Bacon_Book_Representative_Substitution
begin

context book_C_identity_world
begin

lemma identity_environment_update_application:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and replacements: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
    and member: "N \<in> book_closed_terms \<Sigma> G (G x)"
  shows "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (r(x := N)) A) =
    book_C_term_app \<Sigma> G w (G x) \<tau>
      (book_C_identity_class \<Sigma> G w (Arr (G x) \<tau>) (NLam x (book_environment_subst {x} r A)))
      (book_C_identity_class \<Sigma> G w (G x) N)"
proof -
  let ?K = "NLam x (book_environment_subst {x} r A)"
  let ?R = "book_environment_subst {} (r(x := N)) A"
  have km: "?K \<in> book_closed_terms \<Sigma> G (Arr (G x) \<tau>)"
    by (rule book_closed_environment_abstraction[OF language replacements])
  have updated: "\<And>n. (r(x := N)) n \<in> book_closed_terms \<Sigma> G (G n)"
    using replacements member by auto
  have rm: "?R \<in> book_closed_terms \<Sigma> G \<tau>"
    by (rule book_closed_environment_instance[OF language updated])
  have application: "NApp ?K N \<in> book_closed_terms \<Sigma> G \<tau>"
    by (rule book_closed_terms_App[OF km member])
  have rc: "\<And>n. named_fv (r n) = {}" by (rule book_closed_terms_closed[OF replacements])
  have nc: "named_fv N = {}" by (rule book_closed_terms_closed[OF member])
  have free: "named_free_for N x (book_environment_subst {x} r A)"
    by (rule book_exists_closed_free_for[OF nc])
  have body: "named_subst x N (book_environment_subst {x} r A) = ?R"
    by (rule book_environment_subst_unprotect[OF rc]; simp)
  have beta: "named_beta_contract (NApp ?K N) ?R"
    using named_beta_contract.beta[OF free] by (simp only: body)
  have conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> (NApp ?K N) ?R"
  proof (rule named_beta_eta_in_language.Beta)
    show "named_in_language book_minimal_logical_type (\<lambda>_. UNIV) G (NApp ?K N) \<tau>"
      by (simp only: named_universal_language; rule book_closed_terms_type[OF application])
    show "named_in_language book_minimal_logical_type (\<lambda>_. UNIV) G ?R \<tau>"
      by (simp only: named_universal_language; rule book_closed_terms_type[OF rm])
    show "named_compatible_step named_beta_contract (NApp ?K N) ?R"
      by (rule named_compatible_step.root; rule beta)
  qed
  have classes: "book_C_identity_class \<Sigma> G w \<tau> (NApp ?K N) =
    book_C_identity_class \<Sigma> G w \<tau> ?R"
    by (rule identity_class_conversion[OF application rm conversion])
  show ?thesis by (simp only: term_app_classes[OF km member]; rule classes[symmetric])
qed

theorem identity_environment_two_updates:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and replacements: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
    and nm: "N \<in> book_closed_terms \<Sigma> G (G x)" and pm: "P \<in> book_closed_terms \<Sigma> G (G x)"
    and equal: "book_C_identity_class \<Sigma> G w (G x) N = book_C_identity_class \<Sigma> G w (G x) P"
  shows "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (r(x := N)) A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (r(x := P)) A)"
  by (simp only: identity_environment_update_application[OF language replacements nm]
    identity_environment_update_application[OF language replacements pm] equal)

theorem identity_environment_one_update:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and replacements: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
    and nm: "N \<in> book_closed_terms \<Sigma> G (G x)"
    and equal: "book_C_identity_class \<Sigma> G w (G x) (r x) = book_C_identity_class \<Sigma> G w (G x) N"
  shows "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} r A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (r(x := N)) A)"
  using identity_environment_two_updates[OF language replacements replacements[of x] nm equal]
  by simp

end

text \<open>
  A single change of representative is handled by the one closed
  abstraction λx.A[r] with x protected. β identifies its applications
  with the two substituted terms. Equal argument classes give equal
  applications in the already constructed term algebra. We do not
  infer equality of abstractions from pointwise equality or assume
  representative independence to prove this step.
\<close>

end
