theory Bacon_Book_Representative_Independence
  imports Bacon_Book_Representative_One_Change
begin

section \<open>Finite changes establish representative independence\<close>

context book_C_identity_world
begin

lemma identity_environment_finite_changes:
  assumes finite: "finite X"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and rm: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
    and sm: "\<And>n. s n \<in> book_closed_terms \<Sigma> G (G n)"
    and agree: "\<And>n. n \<in> X \<Longrightarrow>
      book_C_identity_class \<Sigma> G w (G n) (r n) = book_C_identity_class \<Sigma> G w (G n) (s n)"
  shows "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} r A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (book_paste_assignment X s r) A)"
  using finite agree
proof (induction X rule: finite_induct)
  case empty
  have same: "book_paste_assignment {} s r = r"
    by (rule ext; simp add: book_paste_assignment_def)
  show ?case by (simp only: same)
next
  case (insert n X)
  let ?k = "book_paste_assignment X s r"
  have restricted: "\<And>m. m \<in> X \<Longrightarrow>
    book_C_identity_class \<Sigma> G w (G m) (r m) = book_C_identity_class \<Sigma> G w (G m) (s m)"
    by (rule insert.prems; rule insertI2; assumption)
  have first: "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} r A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} ?k A)"
    by (rule insert.IH[OF restricted])
  have km: "\<And>m. ?k m \<in> book_closed_terms \<Sigma> G (G m)"
    using rm sm by (auto simp: book_paste_assignment_def)
  have at_n: "?k n = r n" by (rule book_paste_outside[OF insert.hyps(2)])
  have equal: "book_C_identity_class \<Sigma> G w (G n) (?k n) =
    book_C_identity_class \<Sigma> G w (G n) (s n)"
    by (simp only: at_n; rule insert.prems; rule insertI1)
  have second: "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} ?k A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} (?k(n := s n)) A)"
    by (rule identity_environment_one_update[OF language km sm[of n] equal])
  have paste: "book_paste_assignment (insert n X) s r = ?k(n := s n)"
    by (rule ext; simp add: book_paste_assignment_def)
  show ?case by (simp only: paste; rule trans[OF first second])
qed

theorem identity_environment_representative_independence:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and rm: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
    and sm: "\<And>n. s n \<in> book_closed_terms \<Sigma> G (G n)"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow>
      book_C_identity_class \<Sigma> G w (G n) (r n) = book_C_identity_class \<Sigma> G w (G n) (s n)"
  shows "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} r A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} s A)"
proof -
  let ?k = "book_paste_assignment (named_fv A) s r"
  have first: "book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} r A) =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} ?k A)"
    by (rule identity_environment_finite_changes[OF named_fv_finite language rm sm agree])
  have same: "book_environment_subst {} ?k A = book_environment_subst {} s A"
    by (rule book_environment_subst_locality; simp add: book_paste_assignment_def)
  show ?thesis using first by (simp only: same)
qed

theorem book_C_term_denote_any_representatives:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
    and rm: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
    and represents: "\<And>n. n \<in> named_fv A \<Longrightarrow>
      book_C_identity_class \<Sigma> G w (G n) (r n) = g n"
  shows "book_C_term_denote \<Sigma> G w g A =
    book_C_identity_class \<Sigma> G w \<tau> (book_environment_subst {} r A)"
proof -
  have agree: "\<And>n. n \<in> named_fv A \<Longrightarrow>
    book_C_identity_class \<Sigma> G w (G n) (book_C_term_representatives g n) =
    book_C_identity_class \<Sigma> G w (G n) (r n)"
    by (simp only: book_C_term_representatives_def identity_rep_class[OF book_env_at[OF typed]]; rule represents[symmetric]; assumption)
  show ?thesis by (simp only: book_C_term_denote_eq[OF book_language_type[OF language]];
    rule identity_environment_representative_independence[OF language book_C_term_representatives_closed_terms[OF typed] rm agree])
qed

end

text \<open>
  Only finitely many free variables occur in A. Change their closed
  representatives one at a time, applying the checked one-change
  theorem, and then use syntactic locality. Agreement is required
  only on FV(A), not on all names. This proves that the canonical
  interpretation is independent of its Hilbert-choice representatives
  in the exact identity classes of Definition 18.9.
\<close>

end
