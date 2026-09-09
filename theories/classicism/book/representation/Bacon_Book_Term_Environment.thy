theory Bacon_Book_Term_Environment
  imports Bacon_Book_Term_Denotation Bacon_Book_Full_Term_Modalized_Sets
begin

section \<open>The term interpretation satisfies Bacon's environment condition\<close>

context book_C_identity_world
begin

theorem book_C_term_denote_conversion:
  assumes al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<tau>"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
    and typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
  shows "book_C_term_denote \<Sigma> G w g A = book_C_term_denote \<Sigma> G w g B"
proof -
  have substituted: "named_raw_beta_eta book_minimal_logical_type G \<tau>
      (book_environment_subst {} (book_C_term_representatives g) A)
      (book_environment_subst {} (book_C_term_representatives g) B)"
    by (rule book_environment_subst_raw_conversion[OF _ _ conversion];
      rule book_C_term_representatives_closed[OF typed] book_C_term_representatives_type[OF typed])
  show ?thesis
    by (simp only: book_C_term_denote_eq[OF book_language_type[OF al]]
      book_C_term_denote_eq[OF book_language_type[OF bl]];
      rule identity_class_conversion[OF book_C_term_substituted_closed_terms[OF al typed]
        book_C_term_substituted_closed_terms[OF bl typed] substituted])
qed

theorem book_C_term_separated_environment:
  "book_environment_separated (book_C_identity_domain \<Sigma> G w)
    (book_C_term_app \<Sigma> G w) book_minimal_logical_type UNIV \<Sigma> G UNIV
    (book_C_term_denote \<Sigma> G w)"
  apply unfold_locales
       apply (rule term_app_typed; assumption)
      apply (rule book_C_term_denote_type; assumption)
     apply (rule book_C_term_denote_var; assumption)
    apply (rule book_C_term_denote_app; assumption)
   apply (rule book_C_term_denote_locality; assumption)
  apply (rule book_C_term_denote_conversion; assumption)
  done

theorem book_C_term_full_environment:
  "book_full_environment (book_C_identity_domain \<Sigma> G w)
    (book_C_term_app \<Sigma> G w) book_minimal_logical_type UNIV \<Sigma> G
    (book_C_term_denote \<Sigma> G w)"
proof -
  interpret S: book_environment_separated "book_C_identity_domain \<Sigma> G w"
    "book_C_term_app \<Sigma> G w" book_minimal_logical_type UNIV \<Sigma> G UNIV
    "book_C_term_denote \<Sigma> G w" by (rule book_C_term_separated_environment)
  interpret E: book_environment_conditions "book_C_identity_domain \<Sigma> G w"
    "book_C_term_app \<Sigma> G w" book_minimal_logical_type UNIV \<Sigma> G UNIV
    "book_C_term_denote \<Sigma> G w" by (rule S.book_separated_to_environment)
  show ?thesis by unfold_locales
qed

theorem book_C_term_lambda_application:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed (book_C_identity_domain \<Sigma> G w) G g"
    and member: "a \<in> book_C_identity_domain \<Sigma> G w (G n)"
  shows "book_C_term_app \<Sigma> G w (G n) \<tau> (book_C_term_denote \<Sigma> G w g (NLam n A)) a =
    book_C_term_denote \<Sigma> G w (g(n := a)) A"
proof -
  interpret E: book_full_environment "book_C_identity_domain \<Sigma> G w"
    "book_C_term_app \<Sigma> G w" book_minimal_logical_type UNIV \<Sigma> G
    "book_C_term_denote \<Sigma> G w" by (rule book_C_term_full_environment)
  show ?thesis by (rule E.book_full_lambda_application[OF language typed member])
qed

end

context book_full_C_canonical_frame
begin

theorem full_term_environment:
  assumes ww: "w \<in> worlds"
  shows "book_full_environment (book_C_identity_domain (fst w) G (snd w))
    (book_C_term_app (fst w) G (snd w)) book_minimal_logical_type UNIV (fst w) G
    (book_C_term_denote (fst w) G (snd w))"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  show ?thesis by (rule T.book_C_term_full_environment)
qed

end

text \<open>
  The constructed Jᵂ satisfies Definition 14.13's exact intersection
  condition, not merely same-assignment conversion. The abstraction
  equation follows from the proved full-environment theorem. Every
  actual full-C world instantiates it. This is not yet the future
  abstraction equation on the represented modal domains or a truth
  theorem: these require counterpart naturality and the logical clauses.
\<close>

end
