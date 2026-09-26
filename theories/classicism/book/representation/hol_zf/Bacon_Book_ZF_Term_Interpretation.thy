theory Bacon_Book_ZF_Term_Interpretation
  imports Bacon_Book_ZF_Interpretation_Assignments
begin

section \<open>The actual interpretation on the represented domains\<close>

context book_full_C_coded_frame
begin

definition full_ZF_denote where
  "full_ZF_denote w g A = full_ZF_h (book_conversion_result_type G A) w
    (book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) A)"

lemma full_ZF_denote_eq:
  "has_ntype book_minimal_logical_type G A \<tau> \<Longrightarrow>
    full_ZF_denote w g A = full_ZF_h \<tau> w
      (book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) A)"
  by (simp only: full_ZF_denote_def book_conversion_result_type_eq)

theorem full_ZF_denote_type:
  assumes ww: "w \<in> worlds"
    and language: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_denote w g A \<in> explode (full_ZF_D \<tau> w)"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  have source: "book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) A \<in>
    book_C_identity_domain (fst w) G (snd w) \<tau>"
    by (rule T.book_C_term_denote_type[OF language full_ZF_assignment_decode_typed[OF worlds_admitted[OF ww] typed]])
  show ?thesis by (simp only: full_ZF_denote_eq[OF book_language_type[OF language]]; rule full_ZF_h_type[OF worlds_admitted[OF ww] source])
qed

theorem full_ZF_denote_var:
  assumes ww: "w \<in> worlds"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_denote w g (NVar n) = g n"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  have nt: "has_ntype book_minimal_logical_type G (NVar n) (G n)" by (rule has_ntype.Var)
  have decoded: "book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) (NVar n) =
    full_ZF_j (G n) w (g n)"
    using T.book_C_term_denote_var[OF full_ZF_assignment_decode_typed[OF worlds_admitted[OF ww] typed], of n]
    by (simp only: full_ZF_assignment_decode_def)
  show ?thesis by (simp only: full_ZF_denote_eq[OF nt] decoded; rule full_ZF_hj[OF worlds_admitted[OF ww]]; rule book_env_at[OF typed])
qed

theorem full_ZF_denote_closed:
  assumes language: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and closed: "named_fv A = {}"
  shows "full_ZF_denote w g A =
    full_ZF_h \<tau> w (book_C_identity_class (fst w) G (snd w) \<tau> A)"
  by (simp only: full_ZF_denote_eq[OF book_language_type[OF language]]
    book_C_term_denote_eq[OF book_language_type[OF language]] book_environment_subst_closed_fixed[OF closed])

theorem full_ZF_denote_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
  shows "full_ZF_denote w g A = full_ZF_denote w k A"
proof -
  have same: "book_environment_subst {} (book_C_term_representatives (full_ZF_assignment_decode w g)) A =
    book_environment_subst {} (book_C_term_representatives (full_ZF_assignment_decode w k)) A"
    by (rule book_environment_subst_locality; simp add: book_C_term_representatives_def full_ZF_assignment_decode_def agree)
  show ?thesis by (simp only: full_ZF_denote_def book_C_term_denote_def same)
qed

theorem full_ZF_denote_app:
  assumes ww: "w \<in> worlds"
    and fl: "book_in_language book_minimal_logical_type UNIV (fst w) G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<sigma>"
    and typed: "book_env_typed (\<lambda>\<rho>. explode (full_ZF_D \<rho> w)) G g"
  shows "full_ZF_denote w g (NApp F A) =
    app (full_ZF_denote w g F) (Opair (book_ZF_world_code w) (full_ZF_denote w g A))"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  let ?k = "full_ZF_assignment_decode w g"
  let ?J = "book_C_term_denote (fst w) G (snd w) ?k"
  have kt: "book_env_typed (book_C_identity_domain (fst w) G (snd w)) G ?k"
    by (rule full_ZF_assignment_decode_typed[OF worlds_admitted[OF ww] typed])
  have fm: "?J F \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    by (rule T.book_C_term_denote_type[OF fl kt])
  have am: "?J A \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
    by (rule T.book_C_term_denote_type[OF al kt])
  show ?thesis by (simp only: full_ZF_denote_eq[OF book_language_type[OF book_language_App[OF fl al]]]
    full_ZF_denote_eq[OF book_language_type[OF fl]] full_ZF_denote_eq[OF book_language_type[OF al]]
    T.book_C_term_denote_app[OF fl al kt] full_ZF_application_preserved[OF ww am fm])
qed

end

text \<open>
  Define the represented interpretation by hᵂ(Jᵂ_{jᵂg}(A)).
  Typing, variables, closed terms, application and locality are proved
  for this one actual definition. Application uses the actual graph
  at the pair (w,a). Type selection is purely syntactic and is
  eliminated under every well-typed statement. Future naturality and
  abstraction, conversion, and the primitive truth clauses remain
  distinct obligations; no model condition is assumed here.
\<close>

end
