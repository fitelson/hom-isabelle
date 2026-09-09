theory Bacon_Book_Term_Interpretation_Naturality
  imports Bacon_Book_Representative_Independence
begin

section \<open>The canonical interpretation commutes with counterparts\<close>

context book_full_C_canonical_frame
begin

definition full_term_assignment_move where
  "full_term_assignment_move w v g = (\<lambda>n. book_C_term_counterpart G w v (G n) (g n))"

theorem full_term_assignment_move_typed:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and typed: "book_env_typed (book_C_identity_domain (fst w) G (snd w)) G g"
  shows "book_env_typed (book_C_identity_domain (fst v) G (snd v)) G (full_term_assignment_move w v g)"
proof (unfold book_env_typed_def, intro allI)
  fix n
  show "full_term_assignment_move w v g n \<in> book_C_identity_domain (fst v) G (snd v) (G n)"
    unfolding full_term_assignment_move_def
    by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF ww]
      full_rooted_base_world[OF vw] access book_env_at[OF typed]])
qed

theorem full_term_denote_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and language: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and typed: "book_env_typed (book_C_identity_domain (fst w) G (snd w)) G g"
  shows "book_C_term_counterpart G w v \<tau> (book_C_term_denote (fst w) G (snd w) g A) =
    book_C_term_denote (fst v) G (snd v) (full_term_assignment_move w v g) A"
proof -
  have wf: "w \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF ww])
  have vf: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF vw])
  interpret W: book_C_identity_world "fst w" G "snd w" by (rule book_full_C_world_identity_algebra[OF rich wf])
  interpret V: book_C_identity_world "fst v" G "snd v" by (rule book_full_C_world_identity_algebra[OF rich vf])
  let ?r = "book_C_term_representatives g"
  let ?k = "full_term_assignment_move w v g"
  have inclusion: "\<And>\<sigma>. fst w \<sigma> \<subseteq> fst v \<sigma>"
    by (rule book_C_canonical_le_language[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access])
  have target_language: "book_in_language book_minimal_logical_type UNIV (fst v) G A \<tau>"
    by (rule book_language_signature_mono[OF language inclusion])
  have target_typed: "book_env_typed (book_C_identity_domain (fst v) G (snd v)) G ?k"
    by (rule full_term_assignment_move_typed[OF ww vw access typed])
  have old_reps: "\<And>n. ?r n \<in> book_closed_terms (fst w) G (G n)"
    by (rule W.book_C_term_representatives_closed_terms[OF typed])
  have new_reps: "\<And>n. ?r n \<in> book_closed_terms (fst v) G (G n)"
    by (rule book_full_C_closed_terms_future[OF rich wf vf access old_reps])
  have represents: "\<And>n. n \<in> named_fv A \<Longrightarrow>
    book_C_identity_class (fst v) G (snd v) (G n) (?r n) = ?k n"
  proof -
    fix n
    assume "n \<in> named_fv A"
    have old_class: "book_C_identity_class (fst w) G (snd w) (G n) (?r n) = g n"
      by (simp only: book_C_term_representatives_def; rule W.identity_rep_class[OF book_env_at[OF typed]])
    show "book_C_identity_class (fst v) G (snd v) (G n) (?r n) = ?k n"
      unfolding full_term_assignment_move_def
      using book_full_C_term_counterpart_class[OF rich wf vf access old_reps[of n]]
      by (simp only: old_class)
  qed
  have at_target: "book_C_term_denote (fst v) G (snd v) ?k A =
    book_C_identity_class (fst v) G (snd v) \<tau> (book_environment_subst {} ?r A)"
    by (rule V.book_C_term_denote_any_representatives[OF target_language target_typed new_reps represents])
  have closed_instance: "book_environment_subst {} ?r A \<in> book_closed_terms (fst w) G \<tau>"
    by (rule W.book_C_term_substituted_closed_terms[OF language typed])
  show ?thesis by (subst at_target; simp only: book_C_term_denote_eq[OF book_language_type[OF language]]
    book_full_C_term_counterpart_class[OF rich wf vf access closed_instance])
qed

end

text \<open>
  Old representatives remain closed terms in every accessible language.
  Their new classes are exactly the counterparts of the old assigned
  values. Representative independence lets us use those old terms
  instead of the new world's chosen representatives. Consequently
  iᵂᵛ(Jᵂ_g(A)) = Jᵛ_{iᵂᵛg}(A), with no injectivity assumption on
  counterparts. This is the canonical naturality needed to interpret
  abstraction as a function on all future worlds.
\<close>

end
