theory Bacon_Book_ZF_Canonical_Interpretation
  imports Bacon_Book_ZF_Canonical_Evaluation
begin

context book_full_C_coded_frame
begin

theorem full_ZF_J_abstraction:
  assumes ww: "w \<in> explode full_world_set"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D_at \<sigma> w)) G g"
  shows "full_ZF_J w g (NLam n A) =
    Lambda (book_ZF_pairs full_world_set full_ZF_R (full_ZF_D_at (G n)) w)
      (\<lambda>p. full_ZF_J (Fst p) ((book_ZF_move full_ZF_i_at G w (Fst p) g)(n := Snd p)) A)"
proof -
  interpret S: book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    by (rule full_ZF_reindexed_structure)
  have ft: "full_ZF_J w g (NLam n A) \<in> explode (full_ZF_D_at (Arr (G n) \<tau>) w)"
    by (rule full_ZF_J_type[OF ww book_language_Lam[OF language] typed])
  show ?thesis
  proof (rule S.function_as_lambda[OF ww ft])
    fix v a
    assume vw: "v \<in> explode full_world_set" and access: "full_ZF_R w v"
      and am: "a \<in> explode (full_ZF_D_at (G n) v)"
    have behavior: "app (full_ZF_J w g (NLam n A)) (Opair v a) =
      full_ZF_J v ((book_ZF_move full_ZF_i_at G w v g)(n := a)) A"
      using full_ZF_denote_lambda_future[OF full_world_decode_type[OF ww] full_world_decode_type[OF vw]
        access[unfolded full_ZF_R_def] full_ZF_original_language_at[OF ww language]
        typed[unfolded full_ZF_D_at_def] am[unfolded full_ZF_D_at_def]]
      by (simp only: full_ZF_J_def full_world_code_decode[OF vw] full_ZF_move_reindex)
    show "app (full_ZF_J w g (NLam n A)) (Opair v a) =
      full_ZF_J (Fst (Opair v a)) ((book_ZF_move full_ZF_i_at G w (Fst (Opair v a)) g)(n := Snd (Opair v a))) A"
      by (simp only: Fst Snd; rule behavior)
  qed
qed

theorem full_ZF_canonical_interpretation:
  "book_ZF_modal_interpretation full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    \<Sigma> full_ZF_constant_value G full_ZF_J"
  by (rule book_ZF_modal_interpretation.intro[OF full_ZF_canonical_modal_model];
    rule book_ZF_modal_interpretation_axioms.intro;
    (rule full_ZF_J_type | rule full_ZF_J_variable | rule full_ZF_J_constant |
      rule full_ZF_J_logical | rule full_ZF_J_application | rule full_ZF_J_abstraction); assumption?)

theorem full_ZF_canonical_interpretation_unique:
  assumes other: "book_ZF_modal_interpretation full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
      \<Sigma> full_ZF_constant_value G K"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and ww: "w \<in> explode full_world_set"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D_at \<sigma> w)) G g"
  shows "K w g A = full_ZF_J w g A"
proof -
  interpret C: book_ZF_modal_interpretation full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    \<Sigma> full_ZF_constant_value G full_ZF_J by (rule full_ZF_canonical_interpretation)
  show ?thesis by (rule C.interpretation_unique[OF other language ww typed, symmetric])
qed

end

text \<open>
  The already constructed canonical interpretation instantiates
  every independent Definition 17.13 clause over the original
  signature, including equality with the entire future Lambda graph.
  It is unique on typed terms and assignments among all interpretations
  of this model satisfying those clauses. This proves canonical
  existence and uniqueness, not existence for every arbitrary model.
\<close>

end
