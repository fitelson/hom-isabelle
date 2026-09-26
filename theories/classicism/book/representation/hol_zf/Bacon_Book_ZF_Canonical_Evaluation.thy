theory Bacon_Book_ZF_Canonical_Evaluation
  imports Bacon_Book_ZF_Canonical_Modal_Model
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Model_Interpretation_Uniqueness
begin

context book_full_C_coded_frame
begin

definition full_ZF_J where "full_ZF_J w g A = full_ZF_denote (full_world_decode w) g A"

lemma full_ZF_J_code:
  "w \<in> worlds \<Longrightarrow> full_ZF_J (book_ZF_world_code w) g A = full_ZF_denote w g A"
  by (simp only: full_ZF_J_def full_world_decode_code)

lemma full_ZF_original_language_at:
  assumes ww: "w \<in> explode full_world_set"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
  shows "book_in_language book_minimal_logical_type UNIV (fst (full_world_decode w)) G A \<tau>"
proof -
  have inclusion: "\<And>\<sigma>. \<Sigma> \<sigma> \<subseteq> fst (full_world_decode w) \<sigma>"
    by (rule book_full_C_canonical_world_data(1)[OF book_full_C_rooted_world_data(1)[OF full_world_decode_type[OF ww]]])
  show ?thesis by (rule book_language_signature_mono[OF language inclusion])
qed

lemma full_ZF_move_reindex:
  "book_ZF_move full_ZF_i_at G w v g = full_ZF_assignment_move (full_world_decode w) (full_world_decode v) g"
  by (rule ext; simp only: book_ZF_move_def full_ZF_i_at_def full_ZF_assignment_move_def)

theorem full_ZF_J_type:
  assumes ww: "w \<in> explode full_world_set"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D_at \<sigma> w)) G g"
  shows "full_ZF_J w g A \<in> explode (full_ZF_D_at \<tau> w)"
  unfolding full_ZF_J_def full_ZF_D_at_def
  by (rule full_ZF_denote_type[OF full_world_decode_type[OF ww] full_ZF_original_language_at[OF ww language]
    typed[unfolded full_ZF_D_at_def]])

theorem full_ZF_J_variable:
  assumes ww: "w \<in> explode full_world_set"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D_at \<sigma> w)) G g"
  shows "full_ZF_J w g (NVar n) = g n"
  unfolding full_ZF_J_def by (rule full_ZF_denote_var[OF full_world_decode_type[OF ww] typed[unfolded full_ZF_D_at_def]])

theorem full_ZF_J_constant:
  assumes ww: "w \<in> explode full_world_set" and declared: "c \<in> \<Sigma> \<sigma>"
  shows "full_ZF_J w g (NConst c \<sigma>) = full_ZF_i_at \<sigma> full_ZF_root w (full_ZF_constant_value c \<sigma>)"
  by (simp only: full_ZF_J_def full_ZF_i_at_def full_ZF_root_def full_world_decode_code[OF book_full_C_root_is_world];
    rule full_ZF_original_constant_denote[OF full_world_decode_type[OF ww] declared])

theorem full_ZF_J_logical:
  assumes ww: "w \<in> explode full_world_set"
  shows "full_ZF_J w g (NLogical l) = full_ZF_i_at (book_minimal_logical_type l) full_ZF_root w
    (book_ZF_logical_root full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root l)"
proof -
  have decoded: "full_world_decode w \<in> worlds" by (rule full_world_decode_type[OF ww])
  have access: "le actual (full_world_decode w)" by (rule book_full_C_rooted_world_data(2)[OF decoded])
  show ?thesis by (subst full_ZF_logical_root_identification[symmetric]; simp only: full_ZF_J_def full_ZF_logical_denote full_ZF_i_at_def
    full_ZF_root_def full_world_decode_code[OF book_full_C_root_is_world]
    full_ZF_logical_value_natural[OF book_full_C_root_is_world decoded access])
qed

theorem full_ZF_J_application:
  assumes ww: "w \<in> explode full_world_set"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and typed: "book_env_typed (\<lambda>\<rho>. explode (full_ZF_D_at \<rho> w)) G g"
  shows "full_ZF_J w g (NApp F A) = app (full_ZF_J w g F) (Opair w (full_ZF_J w g A))"
  using full_ZF_denote_app[OF full_world_decode_type[OF ww] full_ZF_original_language_at[OF ww fl]
    full_ZF_original_language_at[OF ww al] typed[unfolded full_ZF_D_at_def]]
  by (simp only: full_ZF_J_def full_world_code_decode[OF ww])

end

text \<open>
  The canonical evaluation is reindexed into the independent world's
  actual ZF set, with the original signature retained. Every original
  expression belongs to each relevant future language; values and
  variable assignments themselves are unchanged. Root constants,
  primitive logical values and graph application satisfy the
  independent clauses without an interpretation premise.
\<close>

end
