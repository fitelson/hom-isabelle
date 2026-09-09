theory Bacon_Book_ZF_Original_Theory_Truth
  imports Bacon_Book_ZF_Canonical_Interpretation
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Model_Truth
    Bacon_Book_Environment_Development.Bacon_Book_Universal_Closure_Truth
begin

context book_full_C_canonical_frame
begin

lemma full_ZF_root_validity_bridge:
  "book_ZF_formula_valid full_ZF_D_at G full_ZF_J full_ZF_root A =
    book_formula_valid (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> actual)) G (full_ZF_denote actual) (full_ZF_value_truth actual) A"
  by (simp only: book_ZF_formula_valid_def book_ZF_truth_at_def book_formula_valid_def full_ZF_root_def
    full_ZF_D_at_code[OF book_full_C_root_is_world] full_ZF_J_code[OF book_full_C_root_is_world] full_ZF_value_truth_def)

theorem full_ZF_universal_closure_truth:
  assumes language: "book_theory_formula \<Sigma> G A"
    and contained: "book_universal_closure G A \<in> snd actual"
  shows "book_ZF_formula_valid full_ZF_D_at G full_ZF_J full_ZF_root A"
proof -
  let ?D = "\<lambda>\<sigma>. explode (full_ZF_D \<sigma> actual)"
  let ?J = "full_ZF_denote actual"
  let ?V = "full_ZF_value_truth actual"
  interpret M: book_full_minimal_model ?D "full_ZF_app actual" "fst actual" G ?J ?V "full_ZF_logical_value actual"
    by (rule full_ZF_general_model[OF book_full_C_root_is_world])
  have al: "book_theory_formula (fst actual) G A"
    using full_ZF_original_language_at[OF full_ZF_root_member language]
    by (simp only: full_ZF_root_def full_world_decode_code[OF book_full_C_root_is_world])
  have uc: "book_universal_closure G A \<in> book_closed_terms (fst actual) G Prop"
    by (rule book_closed_termsI[OF book_universal_closure_language[OF al] book_universal_closure_closed])
  have valid_closure: "book_formula_valid ?D G ?J ?V (book_universal_closure G A)"
  proof (rule book_formula_validI)
    fix g
    assume "book_env_typed ?D G g"
    show "?V (?J g (book_universal_closure G A))"
      by (simp only: full_ZF_closed_sentence_truth[OF book_full_C_root_is_world uc]; rule contained)
  qed
  have valid: "book_formula_valid ?D G ?J ?V A"
    using valid_closure by (simp only: M.book_formula_valid_universal_closure_iff[OF al])
  show ?thesis by (simp only: full_ZF_root_validity_bridge; rule valid)
qed

theorem full_ZF_original_theory_satisfied:
  assumes language: "\<And>A. A \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and contained: "\<And>A. A \<in> T \<Longrightarrow> book_universal_closure G A \<in> snd actual"
  shows "book_ZF_satisfies full_ZF_D_at G full_ZF_J full_ZF_root T"
  unfolding book_ZF_satisfies_def
  by (intro ballI; rule full_ZF_universal_closure_truth[OF language contained]; assumption)

theorem full_ZF_original_theory_all_interpretations:
  assumes other: "book_ZF_modal_interpretation full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
      \<Sigma> full_ZF_constant_value G K"
    and language: "\<And>A. A \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and contained: "\<And>A. A \<in> T \<Longrightarrow> book_universal_closure G A \<in> snd actual"
  shows "book_ZF_satisfies full_ZF_D_at G K full_ZF_root T"
proof -
  interpret C: book_ZF_modal_interpretation full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    \<Sigma> full_ZF_constant_value G full_ZF_J by (rule full_ZF_canonical_interpretation)
  have canonical: "book_ZF_satisfies full_ZF_D_at G full_ZF_J full_ZF_root T"
    by (rule full_ZF_original_theory_satisfied[OF language contained])
  show ?thesis using canonical by (simp only: C.satisfaction_independent[OF other language])
qed

end

text \<open>
  Proposition 18.6's truth step: if the canonical root contains the
  universal closure of every original premise, the constructed
  independent interpretation satisfies all those premises under
  every typed assignment. Premises may be open and the set may be
  infinite; there is no common free-variable bound. Every other
  admissible interpretation of this same model agrees.

  The root-containment premise is explicit. Constructing the required
  root from an arbitrary consistent original theory, including any
  needed name/signature transport, is the final existence assembly,
  not an assumption erased by this truth theorem.
\<close>

end
