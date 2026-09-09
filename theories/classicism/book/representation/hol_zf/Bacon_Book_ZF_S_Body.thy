theory Bacon_Book_ZF_S_Body
  imports Bacon_Book_ZF_K_Value
begin

context book_full_C_canonical_frame
begin

definition full_ZF_S_value where
  "full_ZF_S_value w \<sigma> \<tau> \<rho> =
    full_ZF_closed_value w (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>)))
      (book_canonical_S G \<sigma> \<tau> \<rho>)"

theorem full_ZF_S_value_type:
  "full_ZF_S_value w \<sigma> \<tau> \<rho> \<in>
    explode (full_ZF_D (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) w)"
  unfolding full_ZF_S_value_def by (rule full_ZF_closed_value_type[OF book_canonical_S_closed_terms[OF rich]])

theorem full_ZF_S_value_natural:
  "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
    full_ZF_i (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) w v
      (full_ZF_S_value w \<sigma> \<tau> \<rho>) = full_ZF_S_value v \<sigma> \<tau> \<rho>"
  unfolding full_ZF_S_value_def
  by (rule full_ZF_closed_value_natural[OF _ _ _ book_canonical_S_closed_terms[OF rich]]; assumption)

theorem full_ZF_S_body_evaluation:
  assumes ww: "w \<in> worlds"
    and typed: "book_env_typed (\<lambda>\<delta>. explode (full_ZF_D \<delta> w)) G h"
  shows "full_ZF_denote w h (book_canonical_S_body G \<sigma> \<tau> \<rho>) =
    app (app (h (book_canonical_S_f G \<sigma> \<tau> \<rho>))
        (Opair (book_ZF_world_code w) (h (book_canonical_S_x G \<sigma> \<tau> \<rho>))))
      (Opair (book_ZF_world_code w)
        (app (h (book_canonical_S_g G \<sigma> \<tau> \<rho>))
          (Opair (book_ZF_world_code w) (h (book_canonical_S_x G \<sigma> \<tau> \<rho>)))))"
proof -
  let ?F = "NVar (book_canonical_S_f G \<sigma> \<tau> \<rho>)"
  let ?H = "NVar (book_canonical_S_g G \<sigma> \<tau> \<rho>)"
  let ?X = "NVar (book_canonical_S_x G \<sigma> \<tau> \<rho>)"
  have fl: "book_in_language book_minimal_logical_type UNIV (fst w) G ?F (Arr \<sigma> (Arr \<tau> \<rho>))"
    by (simp only: book_language_var_iff book_canonical_S_name_types[OF rich])
  have hl: "book_in_language book_minimal_logical_type UNIV (fst w) G ?H (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff book_canonical_S_name_types[OF rich])
  have xl: "book_in_language book_minimal_logical_type UNIV (fst w) G ?X \<sigma>"
    by (simp only: book_language_var_iff book_canonical_S_name_types[OF rich])
  have fal: "book_in_language book_minimal_logical_type UNIV (fst w) G (NApp ?F ?X) (Arr \<tau> \<rho>)"
    by (rule book_language_App[OF fl xl])
  have hal: "book_in_language book_minimal_logical_type UNIV (fst w) G (NApp ?H ?X) \<tau>"
    by (rule book_language_App[OF hl xl])
  show ?thesis by (simp only: book_canonical_S_body_def full_ZF_denote_app[OF ww fal hal typed]
    full_ZF_denote_app[OF ww fl xl typed] full_ZF_denote_app[OF ww hl xl typed] full_ZF_denote_var[OF ww typed])
qed

end

text \<open>
  The canonical closed s term has its full type and its domain
  membership without a model-membership assumption. The separate
  body calculation expands fx(gx) using actual graph application
  and variable interpretation at one typed assignment. Its three
  future arguments are handled in the next leaf.
\<close>

end
