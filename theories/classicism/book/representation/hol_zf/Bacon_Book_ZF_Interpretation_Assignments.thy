theory Bacon_Book_ZF_Interpretation_Assignments
  imports Bacon_Book_ZF_Arrow_Homomorphisms
    Bacon_Book_Modal_Representation.Bacon_Book_Term_Interpretation_Naturality
begin

context book_full_C_canonical_frame
begin

definition full_ZF_assignment_decode where
  "full_ZF_assignment_decode w g = (\<lambda>n. full_ZF_j (G n) w (g n))"

definition full_ZF_assignment_move where
  "full_ZF_assignment_move w v g = (\<lambda>n. full_ZF_i (G n) w v (g n))"

theorem full_ZF_assignment_decode_typed:
  assumes typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "book_env_typed (book_C_identity_domain (fst w) G (snd w)) G (full_ZF_assignment_decode w g)"
  unfolding book_env_typed_def full_ZF_assignment_decode_def
  by (intro allI; rule full_ZF_j_type[OF book_env_at[OF typed]])

theorem full_ZF_assignment_move_typed:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> v)) G (full_ZF_assignment_move w v g)"
  unfolding book_env_typed_def full_ZF_assignment_move_def
  by (intro allI; rule full_ZF_i_type[OF ww vw access book_env_at[OF typed]])

theorem full_ZF_assignment_decode_move:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_assignment_decode v (full_ZF_assignment_move w v g) =
    full_term_assignment_move w v (full_ZF_assignment_decode w g)"
  by (rule ext; simp only: full_ZF_assignment_decode_def full_ZF_assignment_move_def
    full_term_assignment_move_def full_ZF_j_natural[OF ww vw access book_env_at[OF typed]])

lemma full_ZF_assignment_decode_update:
  "full_ZF_assignment_decode w (g(n := a)) = (full_ZF_assignment_decode w g)(n := full_ZF_j (G n) w a)"
  by (rule ext; simp add: full_ZF_assignment_decode_def)

end

text \<open>
  Decode an assignment at each variable's own type. The inverse maps
  give a typed assignment in the term structure; future transport
  commutes with decoding. The update equation changes only the chosen
  variable and keeps its fixed G-type. These are actual maps, with
  their typing proved on the recursively constructed domains.
\<close>

end
