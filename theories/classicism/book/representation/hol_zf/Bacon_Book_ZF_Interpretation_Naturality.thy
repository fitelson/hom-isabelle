theory Bacon_Book_ZF_Interpretation_Naturality
  imports Bacon_Book_ZF_Term_Interpretation
begin

context book_full_C_coded_frame
begin

theorem full_ZF_denote_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and language: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_i \<tau> w v (full_ZF_denote w g A) =
    full_ZF_denote v (full_ZF_assignment_move w v g) A"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  let ?k = "full_ZF_assignment_decode w g"
  let ?J = "book_C_term_denote (fst w) G (snd w)"
  have kt: "book_env_typed (book_C_identity_domain (fst w) G (snd w)) G ?k"
    by (rule full_ZF_assignment_decode_typed[OF worlds_admitted[OF ww] typed])
  have member: "?J ?k A \<in> book_C_identity_domain (fst w) G (snd w) \<tau>"
    by (rule T.book_C_term_denote_type[OF language kt])
  have natural: "book_C_term_counterpart G w v \<tau> (?J ?k A) =
    book_C_term_denote (fst v) G (snd v) (full_term_assignment_move w v ?k) A"
    by (rule full_term_denote_natural[OF ww vw access language kt])
  show ?thesis by (simp only: full_ZF_denote_eq[OF book_language_type[OF language]]
    full_ZF_h_natural[OF ww member, symmetric] natural full_ZF_assignment_decode_move[OF ww vw access typed])
qed

theorem full_ZF_denote_conversion:
  assumes ww: "w \<in> worlds"
    and al: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and bl: "book_in_language book_minimal_logical_type UNIV (fst w) G C \<tau>"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A C"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_denote w g A = full_ZF_denote w g C"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  have same: "book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) A =
    book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) C"
    by (rule T.book_C_term_denote_conversion[OF al bl conversion full_ZF_assignment_decode_typed[OF worlds_admitted[OF ww] typed]])
  show ?thesis by (simp only: full_ZF_denote_eq[OF book_language_type[OF al]]
    full_ZF_denote_eq[OF book_language_type[OF bl]] same)
qed

end

text \<open>
  The represented interpretation commutes with the actual counterparts
  and respects raw typed βη conversion. These conclusions use the
  constructed term interpretation and the proved all-type inverse
  family, not assumed model naturality or an assumed conversion clause.
\<close>

end
