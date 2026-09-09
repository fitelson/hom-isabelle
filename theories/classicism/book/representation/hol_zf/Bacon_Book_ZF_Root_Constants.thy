theory Bacon_Book_ZF_Root_Constants
  imports Bacon_Book_ZF_Reindexed_Identity_Operator
begin

context book_full_C_canonical_frame
begin

definition full_ZF_constant_value where
  "full_ZF_constant_value c \<sigma> = full_ZF_closed_value actual \<sigma> (NConst c \<sigma>)"

lemma full_ZF_original_constant_closed:
  assumes declared: "c \<in> \<Sigma> \<sigma>"
  shows "NConst c \<sigma> \<in> book_closed_terms (fst actual) G \<sigma>"
proof -
  have inclusion: "\<Sigma> \<sigma> \<subseteq> fst actual \<sigma>"
    by (rule book_full_C_canonical_world_data(1)[OF book_full_C_rooted_world_data(1)[OF book_full_C_root_is_world]])
  have member: "c \<in> fst actual \<sigma>" using inclusion declared by blast
  have language: "book_in_language book_minimal_logical_type UNIV (fst actual) G (NConst c \<sigma>) \<sigma>"
    by (simp only: book_language_const_iff; use member in simp)
  show ?thesis by (rule book_closed_termsI[OF language]; simp)
qed

theorem full_ZF_constant_value_type:
  "c \<in> \<Sigma> \<sigma> \<Longrightarrow> full_ZF_constant_value c \<sigma> \<in> explode (full_ZF_D_at \<sigma> full_ZF_root)"
  by (simp only: full_ZF_D_at_root full_ZF_constant_value_def;
    rule full_ZF_closed_value_type[OF full_ZF_original_constant_closed]; assumption)

theorem full_ZF_original_constant_denote:
  assumes ww: "w \<in> worlds" and declared: "c \<in> \<Sigma> \<sigma>"
  shows "full_ZF_denote w g (NConst c \<sigma>) = full_ZF_i \<sigma> actual w (full_ZF_constant_value c \<sigma>)"
proof -
  have old: "NConst c \<sigma> \<in> book_closed_terms (fst actual) G \<sigma>" by (rule full_ZF_original_constant_closed[OF declared])
  have access: "le actual w" by (rule book_full_C_rooted_world_data(2)[OF ww])
  have future: "NConst c \<sigma> \<in> book_closed_terms (fst w) G \<sigma>"
    by (rule book_full_C_closed_terms_future[OF rich book_full_C_rooted_world_data(1)[OF book_full_C_root_is_world]
      book_full_C_rooted_world_data(1)[OF ww] access old])
  show ?thesis by (simp only: full_ZF_denote_closed_value[OF future] full_ZF_constant_value_def
    full_ZF_closed_value_natural[OF book_full_C_root_is_world ww access old])
qed

end

text \<open>
  Only constants declared in the original signature receive a claimed
  typed root interpretation. Original names are available at the
  canonical root and persist into each future language. Their actual
  denotations are the counterparts of those root values, as required
  by Definition 17.13; no future-only name is falsely treated as an
  original root constant.
\<close>

end
