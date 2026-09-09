theory Bacon_Book_ZF_Reindexed_Frame
  imports Bacon_Book_ZF_S_Future_Value
    Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Model_Operator_Restriction
begin

context book_full_C_canonical_frame
begin

definition full_ZF_R where "full_ZF_R w v = le (full_world_decode w) (full_world_decode v)"
definition full_ZF_D_at where "full_ZF_D_at \<sigma> w = full_ZF_D \<sigma> (full_world_decode w)"
definition full_ZF_i_at where "full_ZF_i_at \<sigma> w v a = full_ZF_i \<sigma> (full_world_decode w) (full_world_decode v) a"
definition full_ZF_root where "full_ZF_root = book_ZF_world_code actual"

lemma full_ZF_R_function:
  "full_ZF_R z = (\<lambda>v. le (full_world_decode z) (full_world_decode v))"
  by (rule ext; simp only: full_ZF_R_def)

lemma full_ZF_D_at_function:
  "full_ZF_D_at \<sigma> = (\<lambda>z. full_ZF_D \<sigma> (full_world_decode z))"
  by (rule ext; simp only: full_ZF_D_at_def)

lemma full_ZF_R_code:
  "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> full_ZF_R (book_ZF_world_code w) (book_ZF_world_code v) = le w v"
  by (simp only: full_ZF_R_def full_world_decode_code)

lemma full_ZF_D_at_code:
  "w \<in> worlds \<Longrightarrow> full_ZF_D_at \<sigma> (book_ZF_world_code w) = full_ZF_D \<sigma> w"
  by (simp only: full_ZF_D_at_def full_world_decode_code)

lemma full_ZF_i_at_code:
  "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow>
    full_ZF_i_at \<sigma> (book_ZF_world_code w) (book_ZF_world_code v) a = full_ZF_i \<sigma> w v a"
  by (simp only: full_ZF_i_at_def full_world_decode_code)

theorem full_ZF_reindexed_frame:
  "book_ZF_frame full_world_set full_ZF_R full_ZF_root"
proof unfold_locales
  show "\<And>w. w \<in> explode full_world_set \<Longrightarrow> full_ZF_R w w"
    unfolding full_ZF_R_def by (rule book_full_C_rooted_refl[OF full_world_decode_type]; assumption)
  show "\<And>w v u. w \<in> explode full_world_set \<Longrightarrow> v \<in> explode full_world_set \<Longrightarrow> u \<in> explode full_world_set \<Longrightarrow>
    full_ZF_R w v \<Longrightarrow> full_ZF_R v u \<Longrightarrow> full_ZF_R w u"
    unfolding full_ZF_R_def by (rule book_full_C_rooted_trans[OF full_world_decode_type]; assumption)
  show "full_ZF_root \<in> explode full_world_set"
    by (simp only: full_ZF_root_def full_world_set_elements; rule imageI[OF book_full_C_root_is_world])
  show "\<And>w. w \<in> explode full_world_set \<Longrightarrow> full_ZF_R full_ZF_root w"
    by (simp only: full_ZF_root_def full_ZF_R_def full_world_decode_code[OF book_full_C_root_is_world];
      rule book_full_C_rooted_world_data(2)[OF full_world_decode_type]; assumption)
qed

theorem full_ZF_reindexed_domains:
  "book_modalized_set (explode full_world_set) full_ZF_R (\<lambda>w. explode (full_ZF_D_at \<sigma> w)) (full_ZF_i_at \<sigma>)"
proof -
  interpret Frame: book_ZF_frame full_world_set full_ZF_R full_ZF_root by (rule full_ZF_reindexed_frame)
  show ?thesis
  proof unfold_locales
    show "\<And>w v a. w \<in> explode full_world_set \<Longrightarrow> v \<in> explode full_world_set \<Longrightarrow> full_ZF_R w v \<Longrightarrow>
      a \<in> explode (full_ZF_D_at \<sigma> w) \<Longrightarrow> full_ZF_i_at \<sigma> w v a \<in> explode (full_ZF_D_at \<sigma> v)"
      unfolding full_ZF_R_def full_ZF_D_at_def full_ZF_i_at_def
      by (rule full_ZF_i_type[OF full_world_decode_type full_world_decode_type]; assumption)
    show "\<And>w a. w \<in> explode full_world_set \<Longrightarrow> a \<in> explode (full_ZF_D_at \<sigma> w) \<Longrightarrow> full_ZF_i_at \<sigma> w w a = a"
      unfolding full_ZF_D_at_def full_ZF_i_at_def by (rule full_ZF_i_identity[OF full_world_decode_type]; assumption)
    show "\<And>w v u a. w \<in> explode full_world_set \<Longrightarrow> v \<in> explode full_world_set \<Longrightarrow> u \<in> explode full_world_set \<Longrightarrow>
      full_ZF_R w v \<Longrightarrow> full_ZF_R v u \<Longrightarrow> a \<in> explode (full_ZF_D_at \<sigma> w) \<Longrightarrow>
      full_ZF_i_at \<sigma> w u a = full_ZF_i_at \<sigma> v u (full_ZF_i_at \<sigma> w v a)"
      unfolding full_ZF_R_def full_ZF_D_at_def full_ZF_i_at_def
      by (rule full_ZF_i_composition[OF full_world_decode_type full_world_decode_type full_world_decode_type]; assumption)
  qed
qed

lemma full_ZF_reindexed_future:
  "book_ZF_future full_world_set full_ZF_R z = full_ZF_future (full_world_decode z)"
  by (simp only: book_ZF_future_def full_ZF_R_function full_ZF_future_def)

lemma full_ZF_reindexed_pairs:
  "book_ZF_pairs full_world_set full_ZF_R (full_ZF_D_at \<sigma>) z =
    full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) (full_world_decode z)"
  by (simp only: book_ZF_pairs_def full_ZF_reindexed_future full_ZF_D_at_function full_ZF_D_def full_ZF_future_pairs_def)

lemma full_ZF_reindexed_restriction:
  "book_ZF_restrict full_world_set full_ZF_R (full_ZF_D_at \<sigma>) z F =
    full_ZF_arrow_restrict \<sigma> (full_world_decode z) F"
  by (simp only: book_ZF_restrict_def full_ZF_reindexed_pairs full_ZF_arrow_restrict_def)

end

text \<open>
  Only worlds are reindexed: each represented value remains the same
  ZF object. The actual world-code bijection gives the independent
  pointed frame and all modalized domains. Its future and pair sets
  are exactly the ones already used in the recursion, and its graph
  restriction is exactly the proved canonical restriction. No new
  transport or representability condition is assumed.
\<close>

end
