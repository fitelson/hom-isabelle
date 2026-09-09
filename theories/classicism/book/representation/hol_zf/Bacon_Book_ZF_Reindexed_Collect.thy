theory Bacon_Book_ZF_Reindexed_Collect
  imports Bacon_Book_ZF_Reindexed_Structure
    Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Model_Curried_Graphs
begin

context book_full_C_canonical_frame
begin

lemma full_ZF_root_member:
  "full_ZF_root \<in> explode full_world_set"
  by (simp only: full_ZF_root_def full_world_set_elements; rule imageI[OF book_full_C_root_is_world])

lemma full_ZF_D_at_root:
  "full_ZF_D_at \<sigma> full_ZF_root = full_ZF_D \<sigma> actual"
  by (simp only: full_ZF_root_def full_ZF_D_at_code[OF book_full_C_root_is_world])

theorem full_ZF_collect_reindex:
  "book_ZF_collect full_world_set full_ZF_R z P =
    full_ZF_future_collect (full_world_decode z) (\<lambda>v. P (book_ZF_world_code v))"
proof (rule iffD2[OF Ext], intro allI)
  fix x
  show "Elem x (book_ZF_collect full_world_set full_ZF_R z P) =
    Elem x (full_ZF_future_collect (full_world_decode z) (\<lambda>v. P (book_ZF_world_code v)))"
  proof (cases "Elem x (full_ZF_future (full_world_decode z))")
    case True
    have member: "x \<in> explode (full_ZF_future (full_world_decode z))" using True by (simp only: explode_Elem)
    have code: "book_ZF_world_code (full_world_decode x) = x" by (rule full_ZF_future_member_data(3)[OF member])
    show ?thesis by (simp only: book_ZF_collect_def full_ZF_reindexed_future full_ZF_future_collect_def Sep code)
  next
    case False
    show ?thesis by (simp only: book_ZF_collect_def full_ZF_reindexed_future full_ZF_future_collect_def Sep False simp_thms)
  qed
qed

lemma full_ZF_future_collect_cong:
  assumes agree: "\<And>v. v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow> P v = Q v"
  shows "full_ZF_future_collect w P = full_ZF_future_collect w Q"
proof (rule full_ZF_future_set_extensional[OF full_ZF_future_collect_subset full_ZF_future_collect_subset])
  fix v
  assume vw: "v \<in> worlds" and access: "le w v"
  show "Elem (book_ZF_world_code v) (full_ZF_future_collect w P) =
    Elem (book_ZF_world_code v) (full_ZF_future_collect w Q)"
    by (simp only: full_ZF_future_collect_member[OF vw] agree[OF vw access])
qed

theorem full_ZF_collect_compatible:
  assumes agree: "\<And>v. v \<in> worlds \<Longrightarrow> P (book_ZF_world_code v) = Q v"
  shows "book_ZF_collect full_world_set full_ZF_R z P = full_ZF_future_collect (full_world_decode z) Q"
  by (simp only: full_ZF_collect_reindex; rule full_ZF_future_collect_cong; rule agree; assumption)

end

text \<open>
  A future comprehension is unchanged by the actual world-code
  bijection. Compatibility of the predicates is needed only on
  actual worlds; decoder behavior outside the world set is irrelevant.
  These lemmas compare the independently prescribed operation graphs
  with the canonical future-set calculations without assuming the
  prescribed graphs already belong to the domains.
\<close>

end
