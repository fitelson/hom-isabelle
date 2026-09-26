theory Bacon_Book_ZF_Reindexed_Structure
  imports Bacon_Book_ZF_Reindexed_Functions
begin

context book_full_C_coded_frame
begin

lemma full_ZF_reindexed_propositions:
  "w \<in> explode full_world_set \<Longrightarrow> p \<in> explode (full_ZF_D_at Prop w) \<Longrightarrow>
    explode p \<subseteq> explode (book_ZF_future full_world_set full_ZF_R w)"
  by (simp only: full_ZF_reindexed_future full_ZF_D_at_def;
    rule full_ZF_proposition_future[OF worlds_admitted[OF full_world_decode_type]]; assumption)

lemma full_ZF_reindexed_proposition_restriction:
  assumes ww: "w \<in> explode full_world_set" and vw: "v \<in> explode full_world_set" and access: "full_ZF_R w v"
    and pm: "p \<in> explode (full_ZF_D_at Prop w)"
  shows "full_ZF_i_at Prop w v p = Sep p (full_ZF_R v)"
  using full_ZF_i_proposition_restriction[OF full_world_decode_type[OF ww] full_world_decode_type[OF vw]
    access[unfolded full_ZF_R_def] pm[unfolded full_ZF_D_at_def]]
  by (simp only: full_ZF_i_at_def full_ZF_R_function full_ZF_proposition_restrict_def)

theorem full_ZF_reindexed_structure:
  "book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at"
proof -
  interpret Frame: book_ZF_frame full_world_set full_ZF_R full_ZF_root by (rule full_ZF_reindexed_frame)
  show ?thesis
    by (rule book_ZF_modal_structure.intro[OF full_ZF_reindexed_frame];
      rule book_ZF_modal_structure_axioms.intro;
      (rule full_ZF_reindexed_domains | rule full_ZF_reindexed_propositions |
      rule full_ZF_reindexed_proposition_restriction | rule full_ZF_reindexed_graph_exact |
      rule full_ZF_reindexed_function_type | rule full_ZF_reindexed_function_natural |
      rule full_ZF_reindexed_function_restriction); assumption?)
qed

end

text \<open>
  The actual reindexed data now instantiate every field of the
  independently defined concrete modalized structure, including
  the proposition subdomain and function-space restrictions.
  Operator equalities and original-signature root constants remain
  to be assembled for the stronger independent modal-model predicate.
\<close>

end
