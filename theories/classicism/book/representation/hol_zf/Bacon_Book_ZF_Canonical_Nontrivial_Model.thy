theory Bacon_Book_ZF_Canonical_Nontrivial_Model
  imports Bacon_Book_ZF_Canonical_Interpretation
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Nontrivial_Interpretation
begin

section \<open>The canonical model satisfies the nontriviality refinement\<close>

context book_full_C_coded_frame
begin

lemma full_ZF_reindexed_domains_nonempty:
  assumes ww: "w \<in> explode full_world_set"
  shows "explode (full_ZF_D_at \<sigma> w) \<noteq> {}"
  unfolding full_ZF_D_at_def
  by (rule full_ZF_domains_nonempty[OF full_world_decode_type[OF ww]])

lemma full_ZF_reindexed_false_at_world:
  assumes ww: "w \<in> explode full_world_set"
  shows "\<exists>p\<in>explode (full_ZF_D_at Prop w). \<not> Elem w p"
  using full_ZF_false_proposition[OF full_world_decode_type[OF ww]]
  by (simp only: full_ZF_D_at_def full_ZF_value_truth_def full_world_code_decode[OF ww])

theorem full_ZF_canonical_nontrivial_modal_model:
  "book_ZF_nontrivial_modal_model full_world_set full_ZF_R full_ZF_root
    full_ZF_D_at full_ZF_i_at \<Sigma> full_ZF_constant_value"
  by (rule book_ZF_nontrivial_modal_model.intro[OF full_ZF_canonical_modal_model];
    rule book_ZF_nontrivial_modal_model_axioms.intro;
    (rule full_ZF_reindexed_domains_nonempty | rule full_ZF_reindexed_false_at_world); assumption)

text \<open>
  Both additional conditions are proved of the SAME constructed data,
  using the already verified per-world domains and false propositions.
  No new model premise, alternate carrier or new constant interpretation
  is inserted. The coded-frame assumptions of book_full_C_coded_frame
  remain explicit; countable coding is one instance.
\<close>

end

end
