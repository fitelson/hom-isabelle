theory Bacon_Book_ZF_Canonical_Modal_Model
  imports Bacon_Book_ZF_Root_Constants
begin

section \<open>Proposition 18.5: the constructed data form an independent modal model\<close>

context book_full_C_canonical_frame
begin

theorem full_ZF_logical_root_identification:
  "full_ZF_logical_value actual l =
    book_ZF_logical_root full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root l"
  by (cases l; simp only: book_ZF_logical_root.simps full_ZF_implication_identification full_ZF_universal_identification)

theorem full_ZF_canonical_modal_model:
  "book_ZF_modal_model full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at \<Sigma> full_ZF_constant_value"
proof (rule book_ZF_modal_model.intro[OF full_ZF_reindexed_structure], rule book_ZF_modal_model_axioms.intro)
  fix \<sigma> \<tau>
  show "book_ZF_k full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root \<sigma> \<tau> \<in>
    explode (full_ZF_D_at (Arr \<sigma> (Arr \<tau> \<sigma>)) full_ZF_root)"
    by (simp only: full_ZF_K_identification[symmetric] full_ZF_D_at_root; rule full_ZF_K_value_type)
next
  fix \<sigma> \<tau> \<rho>
  show "book_ZF_s full_world_set full_ZF_R full_ZF_D_at full_ZF_root \<sigma> \<tau> \<rho> \<in>
    explode (full_ZF_D_at (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) full_ZF_root)"
    by (simp only: full_ZF_S_identification[symmetric] full_ZF_D_at_root; rule full_ZF_S_value_type)
next
  show "book_ZF_if_future full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root \<in>
    explode (full_ZF_D_at (Arr Prop (Arr Prop Prop)) full_ZF_root)"
    by (simp only: full_ZF_implication_identification[symmetric] full_ZF_D_at_root;
      rule full_ZF_implication_value_type[OF book_full_C_root_is_world])
next
  fix \<sigma>
  show "book_ZF_all full_world_set full_ZF_R full_ZF_D_at full_ZF_root \<sigma> \<in>
    explode (full_ZF_D_at (Arr (Arr \<sigma> Prop) Prop) full_ZF_root)"
    by (simp only: full_ZF_universal_identification[symmetric] full_ZF_D_at_root;
      rule full_ZF_forall_value_type[OF book_full_C_root_is_world])
next
  fix \<sigma>
  show "book_ZF_eq full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root \<sigma> \<in>
    explode (full_ZF_D_at (Arr \<sigma> (Arr \<sigma> Prop)) full_ZF_root)"
    by (simp only: full_ZF_identity_identification[symmetric] full_ZF_D_at_root; rule full_ZF_equality_value_type)
next
  fix c \<sigma>
  assume declared: "c \<in> \<Sigma> \<sigma>"
  show "full_ZF_constant_value c \<sigma> \<in> explode (full_ZF_D_at \<sigma> full_ZF_root)"
    by (rule full_ZF_constant_value_type[OF declared])
qed

lemmas book_proposition_18_5_canonical = full_ZF_canonical_modal_model

theorem full_ZF_root_logical_denote:
  "full_ZF_denote actual g (NLogical l) =
    book_ZF_logical_root full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root l"
  by (simp only: full_ZF_logical_denote full_ZF_logical_root_identification)

end

text \<open>
  Every field of the independent modal-model definition is now
  instantiated by the same constructed data. The prescribed operator
  graphs are identified before their domain membership is transferred,
  and the constant interpretation covers the original signature.

  Scope: the countable-name full-C canonical frame, relative to
  standard HOL–ZF and the documented future-domain implication
  convention. This is Proposition 18.5's model certificate, not
  yet Theorem 18.4's theory-level existence/completeness result.
  Generic interpretation, source soundness and original-theory
  satisfaction remain separate proof obligations.
\<close>

end
