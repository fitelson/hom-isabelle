theory Bacon_Book_ZF_Reindexed_Identity_Operator
  imports Bacon_Book_ZF_Reindexed_Logical_Operators
begin

context book_full_C_coded_frame
begin

theorem full_ZF_identity_identification:
  "full_ZF_equality_value actual \<sigma> =
    book_ZF_eq full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root \<sigma>"
proof -
  interpret S: book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    by (rule full_ZF_reindexed_structure)
  have et: "full_ZF_equality_value actual \<sigma> \<in> explode (full_ZF_D_at (Arr \<sigma> (Arr \<sigma> Prop)) full_ZF_root)"
    by (simp only: full_ZF_D_at_root; rule full_ZF_equality_value_type[OF root_admitted])
  show ?thesis
  proof (unfold book_ZF_eq_def, rule S.function_as_two_lambdas[OF full_ZF_root_member et])
    fix v a u b
    assume vw: "v \<in> explode full_world_set" and "full_ZF_R full_ZF_root v"
      and am: "a \<in> explode (full_ZF_D_at \<sigma> v)"
      and uw: "u \<in> explode full_world_set" and vu: "full_ZF_R v u"
      and bm: "b \<in> explode (full_ZF_D_at \<sigma> u)"
    have behavior: "app (app (full_ZF_equality_value actual \<sigma>) (Opair v a)) (Opair u b) =
      full_ZF_future_collect (full_world_decode u) (\<lambda>t.
        full_ZF_i \<sigma> (full_world_decode v) t a = full_ZF_i \<sigma> (full_world_decode u) t b)"
      using full_ZF_equality_future_value[OF full_world_decode_type[OF vw] full_world_decode_type[OF uw]
        vu[unfolded full_ZF_R_def] am[unfolded full_ZF_D_at_def] bm[unfolded full_ZF_D_at_def]]
      by (simp only: full_world_code_decode[OF vw] full_world_code_decode[OF uw])
    have collect: "book_ZF_collect full_world_set full_ZF_R u (\<lambda>t. full_ZF_i_at \<sigma> v t a = full_ZF_i_at \<sigma> u t b) =
      full_ZF_future_collect (full_world_decode u) (\<lambda>t.
        full_ZF_i \<sigma> (full_world_decode v) t a = full_ZF_i \<sigma> (full_world_decode u) t b)"
    proof (rule full_ZF_collect_compatible)
      fix t
      assume tw: "t \<in> worlds"
      show "(full_ZF_i_at \<sigma> v (book_ZF_world_code t) a = full_ZF_i_at \<sigma> u (book_ZF_world_code t) b) =
        (full_ZF_i \<sigma> (full_world_decode v) t a = full_ZF_i \<sigma> (full_world_decode u) t b)"
        by (simp only: full_ZF_i_at_def full_world_decode_code[OF tw])
    qed
    show "app (app (full_ZF_equality_value actual \<sigma>) (Opair v a)) (Opair u b) =
      book_ZF_collect full_world_set full_ZF_R (Fst (Opair u b))
        (\<lambda>t. full_ZF_i_at \<sigma> (Fst (Opair v a)) t (Snd (Opair v a)) =
          full_ZF_i_at \<sigma> (Fst (Opair u b)) t (Snd (Opair u b)))"
      by (simp only: Fst Snd collect; rule behavior)
  qed
qed

end

text \<open>
  The canonical closed Leibniz operator is exactly the independent
  definition's future equality graph. The proof uses actual equality
  of proposition sets after world reindexing. It does not assume
  an independent equality-operator membership field to prove that field.
\<close>

end
