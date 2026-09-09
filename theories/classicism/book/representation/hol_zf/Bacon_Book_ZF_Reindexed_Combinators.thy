theory Bacon_Book_ZF_Reindexed_Combinators
  imports Bacon_Book_ZF_Reindexed_Collect
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_K_identification:
  "full_ZF_K_value actual \<sigma> \<tau> =
    book_ZF_k full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root \<sigma> \<tau>"
proof -
  interpret S: book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    by (rule full_ZF_reindexed_structure)
  have kt: "full_ZF_K_value actual \<sigma> \<tau> \<in> explode (full_ZF_D_at (Arr \<sigma> (Arr \<tau> \<sigma>)) full_ZF_root)"
    by (simp only: full_ZF_D_at_root; rule full_ZF_K_value_type)
  show ?thesis
  proof (unfold book_ZF_k_def, rule S.function_as_two_lambdas[OF full_ZF_root_member kt])
    fix v a u b
    assume vw: "v \<in> explode full_world_set" and "full_ZF_R full_ZF_root v"
      and am: "a \<in> explode (full_ZF_D_at \<sigma> v)"
      and uw: "u \<in> explode full_world_set" and access: "full_ZF_R v u"
      and bm: "b \<in> explode (full_ZF_D_at \<tau> u)"
    have behavior: "app (app (full_ZF_K_value actual \<sigma> \<tau>) (Opair v a)) (Opair u b) =
      full_ZF_i_at \<sigma> v u a"
      using full_ZF_K_future_value[OF full_world_decode_type[OF vw] full_world_decode_type[OF uw]
        access[unfolded full_ZF_R_def] am[unfolded full_ZF_D_at_def] bm[unfolded full_ZF_D_at_def]]
      by (simp only: full_world_code_decode[OF vw] full_world_code_decode[OF uw] full_ZF_i_at_def)
    show "app (app (full_ZF_K_value actual \<sigma> \<tau>) (Opair v a)) (Opair u b) =
      full_ZF_i_at \<sigma> (Fst (Opair v a)) (Fst (Opair u b)) (Snd (Opair v a))"
      by (simp only: Fst Snd; rule behavior)
  qed
qed

theorem full_ZF_S_identification:
  "full_ZF_S_value actual \<sigma> \<tau> \<rho> =
    book_ZF_s full_world_set full_ZF_R full_ZF_D_at full_ZF_root \<sigma> \<tau> \<rho>"
proof -
  interpret S: book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    by (rule full_ZF_reindexed_structure)
  have st: "full_ZF_S_value actual \<sigma> \<tau> \<rho> \<in>
    explode (full_ZF_D_at (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) full_ZF_root)"
    by (simp only: full_ZF_D_at_root; rule full_ZF_S_value_type)
  show ?thesis
  proof (unfold book_ZF_s_def, rule S.function_as_three_lambdas[OF full_ZF_root_member st])
    fix v f u g t a
    assume vw: "v \<in> explode full_world_set" and "full_ZF_R full_ZF_root v"
      and fm: "f \<in> explode (full_ZF_D_at (Arr \<sigma> (Arr \<tau> \<rho>)) v)"
      and uw: "u \<in> explode full_world_set" and vu: "full_ZF_R v u"
      and gm: "g \<in> explode (full_ZF_D_at (Arr \<sigma> \<tau>) u)"
      and tw: "t \<in> explode full_world_set" and ut: "full_ZF_R u t"
      and am: "a \<in> explode (full_ZF_D_at \<sigma> t)"
    have behavior: "app (app (app (full_ZF_S_value actual \<sigma> \<tau> \<rho>) (Opair v f)) (Opair u g)) (Opair t a) =
      app (app f (Opair t a)) (Opair t (app g (Opair t a)))"
      using full_ZF_S_future_value[OF full_world_decode_type[OF vw] full_world_decode_type[OF uw] full_world_decode_type[OF tw]
        vu[unfolded full_ZF_R_def] ut[unfolded full_ZF_R_def] fm[unfolded full_ZF_D_at_def]
        gm[unfolded full_ZF_D_at_def] am[unfolded full_ZF_D_at_def]]
      by (simp only: full_world_code_decode[OF vw] full_world_code_decode[OF uw] full_world_code_decode[OF tw])
    show "app (app (app (full_ZF_S_value actual \<sigma> \<tau> \<rho>) (Opair v f)) (Opair u g)) (Opair t a) =
      app (app (Snd (Opair v f)) (Opair (Fst (Opair t a)) (Snd (Opair t a))))
        (Opair (Fst (Opair t a)) (app (Snd (Opair u g)) (Opair (Fst (Opair t a)) (Snd (Opair t a)))))"
      by (simp only: Fst Snd; rule behavior)
  qed
qed

end

text \<open>
  The actual canonical k and s values are equal to the independent
  definition's prescribed graphs. Candidate membership and the proved
  future behavior determine the nested Lambda graphs; target membership
  is not assumed. Only the established world-code bijection is used
  to pass between the two presentations of worlds.
\<close>

end
