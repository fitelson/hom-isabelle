theory Bacon_Book_ZF_Reindexed_Functions
  imports Bacon_Book_ZF_Reindexed_Frame
begin

context book_full_C_coded_frame
begin

lemma full_ZF_arrow_decode_on:
  assumes vw: "v \<in> worlds" and access: "le w v" and am: "a \<in> explode (full_ZF_D \<sigma> v)"
  shows "full_ZF_arrow_decode \<sigma> w F (v,a) = app F (Opair (book_ZF_world_code v) a)"
  using vw access am by (simp add: full_ZF_arrow_decode_def book_modalized_exponential_pairs_iff)

theorem full_ZF_future_homomorphism_equation:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and uw: "u \<in> worlds"
    and wv: "le w v" and vu: "le v u"
    and fm: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)" and am: "a \<in> explode (full_ZF_D \<sigma> v)"
  shows "full_ZF_i \<tau> v u (app F (Opair (book_ZF_world_code v) a)) =
    app F (Opair (book_ZF_world_code u) (full_ZF_i \<sigma> v u a))"
proof -
  have homo: "full_ZF_arrow_decode \<sigma> w F \<in> book_modalized_exponential worlds le
    (\<lambda>v. explode (full_ZF_D \<sigma> v)) (full_ZF_i \<sigma>) (\<lambda>v. explode (full_ZF_D \<tau> v)) (full_ZF_i \<tau>) w"
    by (rule full_ZF_arrow_domain_homomorphisms[OF ww fm])
  have moved: "full_ZF_i \<sigma> v u a \<in> explode (full_ZF_D \<sigma> u)" by (rule full_ZF_i_type[OF vw uw vu am])
  have wu: "le w u" by (rule book_full_C_rooted_trans[OF ww wv vu])
  show ?thesis using book_modalized_exponential_natural[OF homo vw wv uw vu am]
    by (simp only: full_ZF_arrow_decode_on[OF vw wv am] full_ZF_arrow_decode_on[OF uw wu moved])
qed

theorem full_ZF_reindexed_function_graph:
  assumes wz: "w \<in> explode full_world_set"
    and member: "F \<in> explode (full_ZF_D_at (Arr \<sigma> \<tau>) w)"
  shows "isFun F \<and> Domain F = book_ZF_pairs full_world_set full_ZF_R (full_ZF_D_at \<sigma>) w"
proof -
  obtain X where shape: "F = full_ZF_h (Arr \<sigma> \<tau>) (full_world_decode w) X"
    using member unfolding full_ZF_D_at_def
      full_ZF_D_elements[OF worlds_admitted[OF full_world_decode_type[OF wz]]] by blast
  show ?thesis by (simp only: shape full_ZF_reindexed_pairs; rule full_ZF_arrow_domain)
qed

theorem full_ZF_reindexed_graph_exact:
  assumes wz: "w \<in> explode full_world_set"
    and member: "F \<in> explode (full_ZF_D_at (Arr \<sigma> \<tau>) w)"
  shows "F = Lambda (book_ZF_pairs full_world_set full_ZF_R (full_ZF_D_at \<sigma>) w) (app F)"
proof -
  obtain X where shape: "F = full_ZF_h (Arr \<sigma> \<tau>) (full_world_decode w) X"
    using member unfolding full_ZF_D_at_def
      full_ZF_D_elements[OF worlds_admitted[OF full_world_decode_type[OF wz]]] by blast
  show ?thesis by (simp only: full_ZF_reindexed_pairs shape full_ZF_h.simps; rule book_ZF_graph_eta[symmetric])
qed

theorem full_ZF_reindexed_function_type:
  assumes ww: "w \<in> explode full_world_set" and vw: "v \<in> explode full_world_set" and access: "full_ZF_R w v"
    and fm: "F \<in> explode (full_ZF_D_at (Arr \<sigma> \<tau>) w)" and am: "a \<in> explode (full_ZF_D_at \<sigma> v)"
  shows "app F (Opair v a) \<in> explode (full_ZF_D_at \<tau> v)"
  using full_ZF_future_application_type[OF full_world_decode_type[OF ww] full_world_decode_type[OF vw]
    access[unfolded full_ZF_R_def] fm[unfolded full_ZF_D_at_def] am[unfolded full_ZF_D_at_def]]
  by (simp only: full_world_code_decode[OF vw] full_ZF_D_at_def)

theorem full_ZF_reindexed_function_natural:
  assumes ww: "w \<in> explode full_world_set" and vw: "v \<in> explode full_world_set" and uw: "u \<in> explode full_world_set"
    and wv: "full_ZF_R w v" and vu: "full_ZF_R v u"
    and fm: "F \<in> explode (full_ZF_D_at (Arr \<sigma> \<tau>) w)" and am: "a \<in> explode (full_ZF_D_at \<sigma> v)"
  shows "full_ZF_i_at \<tau> v u (app F (Opair v a)) = app F (Opair u (full_ZF_i_at \<sigma> v u a))"
  using full_ZF_future_homomorphism_equation[OF full_world_decode_type[OF ww] full_world_decode_type[OF vw]
    full_world_decode_type[OF uw] wv[unfolded full_ZF_R_def] vu[unfolded full_ZF_R_def]
    fm[unfolded full_ZF_D_at_def] am[unfolded full_ZF_D_at_def]]
  by (simp only: full_world_code_decode[OF vw] full_world_code_decode[OF uw] full_ZF_i_at_def)

theorem full_ZF_reindexed_function_restriction:
  assumes ww: "w \<in> explode full_world_set" and vw: "v \<in> explode full_world_set" and access: "full_ZF_R w v"
    and fm: "F \<in> explode (full_ZF_D_at (Arr \<sigma> \<tau>) w)"
  shows "full_ZF_i_at (Arr \<sigma> \<tau>) w v F = book_ZF_restrict full_world_set full_ZF_R (full_ZF_D_at \<sigma>) v F"
  by (simp only: full_ZF_i_at_def full_ZF_reindexed_restriction;
    rule full_ZF_i_arrow_restriction[OF full_world_decode_type[OF ww] full_world_decode_type[OF vw]
      access[unfolded full_ZF_R_def] fm[unfolded full_ZF_D_at_def]])

end

text \<open>
  The reindexed function values have the independent model's exact
  graph domains, typed future outputs, homomorphism equation and
  restriction law. The world-code inverse is used only on actual
  members of the world set. These are conclusions about the
  construction, not assumptions inserted into the model certificate.
\<close>

end
