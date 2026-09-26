theory Bacon_Book_ZF_Modalized_Family
  imports Bacon_Book_ZF_All_Type_Inverses
    Bacon_Book_Modal_Representation.Bacon_Book_Modalized_Bijection
begin

context book_full_C_coded_frame
begin

theorem full_ZF_i_type:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_i \<sigma> w v a \<in> explode (full_ZF_D \<sigma> v)"
proof -
  have inverse: "full_ZF_j \<sigma> w a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF worlds_admitted[OF ww] member])
  have moved: "book_C_term_counterpart G w v \<sigma> (full_ZF_j \<sigma> w a) \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
    by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access inverse])
  show ?thesis unfolding full_ZF_i_def by (rule full_ZF_h_type[OF worlds_admitted[OF vw] moved])
qed

theorem full_ZF_i_identity:
  assumes ww: "w \<in> worlds" and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_i \<sigma> w w a = a"
proof -
  have inverse: "full_ZF_j \<sigma> w a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF worlds_admitted[OF ww] member])
  show ?thesis by (simp only: full_ZF_i_def book_C_term_counterpart_identity[OF rich full_rooted_base_world[OF ww] inverse] full_ZF_hj[OF worlds_admitted[OF ww] member])
qed

theorem full_ZF_j_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_j \<sigma> v (full_ZF_i \<sigma> w v a) = book_C_term_counterpart G w v \<sigma> (full_ZF_j \<sigma> w a)"
proof -
  have inverse: "full_ZF_j \<sigma> w a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF worlds_admitted[OF ww] member])
  have moved: "book_C_term_counterpart G w v \<sigma> (full_ZF_j \<sigma> w a) \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
    by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access inverse])
  show ?thesis by (simp only: full_ZF_i_def; rule full_ZF_jh[OF vw moved])
qed

theorem full_ZF_i_composition:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and uw: "u \<in> worlds"
    and wv: "le w v" and vu: "le v u" and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_i \<sigma> w u a = full_ZF_i \<sigma> v u (full_ZF_i \<sigma> w v a)"
proof -
  have inverse: "full_ZF_j \<sigma> w a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF worlds_admitted[OF ww] member])
  have chain: "book_C_term_counterpart G v u \<sigma> (book_C_term_counterpart G w v \<sigma> (full_ZF_j \<sigma> w a)) =
    book_C_term_counterpart G w u \<sigma> (full_ZF_j \<sigma> w a)"
    by (rule book_C_term_counterpart_composition[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw]
      full_rooted_base_world[OF uw] wv vu inverse])
  have "full_ZF_i \<sigma> w u a = full_ZF_h \<sigma> u (book_C_term_counterpart G w u \<sigma> (full_ZF_j \<sigma> w a))"
    by (rule full_ZF_i_def)
  also have "... = full_ZF_h \<sigma> u (book_C_term_counterpart G v u \<sigma> (book_C_term_counterpart G w v \<sigma> (full_ZF_j \<sigma> w a)))"
    by (simp only: chain)
  also have "... = full_ZF_h \<sigma> u (book_C_term_counterpart G v u \<sigma> (full_ZF_j \<sigma> v (full_ZF_i \<sigma> w v a)))"
    by (simp only: full_ZF_j_natural[OF ww vw wv member])
  also have "... = full_ZF_i \<sigma> v u (full_ZF_i \<sigma> w v a)" by (rule full_ZF_i_def[symmetric])
  finally show ?thesis .
qed

theorem full_ZF_h_natural:
  assumes ww: "w \<in> worlds" and member: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "full_ZF_h \<sigma> v (book_C_term_counterpart G w v \<sigma> X) = full_ZF_i \<sigma> w v (full_ZF_h \<sigma> w X)"
  by (simp only: full_ZF_i_def full_ZF_jh[OF ww member])

theorem full_ZF_domains_modalized:
  "book_modalized_set worlds le (\<lambda>w. explode (full_ZF_D \<sigma> w)) (full_ZF_i \<sigma>)"
proof -
  interpret Order: book_pointed_preorder worlds le actual by (rule full_frame_pointed_preorder)
  show ?thesis by (unfold_locales; (rule full_ZF_i_type | rule full_ZF_i_identity | rule full_ZF_i_composition); assumption)
qed

theorem full_ZF_representation_bijection:
  "book_modalized_bijection worlds le (\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<sigma>)
    (\<lambda>w v X. book_C_term_counterpart G w v \<sigma> X) (\<lambda>w. explode (full_ZF_D \<sigma> w)) (full_ZF_i \<sigma>) (full_ZF_h \<sigma>)"
proof -
  interpret S: book_modalized_set worlds le "\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<sigma>"
    "\<lambda>w v X. book_C_term_counterpart G w v \<sigma> X" by (rule full_term_modalized_set)
  interpret T: book_modalized_set worlds le "\<lambda>w. explode (full_ZF_D \<sigma> w)" "full_ZF_i \<sigma>" by (rule full_ZF_domains_modalized)
  have map: "book_modalized_map worlds le (\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<sigma>)
    (\<lambda>w v X. book_C_term_counterpart G w v \<sigma> X) (\<lambda>w. explode (full_ZF_D \<sigma> w)) (full_ZF_i \<sigma>) (full_ZF_h \<sigma>)"
    by (rule book_modalized_mapI; (rule full_ZF_h_type[OF worlds_admitted] | rule full_ZF_h_natural); assumption)
  show ?thesis by (unfold_locales; (rule map | rule full_ZF_h_bijection); assumption?)
qed

theorem full_ZF_domains_nonempty:
  assumes ww: "w \<in> worlds"
  shows "explode (full_ZF_D \<sigma> w) \<noteq> {}"
proof -
  have source: "book_C_identity_domain (fst w) G (snd w) \<sigma> \<noteq> {}"
    by (rule book_full_C_canonical_identity_domain_nonempty[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  show ?thesis using source by (simp add: full_ZF_D_elements[OF worlds_admitted[OF ww]])
qed

end

text \<open>
  The single recursively defined family is now a family of nonempty
  modalized sets, with hσ a modalized bijection at every full type.
  Counterparts are defined by the source counterparts and the proved
  inverse maps. Their identification with set truncation at t and graph
  restriction at function types is still a separate source-correspondence
  obligation; those identifications are not inserted into these proofs.
\<close>

end
