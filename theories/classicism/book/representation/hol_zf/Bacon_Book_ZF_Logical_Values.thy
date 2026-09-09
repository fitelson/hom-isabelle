theory Bacon_Book_ZF_Logical_Values
  imports Bacon_Book_ZF_Characteristic_Truth
begin

context book_full_C_canonical_frame
begin

definition full_ZF_app :: "'c book_C_world \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "full_ZF_app w \<sigma> \<tau> F a = app F (Opair (book_ZF_world_code w) a)"

definition full_ZF_logical_value where
  "full_ZF_logical_value w l = full_ZF_h (book_minimal_logical_type l) w
    (book_C_term_logical_value (fst w) G (snd w) l)"

lemma full_ZF_app_h:
  assumes ww: "w \<in> worlds"
    and fm: "F \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and am: "a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "full_ZF_app w \<sigma> \<tau> (full_ZF_h (Arr \<sigma> \<tau>) w F) (full_ZF_h \<sigma> w a) =
    full_ZF_h \<tau> w (book_C_term_app (fst w) G (snd w) \<sigma> \<tau> F a)"
  unfolding full_ZF_app_def by (rule full_ZF_application_preserved[OF ww am fm])

theorem full_ZF_app_type:
  assumes ww: "w \<in> worlds" and fm: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)"
    and am: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_app w \<sigma> \<tau> F a \<in> explode (full_ZF_D \<tau> w)"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  let ?F = "full_ZF_j (Arr \<sigma> \<tau>) w F"
  let ?a = "full_ZF_j \<sigma> w a"
  have ft: "?F \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)" by (rule full_ZF_j_type[OF fm])
  have at: "?a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF am])
  have evaluated: "full_ZF_app w \<sigma> \<tau> F a =
    full_ZF_h \<tau> w (book_C_term_app (fst w) G (snd w) \<sigma> \<tau> ?F ?a)"
    using full_ZF_app_h[OF ww ft at] by (simp only: full_ZF_hj[OF fm] full_ZF_hj[OF am])
  show ?thesis by (simp only: evaluated; rule full_ZF_h_type[OF T.term_app_typed[OF ft at]])
qed

theorem full_ZF_logical_value_type:
  assumes ww: "w \<in> worlds"
  shows "full_ZF_logical_value w l \<in> explode (full_ZF_D (book_minimal_logical_type l) w)"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  show ?thesis unfolding full_ZF_logical_value_def by (rule full_ZF_h_type[OF T.term_logical_value_typed])
qed

theorem full_ZF_logical_denote:
  "full_ZF_denote w g (NLogical l) = full_ZF_logical_value w l"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV (fst w) G (NLogical l) (book_minimal_logical_type l)"
    by (rule book_language_Logical[OF UNIV_I])
  have closed: "named_fv (NLogical l) = {}" by simp
  show ?thesis by (simp only: full_ZF_denote_closed[OF language closed]
    full_ZF_logical_value_def book_C_term_logical_value_def)
qed

end

text \<open>
  Logical values are the h-images of the actual term logical values,
  and they are the denotations of the literal primitive symbols.
  Pointwise application is actual graph evaluation at (w,a); its
  type closure is proved from the recursive inverse maps and source
  application. No logical truth clause or model field is postulated.
\<close>

end
