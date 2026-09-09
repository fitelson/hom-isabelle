theory Bacon_Book_Full_Term_Application_Map
  imports Bacon_Book_Full_Term_Modalized_Sets
begin

context book_full_C_canonical_frame
begin

theorem full_term_application_product:
  "book_modalized_set worlds le
    (\<lambda>w. book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>) \<times> book_C_identity_domain (fst w) G (snd w) \<sigma>)
    (\<lambda>w v p. (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) (fst p), book_C_term_counterpart G w v \<sigma> (snd p)))"
  by (rule book_modalized_product[OF full_term_modalized_set full_term_modalized_set])

theorem full_term_application_map:
  "book_modalized_map worlds le
    (\<lambda>w. book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>) \<times> book_C_identity_domain (fst w) G (snd w) \<sigma>)
    (\<lambda>w v p. (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) (fst p), book_C_term_counterpart G w v \<sigma> (snd p)))
    (\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<tau>)
    (\<lambda>w v X. book_C_term_counterpart G w v \<tau> X)
    (\<lambda>w p. book_C_term_app (fst w) G (snd w) \<sigma> \<tau> (fst p) (snd p))"
proof (rule book_modalized_mapI)
  fix w p
  assume ww: "w \<in> worlds"
    and member: "p \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>) \<times> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  have head: "fst p \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and argument: "snd p \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" using member by auto
  show "book_C_term_app (fst w) G (snd w) \<sigma> \<tau> (fst p) (snd p) \<in> book_C_identity_domain (fst w) G (snd w) \<tau>"
    by (rule T.term_app_typed[OF head argument])
next
  fix w v p
  assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and member: "p \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>) \<times> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  have head: "fst p \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and argument: "snd p \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" using member by auto
  have equation: "book_C_term_counterpart G w v \<tau> (book_C_term_app (fst w) G (snd w) \<sigma> \<tau> (fst p) (snd p)) =
    book_C_term_app (fst v) G (snd v) \<sigma> \<tau> (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) (fst p))
      (book_C_term_counterpart G w v \<sigma> (snd p))"
    by (rule book_C_term_application_naturality[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access head argument])
  show "book_C_term_app (fst v) G (snd v) \<sigma> \<tau>
      (fst (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) (fst p), book_C_term_counterpart G w v \<sigma> (snd p)))
      (snd (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) (fst p), book_C_term_counterpart G w v \<sigma> (snd p))) =
    book_C_term_counterpart G w v \<tau> (book_C_term_app (fst w) G (snd w) \<sigma> \<tau> (fst p) (snd p))"
    by (simp only: fst_conv snd_conv; rule equation[symmetric])
qed

end

text \<open>
  The source of term application is an actual product of modalized
  sets. Application is a Definition 17.4 map into the result domain,
  by its already proved typing and counterpart equation. Neither
  naturality nor the source product is a new model assumption.
\<close>

end
