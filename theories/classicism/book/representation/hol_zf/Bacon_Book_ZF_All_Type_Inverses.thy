theory Bacon_Book_ZF_All_Type_Inverses
  imports Bacon_Book_ZF_Arrow_Values
    Bacon_Book_Modal_Representation.Bacon_Book_Full_Term_Modalized_Sets
begin

context book_full_C_canonical_frame
begin

lemma full_ZF_jh_from_injective:
  assumes injective: "inj_on (full_ZF_h \<sigma> w) (book_C_identity_domain (fst w) G (snd w) \<sigma>)"
    and member: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "full_ZF_j \<sigma> w (full_ZF_h \<sigma> w X) = X"
  unfolding full_ZF_j_def full_ZF_inverse_def by (rule inv_into_f_f[OF injective member])

theorem full_ZF_h_injective:
  assumes ww: "w \<in> worlds"
  shows "inj_on (full_ZF_h \<sigma> w) (book_C_identity_domain (fst w) G (snd w) \<sigma>)"
  using ww
proof (induction \<sigma> arbitrary: w)
  case Ind
  show ?case by (rule full_ZF_individual_injective)
next
  case Prop
  show ?case by (rule full_ZF_proposition_injective[OF Prop.prems])
next
  case (Arr \<sigma> \<tau>)
  show ?case
  proof (rule inj_onI)
    fix X Y
    assume xd: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
      and yd: "Y \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
      and same: "full_ZF_h (Arr \<sigma> \<tau>) w X = full_ZF_h (Arr \<sigma> \<tau>) w Y"
    show "X = Y"
    proof (rule full_term_quasi_functional[OF Arr.prems xd yd])
      fix v a
      assume vw: "v \<in> worlds" and access: "le w v" and ad: "a \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
      let ?a = "full_ZF_h \<sigma> v a"
      have at: "?a \<in> explode (full_ZF_D \<sigma> v)" by (rule full_ZF_h_type[OF ad])
      have inverse: "full_ZF_j \<sigma> v ?a = a" by (rule full_ZF_jh_from_injective[OF Arr.IH(1)[OF vw] ad])
      have equal_values: "app (full_ZF_h (Arr \<sigma> \<tau>) w X) (Opair (book_ZF_world_code v) ?a) =
        app (full_ZF_h (Arr \<sigma> \<tau>) w Y) (Opair (book_ZF_world_code v) ?a)"
        by (rule arg_cong[where f="\<lambda>z. app z (Opair (book_ZF_world_code v) ?a)", OF same])
      let ?X = "book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X"
      let ?Y = "book_C_term_counterpart G w v (Arr \<sigma> \<tau>) Y"
      let ?L = "book_C_term_app (fst v) G (snd v) \<sigma> \<tau> ?X a"
      let ?R = "book_C_term_app (fst v) G (snd v) \<sigma> \<tau> ?Y a"
      have represented: "full_ZF_h \<tau> v ?L = full_ZF_h \<tau> v ?R"
        using equal_values by (simp only: full_ZF_arrow_value[OF vw access at] inverse)
      have xv: "?X \<in> book_C_identity_domain (fst v) G (snd v) (Arr \<sigma> \<tau>)"
        by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF Arr.prems] full_rooted_base_world[OF vw] access xd])
      have yv: "?Y \<in> book_C_identity_domain (fst v) G (snd v) (Arr \<sigma> \<tau>)"
        by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF Arr.prems] full_rooted_base_world[OF vw] access yd])
      interpret V: book_C_identity_world "fst v" G "snd v" by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF vw]])
      have lt: "?L \<in> book_C_identity_domain (fst v) G (snd v) \<tau>" by (rule V.term_app_typed[OF xv ad])
      have rt: "?R \<in> book_C_identity_domain (fst v) G (snd v) \<tau>" by (rule V.term_app_typed[OF yv ad])
      show "?L = ?R" by (rule inj_onD[OF Arr.IH(2)[OF vw] represented lt rt])
    qed
  qed
qed

theorem full_ZF_h_bijection:
  assumes ww: "w \<in> worlds"
  shows "bij_betw (full_ZF_h \<sigma> w) (book_C_identity_domain (fst w) G (snd w) \<sigma>) (explode (full_ZF_D \<sigma> w))"
  unfolding bij_betw_def by (rule conjI[OF full_ZF_h_injective[OF ww] full_ZF_D_elements[symmetric]])

theorem full_ZF_jh:
  "w \<in> worlds \<Longrightarrow> X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma> \<Longrightarrow>
    full_ZF_j \<sigma> w (full_ZF_h \<sigma> w X) = X"
  by (rule full_ZF_jh_from_injective[OF full_ZF_h_injective]; assumption)

end

text \<open>
  This is one induction over the full object-language type datatype,
  not a collection of unrelated HOL-type instances. The arrow case uses
  actual graph application at every coded future pair, the lower inverse
  and injection, and the independently proved all-type term quasi-
  functionality. Thus hσ is bijective onto its actual range Dσ, and
  both inverse equations hold at every type. Counterpart/function-space
  correspondence and the complete logical-model certificate remain.
\<close>

end
