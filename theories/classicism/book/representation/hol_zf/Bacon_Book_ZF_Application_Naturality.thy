theory Bacon_Book_ZF_Application_Naturality
  imports Bacon_Book_ZF_Closed_Values
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_future_application:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and fm: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)"
    and am: "a \<in> explode (full_ZF_D \<sigma> v)"
  shows "app F (Opair (book_ZF_world_code v) a) =
    full_ZF_app v \<sigma> \<tau> (full_ZF_i (Arr \<sigma> \<tau>) w v F) a"
proof -
  have pair: "Elem (Opair (book_ZF_world_code v) a) (full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) v)"
    by (simp only: full_ZF_future_pair_member[OF vw] full_ZF_D_def[symmetric]
      book_full_C_rooted_refl[OF vw] simp_thms; rule am)
  show ?thesis by (simp only: full_ZF_app_def full_ZF_i_arrow_restriction[OF ww vw access fm]
    full_ZF_arrow_restrict_def Lambda_app[OF pair])
qed

theorem full_ZF_future_application_type:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and fm: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)"
    and am: "a \<in> explode (full_ZF_D \<sigma> v)"
  shows "app F (Opair (book_ZF_world_code v) a) \<in> explode (full_ZF_D \<tau> v)"
  by (simp only: full_ZF_future_application[OF ww vw access fm am];
    rule full_ZF_app_type[OF vw full_ZF_i_type[OF ww vw access fm] am])

theorem full_ZF_app_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and fm: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)"
    and am: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_i \<tau> w v (full_ZF_app w \<sigma> \<tau> F a) =
    full_ZF_app v \<sigma> \<tau> (full_ZF_i (Arr \<sigma> \<tau>) w v F) (full_ZF_i \<sigma> w v a)"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  let ?X = "full_ZF_j (Arr \<sigma> \<tau>) w F"
  let ?b = "full_ZF_j \<sigma> w a"
  let ?Xv = "book_C_term_counterpart G w v (Arr \<sigma> \<tau>) ?X"
  let ?bv = "book_C_term_counterpart G w v \<sigma> ?b"
  let ?R = "book_C_term_app (fst w) G (snd w) \<sigma> \<tau> ?X ?b"
  have xt: "?X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)" by (rule full_ZF_j_type[OF fm])
  have bt: "?b \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF am])
  have rt: "?R \<in> book_C_identity_domain (fst w) G (snd w) \<tau>" by (rule T.term_app_typed[OF xt bt])
  have xv: "?Xv \<in> book_C_identity_domain (fst v) G (snd v) (Arr \<sigma> \<tau>)"
    by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access xt])
  have bv: "?bv \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
    by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access bt])
  have application: "full_ZF_app w \<sigma> \<tau> F a = full_ZF_h \<tau> w ?R"
    using full_ZF_app_h[OF ww xt bt] by (simp only: full_ZF_hj[OF fm] full_ZF_hj[OF am])
  have natural: "book_C_term_counterpart G w v \<tau> ?R = book_C_term_app (fst v) G (snd v) \<sigma> \<tau> ?Xv ?bv"
    by (rule book_C_term_application_naturality[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access xt bt])
  have target: "full_ZF_app v \<sigma> \<tau> (full_ZF_i (Arr \<sigma> \<tau>) w v F) (full_ZF_i \<sigma> w v a) =
    full_ZF_h \<tau> v (book_C_term_app (fst v) G (snd v) \<sigma> \<tau> ?Xv ?bv)"
    by (simp only: full_ZF_i_def; rule full_ZF_app_h[OF vw xv bv])
  show ?thesis by (simp only: application full_ZF_h_natural[OF ww rt, symmetric] natural target)
qed

end

text \<open>
  Evaluation at a future pair is evaluation of the restricted function
  at that future world. Its output has the correct future type.
  Pointwise application also commutes with both counterparts. The
  first fact uses the actual graph-restriction equation; the second
  uses the proved source application map and recursive inverse laws.
\<close>

end
