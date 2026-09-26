theory Bacon_Book_ZF_Recursion_Base
  imports Bacon_Book_ZF_Type_Recursion
begin

context book_full_C_coded_frame
begin

lemma full_world_subset_code_elements:
  assumes subset: "P \<subseteq> worlds"
  shows "explode (paper_ZF_image_code full_world_set book_ZF_world_code P) = book_ZF_world_code ` P"
proof -
  have bound: "book_ZF_world_code ` worlds \<subseteq> explode full_world_set"
    by (simp only: full_world_set_elements; rule subset_refl)
  show ?thesis by (rule paper_ZF_image_code_elements[OF bound subset])
qed

lemma full_world_subset_code_eq:
  assumes ps: "P \<subseteq> worlds" and qs: "Q \<subseteq> worlds"
  shows "paper_ZF_image_code full_world_set book_ZF_world_code P = paper_ZF_image_code full_world_set book_ZF_world_code Q \<longleftrightarrow> P = Q"
proof
  assume equal: "paper_ZF_image_code full_world_set book_ZF_world_code P = paper_ZF_image_code full_world_set book_ZF_world_code Q"
  have decoded: "explode (paper_ZF_image_code full_world_set book_ZF_world_code P) = explode (paper_ZF_image_code full_world_set book_ZF_world_code Q)"
    by (rule arg_cong[OF equal])
  have images: "book_ZF_world_code ` P = book_ZF_world_code ` Q"
    using decoded by (simp only: full_world_subset_code_elements[OF ps] full_world_subset_code_elements[OF qs])
  show "P = Q" using images by (simp only: inj_on_image_eq_iff[OF full_world_code_injective ps qs])
next
  assume "P = Q"
  then show "paper_ZF_image_code full_world_set book_ZF_world_code P = paper_ZF_image_code full_world_set book_ZF_world_code Q" by simp
qed

lemma full_ZF_individual_injective:
  assumes admitted: "full_ZF_admitted w"
  shows "inj_on (full_ZF_h Ind w) (book_C_identity_domain (fst w) G (snd w) Ind)"
  by (simp only: full_ZF_h.simps; rule inj_on_subset[OF class_code_injective identity_domain_admitted[OF admitted]])

theorem full_ZF_proposition_injective:
  assumes ww: "w \<in> worlds"
  shows "inj_on (full_ZF_h Prop w) (book_C_identity_domain (fst w) G (snd w) Prop)"
proof (rule inj_onI)
  fix X Y
  assume xd: "X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
    and yd: "Y \<in> book_C_identity_domain (fst w) G (snd w) Prop"
    and equal: "full_ZF_h Prop w X = full_ZF_h Prop w Y"
  let ?h = "book_full_C_proposition_h \<Sigma> B G actual w"
  have bijection: "bij_betw ?h (book_C_identity_domain (fst w) G (snd w) Prop) (book_full_C_proposition_domain \<Sigma> B G actual w)"
    by (rule proposition_h_bijection[OF ww])
  have image: "?h ` book_C_identity_domain (fst w) G (snd w) Prop = book_full_C_proposition_domain \<Sigma> B G actual w"
    using bijection unfolding bij_betw_def by (rule conjunct2)
  have xm: "?h X \<in> book_full_C_proposition_domain \<Sigma> B G actual w"
    by (simp only: image[symmetric]; rule imageI[OF xd])
  have ym: "?h Y \<in> book_full_C_proposition_domain \<Sigma> B G actual w"
    by (simp only: image[symmetric]; rule imageI[OF yd])
  have xs: "?h X \<subseteq> worlds" using proposition_domain_future[OF xm] by blast
  have ys: "?h Y \<subseteq> worlds" using proposition_domain_future[OF ym] by blast
  have same: "?h X = ?h Y" using equal by (simp only: full_ZF_h.simps full_world_subset_code_eq[OF xs ys])
  have injective: "inj_on ?h (book_C_identity_domain (fst w) G (snd w) Prop)"
    using bijection unfolding bij_betw_def by (rule conjunct1)
  show "X = Y" by (rule inj_onD[OF injective same xd yd])
qed

end

text \<open>
  Injectivity is checked at both primitive types. At e it is the
  concrete identity-class code injection. At t, exact world-subset
  coding and the already constructed full-C proposition bijection give
  injectivity. No global injection on raw world pairs or arbitrary
  proposition sets is assumed; the source profiles lie in the actual W.
\<close>

end
