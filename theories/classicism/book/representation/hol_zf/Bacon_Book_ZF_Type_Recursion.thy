theory Bacon_Book_ZF_Type_Recursion
  imports Bacon_Book_ZF_Future_Pairs
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Proposition_Representation
begin

context book_full_C_coded_frame
begin

primrec full_ZF_h :: "otype \<Rightarrow> 'c book_C_world \<Rightarrow> 'c book_named_term set \<Rightarrow> ZF" where
  "full_ZF_h Ind = (\<lambda>w X. class_code X)"
| "full_ZF_h Prop = (\<lambda>w X. paper_ZF_image_code full_world_set book_ZF_world_code
    (book_full_C_proposition_h \<Sigma> B G actual w X))"
| "full_ZF_h (Arr \<sigma> \<tau>) = (\<lambda>w X. Lambda (full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) w)
    (\<lambda>p. full_ZF_h \<tau> (full_world_decode (Fst p))
      (book_C_term_app (fst (full_world_decode (Fst p))) G (snd (full_world_decode (Fst p))) \<sigma> \<tau>
        (book_C_term_counterpart G w (full_world_decode (Fst p)) (Arr \<sigma> \<tau>) X)
        (full_ZF_inverse \<sigma> (full_ZF_h \<sigma>) (full_world_decode (Fst p)) (Snd p)))))"

definition full_ZF_D where "full_ZF_D \<sigma> = full_ZF_domain \<sigma> (full_ZF_h \<sigma>)"
definition full_ZF_j where "full_ZF_j \<sigma> = full_ZF_inverse \<sigma> (full_ZF_h \<sigma>)"
definition full_ZF_i where
  "full_ZF_i \<sigma> w v a = full_ZF_h \<sigma> v (book_C_term_counterpart G w v \<sigma> (full_ZF_j \<sigma> w a))"

theorem full_ZF_D_elements:
  assumes admitted: "full_ZF_admitted w"
  shows "explode (full_ZF_D \<sigma> w) = full_ZF_h \<sigma> w ` book_C_identity_domain (fst w) G (snd w) \<sigma>"
  by (simp only: full_ZF_D_def full_ZF_domain_elements[OF admitted])

lemma full_ZF_h_type:
  assumes admitted: "full_ZF_admitted w"
    and member: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "full_ZF_h \<sigma> w X \<in> explode (full_ZF_D \<sigma> w)"
  by (simp only: full_ZF_D_elements[OF admitted]; rule imageI[OF member])

lemma full_ZF_j_type:
  assumes admitted: "full_ZF_admitted w" and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_j \<sigma> w a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
proof -
  have unfolded: "a \<in> explode (full_ZF_domain \<sigma> (full_ZF_h \<sigma>) w)" using member unfolding full_ZF_D_def .
  show ?thesis unfolding full_ZF_j_def by (rule full_ZF_inverse_type[OF admitted unfolded])
qed

theorem full_ZF_hj:
  assumes admitted: "full_ZF_admitted w" and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_h \<sigma> w (full_ZF_j \<sigma> w a) = a"
proof -
  have image_member: "a \<in> full_ZF_h \<sigma> w ` book_C_identity_domain (fst w) G (snd w) \<sigma>"
    using member by (simp only: full_ZF_D_elements[OF admitted])
  show ?thesis unfolding full_ZF_j_def full_ZF_inverse_def by (rule f_inv_into_f[OF image_member])
qed

text \<open>
  One primitive recursion on the object-language type now defines hσ
  at every full type, with values in the same explicitly declared ZF
  universe. Dσ is its actual range set and jσ its inverse-into source.
  At e the values are coded identity classes; at t they are actual sets
  of world codes; at σ→τ they are actual graphs on the coded future pairs.
  Initial range/typing and h∘j laws are checked at pairs whose
  signature is included in the ambient signature B (all worlds qualify). Injectivity, j∘h, the
  counterpart laws and source function-space correspondence are not
  assumed and remain to be established by induction.
\<close>

end

end
