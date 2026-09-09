theory Bacon_Book_ZF_Future_Pairs
  imports Bacon_Book_ZF_Represented_Images
    Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Dependent_Pairs
begin

context book_full_C_canonical_frame
begin

definition full_ZF_domain :: "otype \<Rightarrow> ('c book_C_world \<Rightarrow> 'c book_named_term set \<Rightarrow> ZF) \<Rightarrow> 'c book_C_world \<Rightarrow> ZF" where
  "full_ZF_domain \<sigma> h w = book_ZF_powerset_image (h w) (book_C_identity_domain (fst w) G (snd w) \<sigma>)"

definition full_ZF_inverse :: "otype \<Rightarrow> ('c book_C_world \<Rightarrow> 'c book_named_term set \<Rightarrow> ZF) \<Rightarrow> 'c book_C_world \<Rightarrow> ZF \<Rightarrow> 'c book_named_term set" where
  "full_ZF_inverse \<sigma> h w = inv_into (book_C_identity_domain (fst w) G (snd w) \<sigma>) (h w)"

lemma full_ZF_domain_elements:
  "explode (full_ZF_domain \<sigma> h w) = h w ` book_C_identity_domain (fst w) G (snd w) \<sigma>"
  unfolding full_ZF_domain_def by (rule book_ZF_powerset_image_elements)

lemma full_ZF_inverse_type:
  "a \<in> explode (full_ZF_domain \<sigma> h w) \<Longrightarrow>
    full_ZF_inverse \<sigma> h w a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  unfolding full_ZF_inverse_def full_ZF_domain_elements by (rule inv_into_into; assumption)

definition full_ZF_future :: "'c book_C_world \<Rightarrow> ZF" where
  "full_ZF_future w = Sep full_world_set (\<lambda>z. le w (full_world_decode z))"

lemma full_ZF_future_world_member:
  assumes vw: "v \<in> worlds"
  shows "Elem (book_ZF_world_code v) (full_ZF_future w) \<longleftrightarrow> le w v"
proof -
  have member: "book_ZF_world_code v \<in> explode full_world_set"
    by (simp only: full_world_set_elements; rule imageI[OF vw])
  show ?thesis using member by (simp add: full_ZF_future_def Sep full_world_decode_code[OF vw] explode_Elem)
qed

definition full_ZF_future_pairs :: "otype \<Rightarrow> ('c book_C_world \<Rightarrow> 'c book_named_term set \<Rightarrow> ZF) \<Rightarrow> 'c book_C_world \<Rightarrow> ZF" where
  "full_ZF_future_pairs \<sigma> h w = paper_ZF_sigma (full_ZF_future w) (\<lambda>z. full_ZF_domain \<sigma> h (full_world_decode z))"

theorem full_ZF_future_pair_member:
  assumes vw: "v \<in> worlds"
  shows "Elem (Opair (book_ZF_world_code v) a) (full_ZF_future_pairs \<sigma> h w) \<longleftrightarrow>
    le w v \<and> a \<in> explode (full_ZF_domain \<sigma> h v)"
  by (simp only: full_ZF_future_pairs_def paper_ZF_sigma_pair_member full_ZF_future_world_member[OF vw]
    full_world_decode_code[OF vw] explode_Elem)

theorem full_ZF_future_pair_decode:
  assumes pair: "Elem p (full_ZF_future_pairs \<sigma> h w)"
  shows "full_world_decode (Fst p) \<in> worlds"
    and "le w (full_world_decode (Fst p))"
    and "Snd p \<in> explode (full_ZF_domain \<sigma> h (full_world_decode (Fst p)))"
    and "Opair (book_ZF_world_code (full_world_decode (Fst p))) (Snd p) = p"
proof -
  have data: "Elem (Fst p) (full_ZF_future w) \<and>
    Elem (Snd p) (full_ZF_domain \<sigma> h (full_world_decode (Fst p))) \<and> Opair (Fst p) (Snd p) = p"
    using paper_ZF_sigma_projections[OF pair[unfolded full_ZF_future_pairs_def]] .
  have world_code: "Fst p \<in> explode full_world_set" and future: "le w (full_world_decode (Fst p))"
    using data by (auto simp: full_ZF_future_def Sep explode_Elem)
  show "full_world_decode (Fst p) \<in> worlds" by (rule full_world_decode_type[OF world_code])
  show "le w (full_world_decode (Fst p))" by (rule future)
  show "Snd p \<in> explode (full_ZF_domain \<sigma> h (full_world_decode (Fst p)))" using data by (simp only: explode_Elem; blast)
  show "Opair (book_ZF_world_code (full_world_decode (Fst p))) (Snd p) = p"
    using data by (simp only: full_world_code_decode[OF world_code]; blast)
qed

end

text \<open>
  A proposed lower map h has an actual range set Dσw by Replacement.
  Future argument pairs are the internal dependent sum of those range
  sets over the encoded future worlds. Pair decoding is proved only
  on that sum and recovers a real world, its accessibility relation,
  and a value in the appropriate lower domain. No pair-domain bound
  or decoder correctness is added as an assumption.
\<close>

end
