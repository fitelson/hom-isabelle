theory Bacon_Book_Full_Classicism_Uniform_Name_Map
  imports Bacon_Book_Full_Classicism_Name_Inverse
begin

lemma book_full_C_consistent_constant_rename_iff:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> 'd"
  assumes rich: "sg_rich G" and injective: "inj f"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_full_C_theory_consistent (\<lambda>\<tau>. f ` \<Sigma> \<tau>) G (book_constant_rename f ` S)"
proof -
  have each: "inj_on f (\<Sigma> \<tau>)" for \<tau> by (rule inj_on_subset[OF injective subset_UNIV])
  have equivalent: "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_full_C_theory_consistent (book_typed_image_signature (\<lambda>_. f) \<Sigma>) G (book_typed_name_map (\<lambda>_. f) ` S)"
    by (rule book_full_C_consistent_typed_image_iff[where \<rho>="\<lambda>_. f" and \<Sigma>=\<Sigma>, OF rich each language])
  have signature_eq: "book_typed_image_signature (\<lambda>_. f) \<Sigma> = (\<lambda>\<tau>. f ` \<Sigma> \<tau>)"
    by (rule ext; simp only: book_typed_image_signature_def)
  have term_map_eq: "(book_typed_name_map (\<lambda>_. f) :: 'c book_named_term \<Rightarrow> 'd book_named_term) = book_constant_rename f"
    by (rule ext; rule book_typed_name_map_uniform)
  show ?thesis using equivalent by (simp only: signature_eq term_map_eq)
qed

text \<open>
  Uniform injective renaming is the special case of the checked
  type-indexed image theorem needed by the Original-name constructor
  at stage zero. It is full-C consistency on both sides, not an appeal
  to the old Equivalence-base extension.
\<close>

end
