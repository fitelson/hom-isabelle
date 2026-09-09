theory Bacon_Book_Full_Countable_Signature_Recoding
  imports Bacon_Book_Full_Classicism_Name_Inverse Bacon_Book_Countable_Signature_Recoding
begin

theorem book_full_C_countable_signature_consistency_iff:
  assumes rich: "sg_rich G" and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_full_C_theory_consistent (book_countable_signature_image \<Sigma>) G
      (book_typed_name_map (book_countable_signature_map \<Sigma>) ` S)"
proof -
  have injective: "inj_on (book_countable_signature_map \<Sigma> \<sigma>) (\<Sigma> \<sigma>)" for \<sigma>
    by (rule book_countable_signature_map_injective[where \<Sigma>=\<Sigma>]; rule small)
  show ?thesis unfolding book_countable_signature_image_def
    by (rule book_full_C_consistent_typed_image_iff[where \<rho>="book_countable_signature_map \<Sigma>" and \<Sigma>=\<Sigma>,
      OF rich injective language])
qed


text \<open>The existing pure countable name map now transports full-C consistency. The original name carrier remains unrestricted; only its declared components are countable.\<close>

end
