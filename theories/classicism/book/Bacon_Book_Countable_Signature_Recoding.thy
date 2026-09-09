theory Bacon_Book_Countable_Signature_Recoding
  imports Bacon_Book_Ambient_Henkin_Extension
begin

section \<open>Countably many declared names on an arbitrary carrier\<close>

definition book_countable_signature_map :: "'c ssignature \<Rightarrow> otype \<Rightarrow> 'c \<Rightarrow> nat" where
  "book_countable_signature_map \<Sigma> \<sigma> c = 2 * to_nat_on (\<Sigma> \<sigma>) c"

definition book_countable_signature_image :: "'c ssignature \<Rightarrow> nat ssignature" where
  "book_countable_signature_image \<Sigma> = book_typed_image_signature (book_countable_signature_map \<Sigma>) \<Sigma>"

lemma book_countable_signature_map_injective:
  assumes small: "countable (\<Sigma> \<sigma>)"
  shows "inj_on (book_countable_signature_map \<Sigma> \<sigma>) (\<Sigma> \<sigma>)"
  using small unfolding inj_on_def book_countable_signature_map_def by (auto simp: to_nat_on_inj)

lemma book_countable_signature_odd_unused:
  "2*n+1 \<notin> book_countable_signature_image \<Sigma> \<sigma>"
  unfolding book_countable_signature_image_def book_typed_image_signature_def book_countable_signature_map_def
  by (auto; presburger)

lemma book_countable_signature_image_reserve:
  "infinite (UNIV - book_countable_signature_image \<Sigma> \<sigma>)"
proof -
  have injective: "inj (\<lambda>n::nat. 2*n+1)" by (rule injI; simp)
  have infinite_odds: "infinite (range (\<lambda>n::nat. 2*n+1))"
    using finite_imageD[OF _ injective] infinite_UNIV_nat by blast
  have subset: "range (\<lambda>n::nat. 2*n+1) \<subseteq> UNIV - book_countable_signature_image \<Sigma> \<sigma>"
    using book_countable_signature_odd_unused by blast
  show ?thesis using infinite_odds subset finite_subset by blast
qed

theorem book_C_countable_signature_consistency_iff:
  assumes rich: "sg_rich G" and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
  shows "book_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_C_theory_consistent (book_countable_signature_image \<Sigma>) G
      (book_typed_name_map (book_countable_signature_map \<Sigma>) ` S)"
proof -
  have injective: "inj_on (book_countable_signature_map \<Sigma> \<sigma>) (\<Sigma> \<sigma>)" for \<sigma>
    by (rule book_countable_signature_map_injective[where \<Sigma>=\<Sigma>]; rule small)
  show ?thesis unfolding book_countable_signature_image_def
    by (rule book_C_consistent_typed_image_iff[where \<rho>="book_countable_signature_map \<Sigma>" and \<Sigma>=\<Sigma>,
      OF rich injective language])
qed

theorem book_countable_signature_has_ambient:
  "book_countable_ambient_signature (book_countable_signature_image \<Sigma>) (\<lambda>_. UNIV)"
  by (unfold_locales; rule subset_UNIV book_countable_signature_image_reserve)

text \<open>
  The original constant-name type is unrestricted. Only each declared
  component Σσ is countable. At each type we send the declared names
  injectively to even natural numbers; odd numbers remain available.
  Consistency is preserved and reflected in the exact image language.
  This supplies the initial ambient-language hypothesis for the book's
  displayed countable-signature construction (p.398), not a semantic
  model or the arbitrary-cardinality extension of completeness.
\<close>

end
