theory Bacon_Book_Ambient_Henkin_Extension
  imports Bacon_Book_Ambient_Name_Embedding Bacon_Book_Henkin_Image_Extension
begin

section \<open>Henkin completion within one countable ambient language\<close>

locale book_countable_ambient_signature =
  fixes \<Sigma> :: "'c::countable ssignature" and B :: "'c ssignature"
  assumes included: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> B \<tau>"
    and reserve: "\<And>\<tau>. infinite (B \<tau> - \<Sigma> \<tau>)"
begin

definition book_ambient_name_map where
  "book_ambient_name_map \<tau> = book_reserve_name_map (\<Sigma> \<tau>) (B \<tau>)"

definition book_ambient_henkin_signature where
  "book_ambient_henkin_signature G = book_typed_image_signature book_ambient_name_map (book_henkin_full_signature \<Sigma> G)"

lemma book_ambient_name_map_injective:
  "inj (book_ambient_name_map \<tau>)"
proof -
  interpret names: book_countable_name_reserve "\<Sigma> \<tau>" "B \<tau>"
    by (unfold_locales; rule included reserve)
  show ?thesis unfolding book_ambient_name_map_def by (rule names.book_reserve_embedding_injective)
qed

lemma book_ambient_name_map_fixes:
  "c \<in> \<Sigma> \<tau> \<Longrightarrow> book_ambient_name_map \<tau> (BookOriginal c) = c"
  unfolding book_ambient_name_map_def by (rule book_reserve_name_map_original; assumption)

lemma book_ambient_henkin_signature_contains:
  "\<Sigma> \<tau> \<subseteq> book_ambient_henkin_signature G \<tau>"
proof
  fix c
  assume member: "c \<in> \<Sigma> \<tau>"
  have original: "BookOriginal c \<in> book_henkin_full_signature \<Sigma> G \<tau>"
    by (simp only: book_henkin_full_original_iff; rule member)
  have mapped: "book_ambient_name_map \<tau> (BookOriginal c) \<in>
    book_typed_image_signature book_ambient_name_map (book_henkin_full_signature \<Sigma> G) \<tau>"
    by (rule book_typed_image_maps; rule original)
  show "c \<in> book_ambient_henkin_signature G \<tau>"
    using mapped by (simp only: book_ambient_henkin_signature_def book_ambient_name_map_fixes[OF member])
qed

lemma book_ambient_henkin_signature_inside:
  "book_ambient_henkin_signature G \<tau> \<subseteq> B \<tau>"
proof -
  interpret names: book_countable_name_reserve "\<Sigma> \<tau>" "B \<tau>"
    by (unfold_locales; rule included reserve)
  show ?thesis using names.book_reserve_embedding_range
    unfolding book_ambient_henkin_signature_def book_typed_image_signature_def book_ambient_name_map_def by blast
qed

lemma book_ambient_henkin_signature_reserve:
  "infinite (B \<tau> - book_ambient_henkin_signature G \<tau>)"
proof -
  interpret names: book_countable_name_reserve "\<Sigma> \<tau>" "B \<tau>"
    by (unfold_locales; rule included reserve)
  have small: "B \<tau> - range (book_ambient_name_map \<tau>) \<subseteq> B \<tau> - book_ambient_henkin_signature G \<tau>"
    unfolding book_ambient_henkin_signature_def book_typed_image_signature_def by blast
  have infinite_small: "infinite (B \<tau> - range (book_ambient_name_map \<tau>))"
    unfolding book_ambient_name_map_def by (rule names.book_reserve_embedding_leaves_infinite)
  show ?thesis using infinite_small small finite_subset by blast
qed

theorem book_C_ambient_henkin_extension_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_C_closed_maximal_extension (book_ambient_henkin_signature G) G {} M \<and>
    book_C_theory_consistent (book_ambient_henkin_signature G) G M \<and>
    (\<forall>A\<in>S. book_universal_closure G A \<in> M) \<and>
    book_closed_constant_witness_complete (book_ambient_henkin_signature G) G M"
proof -
  have injective: "inj_on (book_ambient_name_map \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)" for \<tau>
    by (rule inj_on_subset[OF book_ambient_name_map_injective subset_UNIV])
  show ?thesis unfolding book_ambient_henkin_signature_def
    by (rule book_C_henkin_image_extension_exists[OF rich language consistent injective book_ambient_name_map_fixes])
qed

end

text \<open>
  Source role: the fixed ambient language Σ∞ and unused-name condition
  in the construction preceding Definition 18.8 (p.399). For each type,
  Σσ ⊆ Ωσ ⊆ Bσ and Bσ − Ωσ remains infinite. The maximal set in Ω
  contains every original universal closure and has witnesses for all
  closed predicates of Ω. Neither witness completeness nor preservation
  of the full enlarged C background is assumed.

  This theorem states countability of the ambient name carrier. The
  map can be chosen independently at different types. It does not yet
  supply the initial transport of a countable declared signature from
  an arbitrary carrier, or the modal term-model representation.
\<close>

end
