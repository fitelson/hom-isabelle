theory Bacon_Book_Full_Ambient_Henkin_Extension
  imports Bacon_Book_Full_Henkin_Image_Extension Bacon_Book_Ambient_Henkin_Extension
begin

context book_countable_ambient_signature
begin

theorem book_full_C_ambient_henkin_extension_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_full_C_closed_maximal_extension (book_ambient_henkin_signature G) G {} M \<and>
    book_full_C_theory_consistent (book_ambient_henkin_signature G) G M \<and>
    (\<forall>A\<in>S. book_universal_closure G A \<in> M) \<and>
    book_closed_constant_witness_complete (book_ambient_henkin_signature G) G M"
proof -
  have injective: "inj_on (book_ambient_name_map \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)" for \<tau>
    by (rule inj_on_subset[OF book_ambient_name_map_injective subset_UNIV])
  show ?thesis unfolding book_ambient_henkin_signature_def
    by (rule book_full_C_henkin_image_extension_exists[OF rich language consistent injective book_ambient_name_map_fixes])
qed

end

text \<open>
  The existing countable signature embedding is purely syntactic and
  is reused unchanged: Σσ ⊆ Ωσ ⊆ Bσ, old declared names are fixed,
  and Bσ − Ωσ remains infinite. The consistency and maximal-extension
  proof is now for the full MF+PE background, not inferred from the
  old base construction. Every closed Ω predicate has a constant witness.
  S may be open/infinite; its universal closures belong to M.
  This is a constructed sentence set, not yet a full-C canonical frame
  or a model with a denotation/truth theorem.
\<close>

end
