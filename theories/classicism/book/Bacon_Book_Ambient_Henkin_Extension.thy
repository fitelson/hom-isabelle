theory Bacon_Book_Ambient_Henkin_Extension
  imports Bacon_Book_Ambient_Name_Embedding Bacon_Book_Ambient_Signature Bacon_Book_Henkin_Image_Extension
begin

section \<open>Henkin completion within one ambient language, with its countable instance\<close>

locale book_countable_ambient_signature =
  fixes \<Sigma> :: "'c::countable ssignature" and B :: "'c ssignature"
  assumes included: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> B \<tau>"
    and reserve: "\<And>\<tau>. infinite (B \<tau> - \<Sigma> \<tau>)"
begin
end

sublocale book_countable_ambient_signature \<subseteq> book_ambient_signature \<Sigma> B
proof (unfold_locales)
  fix \<tau>
  show "\<Sigma> \<tau> \<subseteq> B \<tau>" by (rule included)
  show "infinite (B \<tau> - \<Sigma> \<tau>)" by (rule reserve)
  have countable_names: "card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of (UNIV :: nat set)"
    by (rule card_of_ordLeqI[where f=to_nat]; simp add: inj_on_def)
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of (B \<tau> - \<Sigma> \<tau>)"
    using reserve infinite_iff_card_of_nat by blast
  show "card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of (B \<tau> - \<Sigma> \<tau>)"
    by (rule ordLeq_transitive[OF countable_names naturals])
qed

context book_ambient_signature
begin

theorem book_C_ambient_henkin_extension_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_C_closed_maximal_extension (book_ambient_henkin_signature G) G {} M \<and>
    book_C_theory_consistent (book_ambient_henkin_signature G) G M \<and>
    (\<forall>A\<in>S. book_universal_closure G A \<in> M) \<and>
    book_closed_constant_witness_complete (book_ambient_henkin_signature G) G M"
proof -
  show ?thesis unfolding book_ambient_henkin_signature_def
    by (rule book_C_henkin_image_extension_exists[OF rich language consistent book_ambient_name_map_injective
      book_ambient_name_map_fixes])
qed

end

text \<open>
  Source role: the fixed ambient language Σ∞ and unused-name condition
  in the construction preceding Definition 18.8 (p.399). For each type,
  Σσ ⊆ Ωσ ⊆ Bσ and Bσ − Ωσ remains infinite. The maximal set in Ω
  contains every original universal closure and has witnesses for all
  closed predicates of Ω. Neither witness completeness nor preservation
  of the full enlarged C background is assumed.

  The theorem is now stated for the general ambient locale (reserves
  infinite and at least as large as the declared signature). The
  countable locale is a sublocale, so the external existence results
  proved here are preserved on countable carriers with their earlier
  statements. The internal interface has changed: book_ambient_name_map
  now takes the context G, and its injectivity is proved only on the
  Henkin names actually used, not globally as the earlier countable map's
  was. Interpreting the countable locale does not identify the new map
  with the earlier independently chosen one. The map can be chosen
  independently at different types. It does not yet supply the initial
  transport of a declared signature from an arbitrary carrier, or the
  modal term-model representation.
\<close>

end
