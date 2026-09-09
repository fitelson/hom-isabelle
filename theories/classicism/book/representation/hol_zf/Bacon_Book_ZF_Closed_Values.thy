theory Bacon_Book_ZF_Closed_Values
  imports Bacon_Book_ZF_Future_Truth_Sets
begin

context book_full_C_canonical_frame
begin

definition full_ZF_closed_value where
  "full_ZF_closed_value w \<sigma> A = full_ZF_h \<sigma> w (book_C_identity_class (fst w) G (snd w) \<sigma> A)"

lemma full_ZF_closed_value_type:
  assumes member: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "full_ZF_closed_value w \<sigma> A \<in> explode (full_ZF_D \<sigma> w)"
  unfolding full_ZF_closed_value_def by (rule full_ZF_h_type[OF book_C_identity_domainI[OF member]])

lemma full_ZF_denote_closed_value:
  assumes member: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "full_ZF_denote w g A = full_ZF_closed_value w \<sigma> A"
  unfolding full_ZF_closed_value_def by (rule full_ZF_denote_closed[OF book_closed_terms_language[OF member] book_closed_terms_closed[OF member]])

theorem full_ZF_closed_value_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and member: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "full_ZF_i \<sigma> w v (full_ZF_closed_value w \<sigma> A) = full_ZF_closed_value v \<sigma> A"
  by (simp only: full_ZF_closed_value_def full_ZF_h_natural[OF ww book_C_identity_domainI[OF member], symmetric]
    book_full_C_term_counterpart_class[OF rich book_full_C_rooted_world_data(1)[OF ww]
      book_full_C_rooted_world_data(1)[OF vw] access member])

theorem full_ZF_closed_value_application:
  assumes ww: "w \<in> worlds"
    and fm: "F \<in> book_closed_terms (fst w) G (Arr \<sigma> \<tau>)"
    and am: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "full_ZF_app w \<sigma> \<tau> (full_ZF_closed_value w (Arr \<sigma> \<tau>) F) (full_ZF_closed_value w \<sigma> A) =
    full_ZF_closed_value w \<tau> (NApp F A)"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  show ?thesis by (simp only: full_ZF_closed_value_def
    full_ZF_app_h[OF ww book_C_identity_domainI[OF fm] book_C_identity_domainI[OF am]]
    T.term_app_classes[OF fm am])
qed

theorem full_ZF_logical_value_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
  shows "full_ZF_i (book_minimal_logical_type l) w v (full_ZF_logical_value w l) = full_ZF_logical_value v l"
  using full_ZF_closed_value_natural[OF ww vw access book_C_logical_closed_terms, of l]
  by (simp only: full_ZF_closed_value_def full_ZF_logical_value_def book_C_term_logical_value_def)

end

text \<open>
  The h-image of a closed term is its actual represented denotation,
  with membership in the appropriate Dσ proved from the term's type.
  Closed values commute with counterparts and application. In
  particular, the two primitive logical values are natural families.
  This supplies concrete closed-term images for the remaining modal
  operation and combinator checks, rather than assuming their membership.
\<close>

end
