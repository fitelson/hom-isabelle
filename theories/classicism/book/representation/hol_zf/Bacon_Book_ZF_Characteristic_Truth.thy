theory Bacon_Book_ZF_Characteristic_Truth
  imports Bacon_Book_ZF_Future_Abstraction
    Bacon_Book_Modal_Representation.Bacon_Book_Term_General_Model
begin

section \<open>Truth is membership of the current world in a proposition\<close>

context book_full_C_coded_frame
begin

definition full_ZF_value_truth where
  "full_ZF_value_truth w p = Elem (book_ZF_world_code w) p"

lemma full_world_subset_code_member:
  assumes ww: "w \<in> worlds" and subset: "P \<subseteq> worlds"
  shows "Elem (book_ZF_world_code w) (paper_ZF_image_code full_world_set book_ZF_world_code P) \<longleftrightarrow> w \<in> P"
proof -
  have image: "book_ZF_world_code w \<in> book_ZF_world_code ` P \<longleftrightarrow> w \<in> P"
    using ww subset full_world_code_injective unfolding inj_on_def by blast
  show ?thesis by (simp only: explode_Elem[symmetric] full_world_subset_code_elements[OF subset]; rule image)
qed

theorem full_ZF_h_proposition_truth:
  assumes ww: "w \<in> worlds"
  shows "full_ZF_value_truth w (full_ZF_h Prop w X) = book_C_term_valuation (snd w) X"
proof -
  have subset: "book_full_C_proposition_profile \<Sigma> B G actual w (book_C_identity_rep X) \<subseteq> worlds"
    unfolding book_full_C_proposition_profile_def by blast
  show ?thesis by (simp only: full_ZF_value_truth_def full_ZF_h.simps
    book_full_C_proposition_h_def full_world_subset_code_member[OF ww subset]
    proposition_profile_at_world[OF ww] book_C_term_valuation_def)
qed

theorem full_ZF_denote_truth_correspondence:
  assumes ww: "w \<in> worlds"
    and language: "book_theory_formula (fst w) G A"
  shows "full_ZF_value_truth w (full_ZF_denote w g A) =
    book_C_term_valuation (snd w)
      (book_C_term_denote (fst w) G (snd w) (full_ZF_assignment_decode w g) A)"
  by (simp only: full_ZF_denote_eq[OF book_language_type[OF language]] full_ZF_h_proposition_truth[OF ww])

theorem full_ZF_closed_sentence_truth:
  assumes ww: "w \<in> worlds" and am: "A \<in> book_closed_terms (fst w) G Prop"
  shows "full_ZF_value_truth w (full_ZF_denote w g A) \<longleftrightarrow> A \<in> snd w"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  show ?thesis by (simp only: full_ZF_denote_closed[OF book_closed_terms_language[OF am] book_closed_terms_closed[OF am]]
    full_ZF_h_proposition_truth[OF ww] T.term_valuation_class[OF am])
qed

theorem full_ZF_substituted_sentence_truth:
  assumes ww: "w \<in> worlds" and language: "book_theory_formula (fst w) G A"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_value_truth w (full_ZF_denote w g A) \<longleftrightarrow>
    book_environment_subst {} (book_C_term_representatives (full_ZF_assignment_decode w g)) A \<in> snd w"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  have closed_instance: "book_environment_subst {} (book_C_term_representatives (full_ZF_assignment_decode w g)) A \<in>
    book_closed_terms (fst w) G Prop"
    by (rule T.book_C_term_substituted_closed_terms[OF language full_ZF_assignment_decode_typed[OF worlds_admitted[OF ww] typed]])
  show ?thesis by (simp only: full_ZF_denote_truth_correspondence[OF ww language]
    book_C_term_denote_eq[OF book_language_type[OF language]] T.term_valuation_class[OF closed_instance])
qed

end

text \<open>
  The truth test is the literal membership of w's code in the
  represented proposition. Its agreement with characteristic truth
  is proved from the actual hᵗ profile definition and world-code
  injectivity. Closed sentences are true exactly when they belong
  to w; open sentences use their closed representative instance.
  These calculations concern the constructed interpretation, not
  an assumed modal model or a completed completeness theorem.
\<close>

end
