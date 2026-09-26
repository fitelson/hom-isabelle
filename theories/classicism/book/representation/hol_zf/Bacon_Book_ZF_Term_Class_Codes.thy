theory Bacon_Book_ZF_Term_Class_Codes
  imports Bacon_Book_ZF_World_Codes
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Term_World_Bridge
begin

context book_full_C_coded_frame
begin

lemma identity_domain_admitted:
  assumes admitted: "full_ZF_admitted w"
  shows "book_C_identity_domain (fst w) H (snd w) \<sigma> \<subseteq> admitted_term_sets"
proof
  fix X
  assume xm: "X \<in> book_C_identity_domain (fst w) H (snd w) \<sigma>"
  obtain C where shape: "X = book_C_identity_class (fst w) H (snd w) \<sigma> C"
    using xm unfolding book_C_identity_domain_def by blast
  show "X \<in> admitted_term_sets"
  proof (rule book_ZF_admitted_term_setsI, rule subsetI)
    fix A
    assume am: "A \<in> X"
    have closed: "A \<in> book_closed_terms (fst w) H \<sigma>"
      using am book_C_identity_class_member unfolding shape by blast
    have language: "book_in_language book_minimal_logical_type UNIV (fst w) H A \<sigma>"
      using closed unfolding book_closed_terms_def by blast
    have inside: "named_in_signature (fst w) A" by (rule book_language_signature[OF language])
    show "A \<in> admitted_terms"
      by (rule book_ZF_admitted_termsI[OF named_in_signature_mono[OF inside full_ZF_admittedD[OF admitted]]])
  qed
qed

definition book_ZF_term_class_domain :: "sgcontext \<Rightarrow> 'c book_C_world \<Rightarrow> otype \<Rightarrow> ZF" where
  "book_ZF_term_class_domain H w \<sigma> = paper_ZF_image_code (Power term_bound)
    class_code (book_C_identity_domain (fst w) H (snd w) \<sigma>)"

theorem book_ZF_term_class_domain_elements:
  "explode (book_ZF_term_class_domain H w \<sigma>) =
    class_code ` book_C_identity_domain (fst w) H (snd w) \<sigma>"
  unfolding book_ZF_term_class_domain_def
  by (rule paper_ZF_image_code_elements[OF class_codes_bound subset_UNIV])

theorem book_ZF_term_class_domain_bijection:
  assumes admitted: "full_ZF_admitted w"
  shows "bij_betw class_code (book_C_identity_domain (fst w) H (snd w) \<sigma>)
    (explode (book_ZF_term_class_domain H w \<sigma>))"
  unfolding book_ZF_term_class_domain_def
  by (rule paper_ZF_image_code_bijection[OF class_code_injective class_codes_admitted_bound
    identity_domain_admitted[OF admitted]])

lemma book_ZF_term_class_domain_bound:
  "book_ZF_term_class_domain H w \<sigma> \<in> explode (Power (Power term_bound))"
  unfolding book_ZF_term_class_domain_def by (rule paper_ZF_image_code_type)

theorem book_ZF_term_class_decode_type:
  assumes admitted: "full_ZF_admitted w"
    and member: "z \<in> explode (book_ZF_term_class_domain H w \<sigma>)"
  shows "class_decode z \<in> book_C_identity_domain (fst w) H (snd w) \<sigma>"
proof -
  have image_member: "z \<in> class_code ` book_C_identity_domain (fst w) H (snd w) \<sigma>"
    using member by (simp only: book_ZF_term_class_domain_elements)
  obtain X where xm: "X \<in> book_C_identity_domain (fst w) H (snd w) \<sigma>" and shape: "z = class_code X"
    using image_member by blast
  have xs: "X \<in> admitted_term_sets" by (rule subsetD[OF identity_domain_admitted[OF admitted] xm])
  show ?thesis by (simp only: shape class_code_inverse[OF xs]; rule xm)
qed

end

text \<open>
  Every actual identity class is encoded as a set of term codes.
  Every typed class domain is then an actual bounded set of those codes.
  Both levels have explicit, unconditional Power(term_bound) bounds and
  element equations. The bijection and decoder laws are guarded: they
  require pointwise containment of fst w in the ambient signature B, for
  an arbitrary context H, because the term code is injective only on
  admitted terms; every actual world qualifies. Neither level is replaced
  by an unstructured atom or a PER function domain. These codes realise the already defined term structure, not
  yet the represented semantic domains Dσ or their function graphs.
\<close>

end
