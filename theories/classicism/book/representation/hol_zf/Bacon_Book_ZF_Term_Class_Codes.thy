theory Bacon_Book_ZF_Term_Class_Codes
  imports Bacon_Book_ZF_World_Codes
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Term_World_Bridge
begin

definition book_ZF_term_class_domain :: "sgcontext \<Rightarrow> ('c::countable) book_C_world \<Rightarrow> otype \<Rightarrow> ZF" where
  "book_ZF_term_class_domain G w \<sigma> = paper_ZF_image_code (Power HOLZF.Nat)
    book_ZF_countable_set_code (book_C_identity_domain (fst w) G (snd w) \<sigma>)"

theorem book_ZF_term_class_domain_elements:
  "explode (book_ZF_term_class_domain G w \<sigma>) =
    book_ZF_countable_set_code ` book_C_identity_domain (fst w) G (snd w) \<sigma>"
  unfolding book_ZF_term_class_domain_def
  by (rule paper_ZF_image_code_elements[OF book_ZF_countable_sets_bound subset_UNIV])

theorem book_ZF_term_class_domain_bijection:
  "bij_betw book_ZF_countable_set_code (book_C_identity_domain (fst w) G (snd w) \<sigma>)
    (explode (book_ZF_term_class_domain G w \<sigma>))"
  unfolding book_ZF_term_class_domain_def
  by (rule paper_ZF_image_code_bijection[OF book_ZF_countable_set_code_injective book_ZF_countable_sets_bound subset_UNIV])

lemma book_ZF_term_class_domain_bound:
  "book_ZF_term_class_domain G w \<sigma> \<in> explode (Power (Power HOLZF.Nat))"
  unfolding book_ZF_term_class_domain_def by (rule paper_ZF_image_code_type)

theorem book_ZF_term_class_decode_type:
  assumes member: "z \<in> explode (book_ZF_term_class_domain G w \<sigma>)"
  shows "inv book_ZF_countable_set_code z \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
proof -
  have image_member: "z \<in> book_ZF_countable_set_code ` book_C_identity_domain (fst w) G (snd w) \<sigma>"
    using member by (simp only: book_ZF_term_class_domain_elements)
  obtain X where xm: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" and shape: "z = book_ZF_countable_set_code X"
    using image_member by blast
  show ?thesis by (simp only: shape book_ZF_countable_set_inverse; rule xm)
qed

text \<open>
  Every actual identity class is encoded as a set of term codes.
  Every typed class domain is then an actual bounded set of those codes.
  Both levels have explicit Power(Nat) bounds and exact inverse laws;
  neither is replaced by an unstructured atom or a PER function domain.
  These codes realise the already defined term structure, not yet the
  represented semantic domains Dσ or their function graphs.
\<close>

end
