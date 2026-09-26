theory Bacon_Book_ZF_World_Codes
  imports Bacon_Book_ZF_Coded_Frame
begin

context book_full_C_coded_frame
begin

definition book_ZF_world_code :: "'c book_C_world \<Rightarrow> ZF" where
  "book_ZF_world_code w = class_code (snd w)"

lemma book_ZF_world_code_bound:
  "range book_ZF_world_code \<subseteq> explode (Power term_bound)"
  unfolding book_ZF_world_code_def using class_code_bound by blast

theorem full_world_code_injective:
  "inj_on book_ZF_world_code worlds"
proof (rule inj_onI)
  fix w v
  assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and equal: "book_ZF_world_code w = book_ZF_world_code v"
  have codes: "class_code (snd w) = class_code (snd v)" using equal unfolding book_ZF_world_code_def .
  have sentences: "snd w = snd v"
    by (rule inj_onD[OF class_code_injective codes world_sentences_admitted[OF ww] world_sentences_admitted[OF vw]])
  show "w = v" by (rule book_full_C_canonical_world_sentence_injective[OF rich
    book_full_C_rooted_world_data(1)[OF ww] book_full_C_rooted_world_data(1)[OF vw] sentences])
qed

definition full_world_set :: ZF where
  "full_world_set = paper_ZF_image_code (Power term_bound) book_ZF_world_code worlds"

definition full_world_decode :: "ZF \<Rightarrow> 'c book_C_world" where
  "full_world_decode = inv_into worlds book_ZF_world_code"

theorem full_world_set_elements:
  "explode full_world_set = book_ZF_world_code ` worlds"
  unfolding full_world_set_def by (rule paper_ZF_image_code_elements[OF book_ZF_world_code_bound subset_UNIV])

lemma full_world_set_bound:
  "full_world_set \<in> explode (Power (Power term_bound))"
  unfolding full_world_set_def by (rule paper_ZF_image_code_type)

theorem full_world_decode_code:
  "w \<in> worlds \<Longrightarrow> full_world_decode (book_ZF_world_code w) = w"
  unfolding full_world_decode_def by (rule inv_into_f_f[OF full_world_code_injective]; assumption)

theorem full_world_decode_type:
  "z \<in> explode full_world_set \<Longrightarrow> full_world_decode z \<in> worlds"
  unfolding full_world_decode_def full_world_set_elements by (rule inv_into_into; assumption)

theorem full_world_code_decode:
  "z \<in> explode full_world_set \<Longrightarrow> book_ZF_world_code (full_world_decode z) = z"
  unfolding full_world_decode_def full_world_set_elements by (rule f_inv_into_f; assumption)

theorem full_world_code_bijection:
  "bij_betw book_ZF_world_code worlds (explode full_world_set)"
  unfolding bij_betw_def by (rule conjI[OF full_world_code_injective full_world_set_elements[symmetric]])

end

theorem book_countable_world_code:
  fixes \<Sigma> B :: "'c::countable ssignature" and w :: "'c book_C_world"
  assumes frame: "book_full_C_canonical_frame \<Sigma> B G actual"
  shows "book_full_C_coded_frame.book_ZF_world_code book_ZF_countable_code HOLZF.Nat w =
    book_ZF_countable_set_code (snd w)"
proof -
  interpret book_full_C_coded_frame \<Sigma> B G actual book_ZF_countable_code HOLZF.Nat
    by (intro book_full_C_coded_frame.intro book_full_C_coded_frame_axioms.intro frame
      inj_on_subset[OF book_ZF_countable_code_injective subset_UNIV] book_ZF_countable_code_bound)
  show ?thesis by (simp only: book_ZF_world_code_def book_countable_class_code[OF frame])
qed

text \<open>
  A valid world is determined by its closed sentence set, so its code
  is the set of term codes of those sentences. Injectivity is proved
  only on the actual full-C world set, not on all raw pairs of
  signatures and sentence sets. The world collection itself is an
  explicit subset of Power(term_bound), hence an actual HOL-ZF set. Its
  decoder is typed and inverse only on that displayed set. No global
  universe coding assumption or new logical axiom is introduced.
\<close>

end
