theory Bacon_Book_ZF_World_Codes
  imports Bacon_Book_ZF_Countable_Codes
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Canonical_Frame
begin

definition book_ZF_world_code :: "('c::countable) book_C_world \<Rightarrow> ZF" where
  "book_ZF_world_code w = book_ZF_countable_set_code (snd w)"

lemma book_ZF_world_code_bound:
  "range (book_ZF_world_code :: ('c::countable) book_C_world \<Rightarrow> ZF) \<subseteq> explode (Power HOLZF.Nat)"
  unfolding book_ZF_world_code_def using book_ZF_countable_set_bound by blast

context book_full_C_canonical_frame
begin

theorem full_world_code_injective:
  "inj_on book_ZF_world_code worlds"
proof (rule inj_onI)
  fix w v
  assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and equal: "book_ZF_world_code w = book_ZF_world_code v"
  have codes: "book_ZF_countable_set_code (snd w) = book_ZF_countable_set_code (snd v)"
    using equal unfolding book_ZF_world_code_def .
  have sentences: "snd w = snd v" by (rule injD[OF book_ZF_countable_set_code_injective codes])
  show "w = v" by (rule book_full_C_canonical_world_sentence_injective[OF rich
    book_full_C_rooted_world_data(1)[OF ww] book_full_C_rooted_world_data(1)[OF vw] sentences])
qed

definition full_world_set :: ZF where
  "full_world_set = paper_ZF_image_code (Power HOLZF.Nat) book_ZF_world_code worlds"

definition full_world_decode :: "ZF \<Rightarrow> 'c book_C_world" where
  "full_world_decode = inv_into worlds book_ZF_world_code"

theorem full_world_set_elements:
  "explode full_world_set = book_ZF_world_code ` worlds"
  unfolding full_world_set_def by (rule paper_ZF_image_code_elements[OF book_ZF_world_code_bound subset_UNIV])

lemma full_world_set_bound:
  "full_world_set \<in> explode (Power (Power HOLZF.Nat))"
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

text \<open>
  A valid world is determined by its closed sentence set, so its code
  is the set of natural-number codes of those sentences. Injectivity
  is proved only on the actual full-C world set, not on all raw pairs
  of signatures and sentence sets. The world collection itself is an
  explicit subset of Power(Nat), hence an actual HOL-ZF set. Its decoder
  is typed and inverse only on that displayed set. No global universe
  coding assumption or new logical axiom is introduced.
\<close>

end
