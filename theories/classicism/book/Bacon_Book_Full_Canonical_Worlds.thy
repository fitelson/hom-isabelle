theory Bacon_Book_Full_Canonical_Worlds
  imports Bacon_Book_Full_Ambient_Henkin_Successor Bacon_Book_Full_Classicism_Modal_Transfer
    Bacon_Book_Canonical_Worlds
begin

section \<open>Canonical worlds with the full MF+PE background\<close>

definition book_full_C_canonical_worlds :: "'c ssignature \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_C_world set" where
  "book_full_C_canonical_worlds \<Sigma> B G = {w.
    (\<forall>\<sigma>. \<Sigma> \<sigma> \<subseteq> fst w \<sigma> \<and> fst w \<sigma> \<subseteq> B \<sigma> \<and> infinite (B \<sigma> - fst w \<sigma>) \<and>
      card_of (\<Union>\<rho>. fst w \<rho>) \<le>o card_of (B \<sigma> - fst w \<sigma>)) \<and>
    book_full_C_closed_maximal_extension (fst w) G {} (snd w) \<and>
    book_closed_constant_witness_complete (fst w) G (snd w)}"

lemma book_full_C_canonical_world_data:
  assumes world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
  shows "\<Sigma> \<sigma> \<subseteq> fst w \<sigma>" and "fst w \<sigma> \<subseteq> B \<sigma>"
    and "infinite (B \<sigma> - fst w \<sigma>)"
    and "book_full_C_closed_maximal_extension (fst w) G {} (snd w)"
    and "book_closed_constant_witness_complete (fst w) G (snd w)"
    and "card_of (\<Union>\<rho>. fst w \<rho>) \<le>o card_of (B \<sigma> - fst w \<sigma>)"
  using world unfolding book_full_C_canonical_worlds_def by blast+

lemmas book_full_C_canonical_world_reserve_large = book_full_C_canonical_world_data(6)

theorem book_full_C_canonical_world_is_base:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
  shows "w \<in> book_C_canonical_worlds \<Sigma> B G"
proof -
  have maximal: "book_C_closed_maximal_extension (fst w) G {} (snd w)"
    by (rule book_full_C_closed_maximal_is_base[OF rich book_full_C_canonical_world_data(4)[OF world]])
  show ?thesis using world maximal unfolding book_full_C_canonical_worlds_def book_C_canonical_worlds_def by blast
qed

lemma book_full_C_canonical_box_member_data:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and member: "book_box G A \<in> snd w"
  shows "book_theory_formula (fst w) G A" and "named_fv A = {}"
  by (rule book_C_canonical_box_member_data[OF rich book_full_C_canonical_world_is_base[OF rich world] member])+

theorem book_full_C_canonical_le_language:
  assumes rich: "sg_rich G" and w: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
  shows "fst w \<sigma> \<subseteq> fst v \<sigma>"
  by (rule book_C_canonical_le_language[OF rich book_full_C_canonical_world_is_base[OF rich w]
    book_full_C_canonical_world_is_base[OF rich v] access])

theorem book_full_C_canonical_le_refl:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
  shows "book_C_canonical_le G w w"
  by (rule book_C_canonical_le_refl[OF rich book_full_C_canonical_world_is_base[OF rich world]])

theorem book_full_C_canonical_le_trans:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and first: "book_C_canonical_le G w v" and second: "book_C_canonical_le G v u"
  shows "book_C_canonical_le G w u"
  by (rule book_C_canonical_le_trans[OF rich book_full_C_canonical_world_is_base[OF rich world] first second])

theorem book_full_C_canonical_world_sentence_injective:
  assumes rich: "sg_rich G" and w: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" and same: "snd w = snd v"
  shows "w = v"
  by (rule book_C_canonical_world_sentence_injective[OF rich book_full_C_canonical_world_is_base[OF rich w]
    book_full_C_canonical_world_is_base[OF rich v] same])

text \<open>
  The world set now requires the full-C background. The raw paired
  world type and the literal relation “□A∈w implies A∈v” are reused.
  Inclusion in the base world set is proved using the verified proof
  embedding; reflexivity, transitivity and language inclusion then follow.
  There is no converse inclusion or equality of future truth sets.
  Actual full-C successor existence is a separate theorem.
\<close>

end
