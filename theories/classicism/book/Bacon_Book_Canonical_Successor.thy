theory Bacon_Book_Canonical_Successor
  imports Bacon_Book_Canonical_World_Existence
begin

theorem book_C_canonical_successor_exists:
  fixes w :: "('c::countable) book_C_world"
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and pl: "book_theory_formula (fst w) G P" and closed: "named_fv P = {}"
    and missing: "book_box G P \<notin> snd w"
  shows "\<exists>v\<in>book_C_canonical_worlds \<Sigma> B G.
    book_C_canonical_le G w v \<and> book_not G P \<in> snd v \<and> P \<notin> snd v"
proof -
  interpret names: book_countable_ambient_signature "fst w" B
    by (unfold_locales; rule book_C_canonical_world_data(2,3)[OF world])
  let ?\<Omega> = "names.book_ambient_henkin_signature G"
  obtain M where maximal: "book_C_closed_maximal_extension ?\<Omega> G {} M"
    and witnesses: "book_closed_constant_witness_complete ?\<Omega> G M"
    and negative: "book_not G P \<in> M" and absent: "P \<notin> M"
    and kernel: "book_C_unboxed_sentences (fst w) G (snd w) \<subseteq> M"
    using names.book_C_ambient_henkin_successor_exists[
      OF rich book_C_canonical_world_data(4)[OF world] pl closed missing] by blast
  have base: "\<Sigma> \<sigma> \<subseteq> ?\<Omega> \<sigma>" for \<sigma>
    by (rule subset_trans[OF book_C_canonical_world_data(1)[OF world] names.book_ambient_henkin_signature_contains])
  have target: "(?\<Omega>, M) \<in> book_C_canonical_worlds \<Sigma> B G"
    unfolding book_C_canonical_worlds_def
    by (simp only: mem_Collect_eq fst_conv snd_conv; intro conjI allI;
      rule base names.book_ambient_henkin_signature_inside names.book_ambient_henkin_signature_reserve maximal witnesses)
  have accessible: "book_C_canonical_le G w (?\<Omega>, M)"
  proof (unfold book_C_canonical_le_def, intro allI impI)
    fix A
    assume boxed: "book_box G A \<in> snd w"
    have al: "book_theory_formula (fst w) G A" and ac: "named_fv A = {}"
      by (rule book_C_canonical_box_member_data[OF rich world boxed])+
    have am: "A \<in> book_C_unboxed_sentences (fst w) G (snd w)"
      using al ac boxed unfolding book_C_unboxed_sentences_def by blast
    show "A \<in> snd (?\<Omega>, M)" by (simp only: snd_conv; rule subsetD[OF kernel am])
  qed
  show ?thesis using target accessible negative absent by auto
qed

text \<open>
  Proposition 18.3's missing-box successor now belongs to the actual
  world set of Definition 18.8, before restriction to the root's future.
  Its own language, witnesses and infinite reserve are all certified.
  Accessibility uses the literal all-formulas condition. Typing and
  closedness of an unboxed member are recovered from the source world's
  well-formedness, rather than appended to that condition.
\<close>

end
