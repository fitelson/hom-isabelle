theory Bacon_Book_Canonical_Frame
  imports Bacon_Book_Canonical_Successor
begin

section \<open>The root's future and Proposition 18.3\<close>

definition book_C_rooted_worlds where
  "book_C_rooted_worlds \<Sigma> B G actual =
    {w \<in> book_C_canonical_worlds \<Sigma> B G. book_C_canonical_le G actual w}"

locale book_C_canonical_frame =
  fixes \<Sigma> :: "('c::countable) ssignature" and B :: "'c ssignature"
    and G :: sgcontext and actual :: "'c book_C_world"
  assumes rich: "sg_rich G"
    and root_world: "actual \<in> book_C_canonical_worlds \<Sigma> B G"
begin

abbreviation worlds where "worlds \<equiv> book_C_rooted_worlds \<Sigma> B G actual"
abbreviation le where "le \<equiv> book_C_canonical_le G"

lemma book_C_rooted_world_data:
  "w \<in> worlds \<Longrightarrow> w \<in> book_C_canonical_worlds \<Sigma> B G"
  "w \<in> worlds \<Longrightarrow> le actual w"
  unfolding book_C_rooted_worlds_def by blast+

theorem book_C_root_is_world:
  "actual \<in> worlds"
  using root_world book_C_canonical_le_refl[OF rich root_world] unfolding book_C_rooted_worlds_def by blast

theorem book_C_rooted_refl:
  "w \<in> worlds \<Longrightarrow> le w w"
  by (rule book_C_canonical_le_refl[OF rich book_C_rooted_world_data(1)]; assumption)

theorem book_C_rooted_trans:
  "w \<in> worlds \<Longrightarrow> le w v \<Longrightarrow> le v u \<Longrightarrow> le w u"
  by (rule book_C_canonical_le_trans[OF rich book_C_rooted_world_data(1)]; assumption)

theorem book_C_rooted_future_closed:
  assumes source: "w \<in> worlds" and target: "v \<in> book_C_canonical_worlds \<Sigma> B G"
    and access: "le w v"
  shows "v \<in> worlds"
proof -
  have from_root: "le actual v"
    by (rule book_C_canonical_le_trans[OF rich root_world book_C_rooted_world_data(2)[OF source] access])
  show ?thesis using target from_root unfolding book_C_rooted_worlds_def by blast
qed

theorem book_C_rooted_successor_exists:
  assumes world: "w \<in> worlds" and pl: "book_theory_formula (fst w) G P"
    and closed: "named_fv P = {}" and missing: "book_box G P \<notin> snd w"
  shows "\<exists>v\<in>worlds. le w v \<and> book_not G P \<in> snd v \<and> P \<notin> snd v"
proof -
  obtain v where vw: "v \<in> book_C_canonical_worlds \<Sigma> B G" and access: "le w v"
    and negative: "book_not G P \<in> snd v" and absent: "P \<notin> snd v"
    using book_C_canonical_successor_exists[OF rich book_C_rooted_world_data(1)[OF world] pl closed missing] by blast
  have inside: "v \<in> worlds" by (rule book_C_rooted_future_closed[OF world vw access])
  show ?thesis using inside access negative absent by blast
qed

theorem book_proposition_18_3:
  assumes world: "w \<in> worlds" and pl: "book_theory_formula (fst w) G P" and closed: "named_fv P = {}"
  shows "book_box G P \<in> snd w \<longleftrightarrow> (\<forall>v\<in>worlds. le w v \<longrightarrow> P \<in> snd v)"
proof
  assume necessary: "book_box G P \<in> snd w"
  show "\<forall>v\<in>worlds. le w v \<longrightarrow> P \<in> snd v"
    using necessary unfolding book_C_canonical_le_def by blast
next
  assume every: "\<forall>v\<in>worlds. le w v \<longrightarrow> P \<in> snd v"
  show "book_box G P \<in> snd w"
  proof (rule ccontr)
    assume missing: "book_box G P \<notin> snd w"
    obtain v where vw: "v \<in> worlds" and access: "le w v" and absent: "P \<notin> snd v"
      using book_C_rooted_successor_exists[OF world pl closed missing] by blast
    show False using every vw access absent by blast
  qed
qed

end

context book_countable_ambient_signature
begin

theorem book_C_canonical_frame_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "\<exists>actual. book_C_canonical_frame \<Sigma> B G actual \<and>
    (\<forall>A\<in>S. book_universal_closure G A \<in> snd actual)"
proof -
  obtain actual where aw: "actual \<in> book_C_canonical_worlds \<Sigma> B G"
    and contains: "\<forall>A\<in>S. book_universal_closure G A \<in> snd actual"
    using book_C_canonical_world_exists[OF rich language consistent] by blast
  have frame: "book_C_canonical_frame \<Sigma> B G actual" by (unfold_locales; rule rich aw)
  show ?thesis by (rule exI[where x=actual], rule conjI[OF frame contains])
qed

end

text \<open>
  Definition 18.8 is now assembled over the fixed countable ambient
  carrier. The root exists for each well-formed C-consistent premise
  set; open premises enter by universal closure. Reflexivity, transitivity
  and the root condition are proved, with no antisymmetry requirement.

  Proposition 18.3 uses actual witness-complete successors within the
  root's future. It does not presuppose the term model or its truth lemma.
  The countable-carrier restriction and rich variable stock remain
  explicit. Definition 18.9 and Propositions 18.4–18.6 still require the
  identity-class domains and their all-type semantic representation.
\<close>

end
