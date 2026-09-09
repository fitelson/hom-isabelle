theory Bacon_Book_Canonical_Worlds
  imports Bacon_Book_Canonical_Language_Inclusion
begin

section \<open>Definition 18.8: worlds and the literal accessibility condition\<close>

type_synonym 'c book_C_world = "'c ssignature \<times> 'c book_named_term set"

definition book_C_canonical_worlds :: "'c ssignature \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_C_world set" where
  "book_C_canonical_worlds \<Sigma> B G = {w.
    (\<forall>\<sigma>. \<Sigma> \<sigma> \<subseteq> fst w \<sigma> \<and> fst w \<sigma> \<subseteq> B \<sigma> \<and> infinite (B \<sigma> - fst w \<sigma>)) \<and>
    book_C_closed_maximal_extension (fst w) G {} (snd w) \<and>
    book_closed_constant_witness_complete (fst w) G (snd w)}"

definition book_C_canonical_le :: "sgcontext \<Rightarrow> 'c book_C_world \<Rightarrow> 'c book_C_world \<Rightarrow> bool" where
  "book_C_canonical_le G w v \<longleftrightarrow> (\<forall>A. book_box G A \<in> snd w \<longrightarrow> A \<in> snd v)"

lemma book_C_canonical_world_data:
  assumes world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
  shows "\<Sigma> \<sigma> \<subseteq> fst w \<sigma>" and "fst w \<sigma> \<subseteq> B \<sigma>"
    and "infinite (B \<sigma> - fst w \<sigma>)"
    and "book_C_closed_maximal_extension (fst w) G {} (snd w)"
    and "book_closed_constant_witness_complete (fst w) G (snd w)"
  using world unfolding book_C_canonical_worlds_def by blast+

lemma book_box_language_operand:
  assumes rich: "sg_rich G" and boxed: "book_theory_formula \<Sigma> G (book_box G A)"
  shows "book_theory_formula \<Sigma> G A"
proof -
  obtain \<sigma> where head: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_box_const G) (Arr \<sigma> Prop)"
    and argument: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    using boxed unfolding book_box_def by (rule book_language_App_obtain)
  have equal: "Arr \<sigma> Prop = Arr Prop Prop"
    by (rule named_type_unique[OF book_language_type[OF head] book_language_type[OF book_box_const_language[OF rich]]])
  have type_eq: "\<sigma> = Prop" using equal by simp
  show ?thesis using argument by (simp only: type_eq)
qed

lemma book_C_canonical_box_member_data:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and member: "book_box G A \<in> snd w"
  shows "book_theory_formula (fst w) G A" and "named_fv A = {}"
proof -
  have closed_set: "book_closed_formula_set (fst w) G (snd w)"
    by (rule book_C_closed_maximal_data(1)[OF book_C_canonical_world_data(4)[OF world]])
  have data: "book_theory_formula (fst w) G (book_box G A) \<and> named_fv (book_box G A) = {}"
    by (rule book_closed_formula_set_member[OF closed_set member])
  show "book_theory_formula (fst w) G A" by (rule book_box_language_operand[OF rich conjunct1[OF data]])
  show "named_fv A = {}" using conjunct2[OF data] by (simp only: book_box_fv)
qed

theorem book_C_canonical_le_language:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and le: "book_C_canonical_le G w v"
  shows "fst w \<sigma> \<subseteq> fst v \<sigma>"
proof -
  have target: "book_closed_formula_set (fst v) G (snd v)"
    by (rule book_C_closed_maximal_data(1)[OF book_C_canonical_world_data(4)[OF v]])
  have access: "\<And>A. book_box G A \<in> snd w \<Longrightarrow> A \<in> snd v" using le unfolding book_C_canonical_le_def by blast
  show ?thesis by (rule book_C_successor_language_inclusion[OF rich book_C_canonical_world_data(4)[OF w] target access])
qed

theorem book_C_canonical_le_refl:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
  shows "book_C_canonical_le G w w"
proof (unfold book_C_canonical_le_def, intro allI impI)
  fix A
  assume member: "book_box G A \<in> snd w"
  have al: "book_theory_formula (fst w) G A" and ac: "named_fv A = {}"
    by (rule book_C_canonical_box_member_data[OF rich world member])+
  have old_world: "snd w \<in> book_C_closed_worlds (fst w) G"
    by (rule book_C_closed_maximal_is_world[OF book_C_canonical_world_data(4)[OF world]])
  show "A \<in> snd w"
    by (rule book_C_closed_world_apply_theorem[OF rich old_world book_C_modal_T[OF rich al] member ac])
qed

theorem book_C_canonical_le_trans:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and first: "book_C_canonical_le G w v" and second: "book_C_canonical_le G v u"
  shows "book_C_canonical_le G w u"
proof (unfold book_C_canonical_le_def, intro allI impI)
  fix A
  assume member: "book_box G A \<in> snd w"
  have al: "book_theory_formula (fst w) G A" and ac: "named_fv A = {}"
    by (rule book_C_canonical_box_member_data[OF rich world member])+
  have bbc: "named_fv (book_box G (book_box G A)) = {}" by (simp only: book_box_fv ac)
  have old_world: "snd w \<in> book_C_closed_worlds (fst w) G"
    by (rule book_C_closed_maximal_is_world[OF book_C_canonical_world_data(4)[OF world]])
  have iterated: "book_box G (book_box G A) \<in> snd w"
    by (rule book_C_closed_world_apply_theorem[OF rich old_world book_C_modal_4[OF rich al] member bbc])
  have boxed_v: "book_box G A \<in> snd v" using first iterated unfolding book_C_canonical_le_def by blast
  show "A \<in> snd u" using second boxed_v unfolding book_C_canonical_le_def by blast
qed

theorem book_C_canonical_world_sentence_injective:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and same: "snd w = snd v"
  shows "w = v"
proof -
  have forward: "book_C_canonical_le G w v"
    using book_C_canonical_le_refl[OF rich w] same unfolding book_C_canonical_le_def by simp
  have backward: "book_C_canonical_le G v w"
    using book_C_canonical_le_refl[OF rich v] same unfolding book_C_canonical_le_def by simp
  have signatures: "fst w = fst v"
  proof (rule ext)
    fix \<sigma>
    show "fst w \<sigma> = fst v \<sigma>"
      by (rule subset_antisym[OF book_C_canonical_le_language[OF rich w v forward]
        book_C_canonical_le_language[OF rich v w backward]])
  qed
  show ?thesis using signatures same by (cases w; cases v; simp)
qed

text \<open>
  A world is represented by its language and its closed maximal,
  constant-witness-complete sentence set. The base signature and the
  ambient reserve condition are explicit. Accessibility is exactly
  “□A ∈ w implies A ∈ v”, with no language inclusion added to it.
  Language inclusion is a theorem. The sentence set uniquely determines
  the signature, so pairing it with its language does not duplicate the
  source's worlds. T and 4 give reflexivity and
  transitivity. Root restriction and the successor property are next;
  these definitions do not assume a higher-order modal interpretation.
\<close>

end
