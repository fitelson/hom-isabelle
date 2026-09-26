theory Bacon_Book_ZF_Future_Truth_Sets
  imports Bacon_Book_ZF_Actual_Identity
begin

context book_full_C_coded_frame
begin

lemma full_ZF_future_member_data:
  assumes member: "z \<in> explode (full_ZF_future w)"
  shows "full_world_decode z \<in> worlds" and "le w (full_world_decode z)"
    and "book_ZF_world_code (full_world_decode z) = z"
proof -
  have world: "z \<in> explode full_world_set" and access: "le w (full_world_decode z)"
    using member by (auto simp: full_ZF_future_def Sep explode_Elem)
  show "full_world_decode z \<in> worlds" by (rule full_world_decode_type[OF world])
  show "le w (full_world_decode z)" by (rule access)
  show "book_ZF_world_code (full_world_decode z) = z" by (rule full_world_code_decode[OF world])
qed

theorem full_ZF_future_set_extensional:
  assumes ps: "explode p \<subseteq> explode (full_ZF_future w)"
    and qs: "explode q \<subseteq> explode (full_ZF_future w)"
    and agree: "\<And>v. v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
      Elem (book_ZF_world_code v) p = Elem (book_ZF_world_code v) q"
  shows "p = q"
proof (rule injD[OF inj_explode], rule set_eqI)
  fix z
  show "z \<in> explode p \<longleftrightarrow> z \<in> explode q"
  proof (cases "z \<in> explode p \<or> z \<in> explode q")
    case True
    have future: "z \<in> explode (full_ZF_future w)" using ps qs True by blast
    have vw: "full_world_decode z \<in> worlds" and access: "le w (full_world_decode z)"
      and code: "book_ZF_world_code (full_world_decode z) = z"
      using full_ZF_future_member_data[OF future] by blast+
    show ?thesis using agree[OF vw access] by (simp only: code explode_Elem)
  next
    case False
    then show ?thesis by blast
  qed
qed

definition full_ZF_future_collect where
  "full_ZF_future_collect w P = Sep (full_ZF_future w) (\<lambda>z. P (full_world_decode z))"

lemma full_ZF_future_collect_subset:
  "explode (full_ZF_future_collect w P) \<subseteq> explode (full_ZF_future w)"
  by (auto simp: full_ZF_future_collect_def Sep explode_Elem)

lemma full_ZF_future_collect_member:
  assumes vw: "v \<in> worlds"
  shows "Elem (book_ZF_world_code v) (full_ZF_future_collect w P) \<longleftrightarrow> le w v \<and> P v"
  by (simp only: full_ZF_future_collect_def Sep full_ZF_future_world_member[OF vw] full_world_decode_code[OF vw])

theorem full_ZF_proposition_eq_collect:
  assumes admitted: "full_ZF_admitted w" and member: "p \<in> explode (full_ZF_D Prop w)"
    and agree: "\<And>v. v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
      Elem (book_ZF_world_code v) p = P v"
  shows "p = full_ZF_future_collect w P"
proof (rule full_ZF_future_set_extensional[OF full_ZF_proposition_future[OF admitted member] full_ZF_future_collect_subset])
  fix v
  assume vw: "v \<in> worlds" and access: "le w v"
  show "Elem (book_ZF_world_code v) p = Elem (book_ZF_world_code v) (full_ZF_future_collect w P)"
    by (simp only: full_ZF_future_collect_member[OF vw] access simp_thms; rule agree[OF vw access])
qed

theorem full_ZF_proposition_future_truth:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and member: "p \<in> explode (full_ZF_D Prop w)"
  shows "full_ZF_value_truth v (full_ZF_i Prop w v p) = Elem (book_ZF_world_code v) p"
  by (simp only: full_ZF_value_truth_def full_ZF_i_proposition_restriction[OF ww vw access member]
    full_ZF_proposition_restrict_def Sep full_world_decode_code[OF vw] book_full_C_rooted_refl[OF vw] simp_thms)

end

text \<open>
  Equality of represented propositions is equality of their whole
  future truth sets. The future guard is explicit in the internal
  comprehension. Every member of the coded future decodes to a
  genuine accessible world; no unguarded use of a decoder or of
  off-domain application is admitted by these lemmas.
\<close>

end
